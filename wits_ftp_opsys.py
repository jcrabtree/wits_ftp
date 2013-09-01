'''
   wits_ftp - automatic monitoring of New Zealand electricity prices
    Copyright (C) 2013 David Hume, Electricty Authority, New Zealand.

    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <http://www.gnu.org/licenses/>.


This is the wits_ftp class.  It is used to connect, login, download, convert and save the WITS 5 minute price data.   
This is part of the spot price alert system implemented by the New Zealand Electricty Authority.

This originated from a simple "matlab like" script (spot_price_ftp_v0.4.py) but is now more functionized using a class and 
various function definitions in Python. 

Overall, there are two independent parts to the spot price alert system.  Both run as separate processes, 
but linked through a shared file, live5.h5

Process 1. This part, an FTP client, connects, determines what file to download, downloads the file (to memory), 
processes the file and saves this file containing:
 1. the 5 minute prices for the previous 5 minutes live5[live5], and,
 2. a rolling half-hourly 
Process 2. A price_stats_alert.py script that calculates various statistics on the five minute data and, if alert 
conditions are met, alerts people through the MyMailer class. 

This script makes heavy use of the Wes McKinney's amazing Pandas module (thanks Wes!) 

Used with the following crontab

*/5 * * * * /usr/bin/python /home/dave/python/wits_ftp/wits_ftp_opsys.py 
    --ftp_pass='password' --ftp_user='user' >> /home/dave/python/wits_ftp/wits_ftp_cron.log 2>&1

Now tracking this project directory with GIT (10/8/2012) 
       
**KNOWN ISSUES**
**Between December 5 and December 19, 2012, this script stopped outputing prices, reason was lack of a published 
infeasibility file -- fixed December 19, 2012**
**NOTE: In development, on some systems (i.e., within a restricted coporate environment like the EA) an HTTP tunnel is 
required due to combination of proxy issues/settings and the python FTPlib module.
**proxy host required for the ftp instance, via an HTTP tunnel, i.e., socket mapping...At the EA the ECOM proxy servers 
appear to disallow FTP transfer.  

David Hume, 23/01/2013.

'''
import smtplib
from email.mime.text import MIMEText
import ftplib
import setuphttpproxy as sup
import datetime as dt
import StringIO
import pickle
import re, sys, os
import gzip
import signal
from pandas import *
import time
import logging
import logging.handlers
import argparse
import warnings
warnings.filterwarnings('ignore',category=pandas.io.pytables.PerformanceWarning)

#############################################################################################################################################################################        
#Setup command line option and argument parsing
#############################################################################################################################################################################        
parser = argparse.ArgumentParser(add_help=False)
parser.add_argument('--ftp_host', action="store",dest='ftp_host',default='ftpakl.electricitywits.co.nz')
parser.add_argument('--ftp_user', action="store",dest='ftp_user',default='ecom')
parser.add_argument('--ftp_pass', action="store",dest='ftp_pass')

parser.add_argument('--wits_path', action="store",dest='wits_path',default='/home/dave/python/wits_ftp/')
parser.add_argument('--proxy_host', action="store",dest='proxy_host',default='172.29.52.79') #use eaintranet as of ~5/2013. Use 127.0.0.1 when using cntlm on workstation...
parser.add_argument('--proxy_port', action="store",dest='proxy_port',default='8081') #use earnie as of ~5/2013. Use 3128 when using cntlm on workstation...
cmd_line = parser.parse_args()

#############################################################################################################################################################################        
#Setup tunnel
#############################################################################################################################################################################        

tunnel = sup.setup_http_proxy(cmd_line.proxy_host,cmd_line.proxy_port)

#############################################################################################################################################################################        
#Setup logging
#############################################################################################################################################################################        

formatter = logging.Formatter('|%(asctime)-6s|%(message)s|','%Y-%m-%d %H:%M')
consoleLogger = logging.StreamHandler()
consoleLogger.setLevel(logging.INFO)
consoleLogger.setFormatter(formatter)
logging.getLogger('').addHandler(consoleLogger)
fileLogger = logging.handlers.RotatingFileHandler(filename=cmd_line.wits_path + 'wits_ftp.log',maxBytes = 1024*1024, backupCount = 9)
fileLogger.setLevel(logging.ERROR)
fileLogger.setFormatter(formatter)
logging.getLogger('').addHandler(fileLogger)
logger = logging.getLogger('WITS FTP')
logger.setLevel(logging.INFO)

#############################################################################################################################################################################        
#Exception class pass...
#############################################################################################################################################################################        

class ConnectionError(Exception): pass 
class LoginError(Exception): pass
class FTPcdError(Exception): pass
class FTPfilelistError(Exception): pass
class FTPfilefoundError(Exception): pass
class GZIPfileError(Exception): pass
class WITSFileNameGuessError(Exception): pass
class FTPRetrBinaryError(Exception): pass

class wits_ftp():
   
    def __init__(self,ftp_host,ftp_user,ftp_pass,wits_path):
        #Define Path
        self.ftp_host = ftp_host
        self.ftp_user = ftp_user
        self.ftp_pass = ftp_pass
        self.wits_path = wits_path
        self.msg_text = None
        self.sub_text = None
        self.ftp_timeout=20
        self.file_match = {'i':[],'p':[],'s':[]}
        self.nowM10 = {}
        self.dto = None 
        self.f = {'i': None, 'p':None, 's':None} #String buffer from the FTP process for, infeasible GXPs and all GXP dispatch prices. 
        self.colnames = {'i': ['gxp','date','TP','type','price','file_write','dispatch?'],\
                         'p': ['date','TP','time','price','island','region','price_type','file_write'],\
                         's': ['Ramp Up Cons','Ramp Down Cons','Branch Cons','Branch Group Cons','GIP/GXP Group Cons', \
                               'Market Node Group Cons','GIP/GXP Deficit','GXP Integrity','NI Fast Reserve MW','NI Fast Reserve Price',\
                               'NI Sustained Reserve MW','NI Sustained Reserve Price','SI Fast Reserve MW','SI Fast Reserve Price',\
                               'SI Sustained Reserve MW','SI Sustained Reserve Price','Datetime','NI Fast Reserve Deficit','NI Sustained Reserve Deficit',\
                               'SI Fast Reserve Deficit','SI Sustained Reserve Deficit']} #define some column names for the ftp'ed data
        self.min5min = None
        self.ftp = None
        self.region_dayDF = None
        self.island_dayDF = None
        self.region_hourDF = None
        self.island_hourDF = None
        self.region_TPDF = None
        self.island_TPDF = None
        self.l5 = None  #live 5 minute raw GXP series 
        self.i5 = None  #live 5 minute island mean price series
        self.r5 = None  #live 5 minute region mean price series
        self.s5 = None  #summary data
        self.last_l5_data = None
        self.last_i5_data = None
        self.last_r5_data = None
        self.l5w = DataFrame() #live 5 minute raw GXP series DataFrame for one week 
        self.i5w = DataFrame() #live 5 minute island mean price DataFrame for one week 
        self.r5w = DataFrame() #live 5 minute region mean price DataFrame for one week 
        self.s5w = DataFrame() #summary 5 minute dataframe
        self.statsw = DataFrame() #live 5 minute region mean price DataFrame for one week 
        self.mult_idx = None
        self.lmt = 400000  #Max and minimum price filter (in cents)
        self.dto = None #Date time object
        self.TP = None  #Trading Period
        self.region = None
        self.island = None
        self.connect_time = None
        self.total_ftp_time = None
        self.total_time = None
        self.ftp_filelist= {}
        self.end_digs = {'i':['00','01','02','03','04','05'],'p':['30','31','32','33','34','35'],'s':['30','31','32','33','34','35']} 
        self.end_ext = {'i':'.csv.gz','p':'.csv.gz','s':'.csv'}
        self.ftp_dirs = {'i':'/public/','p':'/5minprices/','s':'/5minprices/'}
        self.washup = []
        self.washedup = False
        self.date_format = "%Y-%m-%d %H:%M"
        self.last_live5 = 0
        self.testi=0
        self.m5 = None
        self.hh = None
        self.hr = None
        self.dy = None
        self.m5x = None
        self.hhx = None
        self.hrx = None
        self.dyx = None
        self.nisland_txt = None
        self.sisland_txt = None
        self.nregion_txt = None
        self.sregion_txt = None        
        self.live5exists = False
        self.ftp_error = False
        self.stats = None
        self.timelag = 15

    #############################################################################################################################################################################        
    def ftp_filenames(self):       #Determine the first parts of the most recent five minute filenames which are then matched
    #############################################################################################################################################################################        
        now = dt.datetime.now()                                #The current time
        back_a_bit = dt.timedelta(minutes=(now.minute % 5)+self.timelag) #Determine the remainder minutes after division of 5 and add 10 minutes
        self.nowM10['p'] = now - back_a_bit                          #Subtract this time from the current time
        self.nowM10['i'] = now - back_a_bit - dt.timedelta(minutes=1)         #and take a minute of this for the list of infeasible gxps (GXPs not connected to the grid?)
        #self.nowM10['s'] = now - back_a_bit - dt.timedelta(minutes=1)   #ditto for summary file
        self.file_match['p']='5minprices_' + str(self.nowM10['p'].isoformat()[0:16]).replace('-','').replace('T','').replace(':','') #filename match text string
        self.file_match['s']='5minprices_' + 'summary_' + str(self.nowM10['p'].isoformat()[0:16]).replace('-','').replace('T','').replace(':','') #filename match text string
        self.file_match['i']='inf_rtd' + str(self.nowM10['i'].isoformat()[0:16]).replace('-','').replace('T','').replace(':','')     #filename match text string
        min5s = dt.timedelta(minutes=5)
        min5min = self.nowM10['p']-min5s
        self.min5min = min5min.strftime(self.date_format) 
        
    #############################################################################################################################################################################        
    def ftp_connect(self):
    #############################################################################################################################################################################        
        try:
            self.connect_time = time.time()
            self.ftp = ftplib.FTP(self.ftp_host, timeout=self.ftp_timeout)
            connect_time2 = time.time()
            self.ftp_error = False
        except (sup.socket.error, sup.socket.gaierror), e:
            error_txt = 'ERROR: Unable to reach %s' % self.ftp_host
            logger.error(error_txt.center(125,'*'))
            ConnectionError(error_txt.center(125,'*'))
            self.ftp_error = True
        try:        #Login
            self.ftp.login(self.ftp_user,self.ftp_pass)
            log_time = time.time()
        except ftplib.error_perm:
            error_txt = 'ERROR: Unable to login'
            logger.error(error_txt.center(125,'*'))
            LoginError(error_txt.center(125,'*'))
            self.ftp_error = True
            
    #############################################################################################################################################################################               
    def ftp_get(self,pis):  
    #############################################################################################################################################################################        
        five_min_data = StringIO.StringIO()
        filename_start = self.ftp_dirs[pis] + self.file_match[pis]
        end_ext = self.end_ext[pis]
        for end_digit in self.end_digs[pis]:
            filename = filename_start + end_digit + end_ext
            try: 
                self.ftp.retrbinary('RETR ' + filename, five_min_data.write) 
                break
            except ftplib.error_perm, resp:   #often the name in incorrect, as we are guessing the last two digits in end_digs, this exception passes this exception
                if resp[0][0:3] == '550':
                    error_text = 'Name not %s' % filename
                    WITSFileNameGuessError(error_text.center(msg_len,'*'))
                    self.ftp_error = True
            except:  #We may, from time-to-time, get other errors, this is trying to pass these errors
                #If the FTP is broken we need to flag this and make sure that we don't call ftp_quit
                error_text = 'An error occurred in retrieving file %s' % (filename)
                logger.error(error_text.center(msg_len,'*'))       #definately log this error
                FTPRetrBinaryError(error_text.center(msg_len,'*')) #and pass to this exception class (above)
                self.ftp_error = True
        five_min_data.seek(0, os.SEEK_END)
        if pis == 'p' or pis == 'i':
            if five_min_data.tell() > 0: #if we have some data
                got_file_end = time.time()     
                five_min_data.seek(0) #rewind stream to start!
                f = gzip.GzipFile(mode='rb', fileobj=five_min_data)
                try:
                    self.f[pis] = f.read()
                except: #otherwise, log error
                    if pis == 'i':
                        error_text = (self.min5min + '|Unable to unzip %s!'.center(89,'*')) % filename
                    if pis == 'p':
                        self.price_info = self.min5min + '|GXPXXXX:    $XXX.XX|GXPXXXX:    $XXX.XX|Ave:    $XXX.XX|'    
                        error_text = 'Unable to unzip %s! --> skipping' % filename
                        if self.file_match[pis] not in self.washup:
                            self.washup.append(self.file_match[pis]) #add to the file match list for next time, if not all ready in the queue
                    GZIPfileError(error_text.center(msg_len,'*')) 
                    logger.error(error_text.center(msg_len,'*'))
                finally:
                    f.close()
            else:  #otherwise, if we didn't get any data...
                if pis == 'i':   #Hack here to allow continue if we don't get a inf_rtd file (19 December 2012) 
                    error_text = '|File %s not found, probably because it does not exist! --> skipping' % filename
                if pis == 'p':
                    self.price_info = self.min5min + '|GXP????:    $???.??|GXP????:    $???.??|Ave:    $???.??|'    
                    error_text = '|File %s not found, or empty! --> skipping' % filename              
                    if self.file_match[pis] not in self.washup:
                        self.washup.append(self.file_match[pis]) #if not already in the list, add to the file match list for next time
                    FTPfilefoundError(u"\u2718" + '|' + ftp_data.min5min + '|' + error_text.center(msg_len,'*'))
                    logger.error(u"\u2718" + '|' + ftp_data.min5min + '|' + error_text.center(msg_len,'*'))                                                

        if pis == 's': #unzipped summary file
            five_min_data.seek(0)
            self.f[pis] = five_min_data.read() 
            
    #############################################################################################################################################################################        
    def ftp_quit(self):       #Quit FTP server
    #############################################################################################################################################################################        
        if self.ftp_error == False:  #i.e., if there was an issue, don't quit as likely we lost the FTP pipe|link
            q = self.ftp.quit()

    #############################################################################################################################################################################            
    def ftp_pandas(self):   #combine 5 minute prices into one pandas dataframe object - this needs work, multi-index and groupby shoiuld be impliemnted here...
    #############################################################################################################################################################################                    
        self.inf = None
        self.l5 = None
        self.i5 = None
        self.r5 = None
        self.stats = None

        if self.f['i']: #if any infeasible gxps exist 
            if isnull(self.f['i']) == False:
                buf = StringIO.StringIO(self.f['i'])    #ok, this is a string buffer straight from the ftp
                self.inf = read_csv(buf, names = self.colnames['i'], index_col = 0)   #read in the new live 5 data 
        
        if self.f['p']: #if prices exist
            if isnull(self.f['p']) == False:
                buf = StringIO.StringIO(self.f['p'])   #ok, this is a string buffer straight from the ftp
                self.l5 = read_csv(buf, names = self.colnames['p'])   #read in the new live 5 data 
                #Now obtain the dto from the data        
                self.dto = datetime(int(self.l5.date[0].split('/')[2]),int(self.l5.date[0].split('/')[1]),int(self.l5.date[0].split('/')[0]),int(self.l5.time[0].split(':')[0]),int(self.l5.time[0].split(':')[1])) #yes, the date/time object of this file, read from the first row.
                self.TP = self.l5.TP[0]  #get the current trading period
                self.l5 = self.l5.drop(['date', 'TP' , 'time' , 'price_type' , 'file_write'], axis=1) #we have the datetime, delete all the extra crap that wastes space.
                self.l5 = self.l5.ix[((self.l5<self.lmt)*(self.l5>-self.lmt)).price,:] #removes any row over or under the self.lmt (Note: could be smarter here are then add those removes to the inf.index obj and record - perhaps somehting for the future
                self.r5 = self.l5.groupby('region').mean().price #r5 is the regional mean price series
                self.r5 = self.r5.T             #transpose, and, 
                self.r5.name = self.dto         #rename region series with the datetimeobject (dto)
                self.i5 = self.l5.groupby('island').mean().price #i5 is the island mean price series
                self.i5 = self.i5.T             #transpose, and, 
                self.i5.name = self.dto         #rename island series with the datetimeobject (dto)
                self.l5 = self.l5.pop('price')  #remove the extra island and region columns and pop only the price to a series, as this is all we require.
                self.l5 = self.l5.T             #transpose, and, 
                self.l5.name = self.dto         #rename
                #Now we need to store the live5 data in a dataframe, based on the above dto name tags.
                #Too complicate things, we need a multi-index with trading periods on the column indexing (and possible hours in the future).  For now we attempt a multiindex with the dto and TP from above.
                #To start with we only have the above series and want to add this to either the existing dataframe, or, if we are starting afresh with a new live5.h5 file, we will need to create the dataframe from the start...we'll attempt this first
                #Ok, currently from release 0.7.3 of Pandas, manual page 88...
                self.mult_idx = MultiIndex.from_tuples([(self.dto,self.TP)], names=['dto', 'TP'])  #first we have to create a multi-index 
                #Do a stats series
                self.stats = Series([self.l5.idxmax(), self.l5.max(),self.l5.mean(),self.l5.idxmin(),self.l5.min(),self.l5.std(),self.l5.skew(),self.l5.kurt()], index=['Max GXP','Max $/MWh','Mean','Min GXP','Min $/MWh','Std','Skew','Kurt'])
                self.last_l5_data = self.l5
                self.last_r5_data = self.r5
                self.last_i5_data = self.i5
                self.last_stats_data = self.stats

        if self.f['s']: #if summary data exists
            if isnull(self.f['p']) == False:
                buf = StringIO.StringIO(self.f['s'])   #ok, this is a string buffer straight from the ftp
                self.s5 = read_csv(buf, names = self.colnames['s'])   #read in the new live 5 data 
                self.s5 = self.s5.reset_index().T.pop(0)  #reset index and convert to series 
                self.s5 = self.s5.drop(['level_0', 'level_1' , 'level_2' , 'Datetime']) #remove extra buff
                self.s5.name = self.dto  #and stamp with the dto   
    
    #############################################################################################################################################################################                            
    def update_df(self,cropped_pickle_file,current_series,current_index,crop_days,crop_hours):          #Update function for cropped dataframes
    #############################################################################################################################################################################                            
 
        if os.path.isfile(cropped_pickle_file):                  #if the file exists
            cropped_df = read_pickle(cropped_pickle_file) #read the file
            if list(current_index)[0] not in list(cropped_df.columns): #make sure current index not already in dataframe (when in 1 minute testing mode)		
                cropped_df = cropped_df.join(DataFrame(current_series, columns=current_index))  #join current 5 minute series to cropped dataframe
                cropped_df = self.crop_data(cropped_df,crop_days,crop_hours) #keep dataframe cropped by crop_days + crop_hours
                cropped_df.to_pickle(cropped_pickle_file)    #save the cropped file
            return cropped_df
        else:
            cropped_df = DataFrame(current_series, columns=current_index)   #create new DataFrame if on first iteration 
            cropped_df.to_pickle(cropped_pickle_file)                       #and save
            return cropped_df  
      
    #############################################################################################################################################################################            
    def update_prices(self):    #Ok, report current prices, this seems way too long, and quite yuck really - sure this can be imporved in the future
    #############################################################################################################################################################################                    
        
        m5_mean = (self.l5w.mean()[-1])        #Mean price over all GXPs for the peroid, do some stats, mean, max, std, skew and kurtosis and add to dataframe object
        m5_max = {self.l5w.idxmax()[-1]:(self.l5w.max()[-1])}
        m5_min = {self.l5w.idxmin()[-1]:(self.l5w.min()[-1])}
        m5_std = (self.l5w.std()[-1])
        m5_skew = (self.l5w.skew()[-1])        
        m5_kurt = (self.l5w.kurt()[-1])
        dgs = 10           #Do regional/island info
        self.nregion_txt = self.i5w[self.i5w.columns[-1]].to_string(float_format = lambda x: '$%.2f' % x).replace(' ','').replace('\n','|') + '|' + self.r5w[self.r5w.columns[-1]].to_string(float_format = lambda x: '$%.2f' % x).replace(' ','').replace('\n','|')
        #Format up a string for aleat purposes that gives max info. limit 160 characters...
        str_tup_m5 = (str('$%.2f' % m5_max.values()[0]).rjust(dgs,' '),m5_max.keys()[0],str('$%.2f' % m5_mean).center(dgs,' '),m5_min.keys()[0],str('$%.2f' % m5_min.values()[0]).ljust(dgs,' '),u"\u03C3" + '=' + str('%.1f' % m5_std).rjust(6,' '),'S=' + str('%.2f' % m5_skew).rjust(6,' '),'K=' + str('%.2f' % m5_kurt).rjust(6,' '))
        self.m5 = '%s@%s<%s>%s@%s|%s|%s|%s| ' % str_tup_m5 + self.nregion_txt
        
    #############################################################################################################################################################################                            
    def ftp_data_process(self):        #grab both files, combine, put into pandas series object
    #############################################################################################################################################################################                            

        self.ftp_filenames()             #get the first part of the filenames to match
        self.ftp_connect()               #connect to ftp server
        if self.ftp_error == False:     #i.e., if we got data then process it
           self.ftp_get('p')             #try and get price
           self.ftp_get('i')             #get infesability files
           self.ftp_get('s')             #get the summary file download
        self.ftp_quit()
        self.ftp_pandas()                #Ok, so we have the data, now process to pandas object
        self.l5w = self.update_df(self.wits_path + 'l5w.pickle',self.l5,self.mult_idx,7,0)         #update pickled files
        self.r5w = self.update_df(self.wits_path + 'r5w.pickle',self.r5,self.mult_idx,7,0)
        self.i5w = self.update_df(self.wits_path + 'i5w.pickle',self.i5,self.mult_idx,7,0)
        self.s5w = self.update_df(self.wits_path + 's5w.pickle',self.s5,self.mult_idx,7,0)
        self.statsw = self.update_df(self.wits_path + 'statsw.pickle',self.stats,self.mult_idx,7,0)
        self.update_prices()
        self.spit_to_csv()  #as the name suggests... we could add this to update_df --todo

    #############################################################################################################################################################################                            
    def spit_to_csv(self):    #Crop data and save 
    #############################################################################################################################################################################                    
        
        i5w_hr = self.i5w
        r5w_hr = self.r5w
        l5w_hr = self.l5w
        s5w_hr = self.s5w

        statsw_hr = self.statsw
        #Dump to csv in an attemp to use javascript d3 to read and display (in a nice format) the csv data
        i5w_d3 = ((i5w_hr.T)/100.0).reset_index(level=1).asfreq('5Min') #get rid of multi-index (Trading Periods), resample at 5min intervals, and fill NANs with zeros.
        r5w_d3 = ((r5w_hr.T)/100.0).reset_index(level=1).asfreq('5Min') 
        l5w_d3 = ((l5w_hr.T)/100.0).reset_index(level=1).asfreq('5Min') 
        s5w_d3 = ((s5w_hr.T)/100.0).reset_index(level=1).asfreq('5Min') 
        
        s5w_d3 = s5w_d3.rename(columns=dict(zip(s5w_d3.columns,s5w_d3.columns.map(lambda x: x.replace(' ','_')))))      
        s5w_d3 = s5w_d3.rename(columns=dict(zip(["NI_Fast_Reserve_Price","NI_Sustained_Reserve_Price","SI_Fast_Reserve_Price","SI_Sustained_Reserve_Price"],["NIFIR","NISIR","SIFIR","SISIR"])))
       
        i5w_d3.to_csv(self.wits_path + 'island_week.csv',float_format='%.4f') 
        r5w_d3.to_csv(self.wits_path + 'region_week.csv',float_format='%.4f')
        l5w_d3.to_csv(self.wits_path + 'all_week.csv',float_format='%.4f')
        s5w_d3.to_csv(self.wits_path + 'reserve_week.csv',float_format='%.4f')

        statsw_hr.T.to_csv(self.wits_path + 'stats_week.csv',float_format='%.4f') 
        #Dump just the current prices
        current_prices = DataFrame({'price':self.l5})
        current_prices = current_prices.reset_index().rename(columns={'index':'id'}).set_index('id').dropna()
        current_prices = current_prices[current_prices['price']>0]
        current_prices.to_csv(self.wits_path + 'price.csv',float_format='%.2f') 
        #Lets also groupby Trading periods and dump that to csv for the text alert system in mymailer.py
        all_week = read_csv(self.wits_path + 'all_week.csv',index_col=[0,1],parse_dates=True)*100#.reset_index().set_index([[0,1]])*100.0
        #print all_week.index
        all_week['Date']=all_week.index.map(lambda x: x[0].date())
        all_week_bytp = all_week.fillna(0).groupby(level=[0,1]).mean()
        all_week_bytp.to_csv(self.wits_path + 'all_week_bytp.csv')
        island_week = read_csv(self.wits_path + 'island_week.csv',index_col=[0,1],parse_dates=True)*100 #.reset_index().set_index([[0,1]])*100.0
        island_week['Date']=island_week.index.map(lambda x: x[0].date())
        island_week_bytp = island_week.fillna(0).groupby(level=[0,1]).mean()
        island_week_bytp.to_csv(self.wits_path + 'island_week_bytp.csv')
        region_week = read_csv(self.wits_path + 'region_week.csv',index_col=[0,1],parse_dates=True)*100 #.reset_index().set_index([[0,1]])*100.0
        region_week['Date']=region_week.index.map(lambda x: x[0].date())
        region_week_bytp = region_week.fillna(0).groupby(level=[0,1]).mean()
        region_week_bytp.to_csv(self.wits_path + 'region_week_bytp.csv')


    #############################################################################################################################################################################                            
    def crop_data(self,data,days,hours):        #First we check the working directory for an existing live5.h5 
    #############################################################################################################################################################################                            

        dataT = data.T #Transpose data
        lastest_data = data.columns[-1] #the lastest dispatch time stamp in the h5 file
        lastest_date = lastest_data[0].date() #latest date
        cropped_data  = dataT[dataT.index.levels[0]>=(lastest_data[0]-(dt.timedelta(days = days,hours=hours)))]        
        return cropped_data.T 
        
    #############################################################################################################################################################################                            
    def report_prices(self):
    #############################################################################################################################################################################                            
        
        self.msg_text = self.l5w.T[-1:].T.idxmax()[0] + '=$' + str(self.l5w.T[-1:].T.max()[0]) + '/MWh' #,@' + str(self.l5w.T.index[-1][0])[:-3]
        self.sub_text = 'Price alert @ ' + str(self.l5w.columns[-1][0])

#############################################################################################################################################################################                            
#Start the programme
#############################################################################################################################################################################                            
msg_len = 194

if __name__ == '__main__':
    time1 = dt.datetime.now() 
    ftp_data = wits_ftp(cmd_line.ftp_host,cmd_line.ftp_user,cmd_line.ftp_pass,cmd_line.wits_path)  #create class instance
    ftp_data.ftp_data_process() #FTP the wits server and get the lastest 5 minute data
    time2 = dt.datetime.now()
    ftp_data.report_prices() 
    ftp_processing_time = time2 - time1
    ftp_processing_time_2 = (ftp_processing_time.seconds + (ftp_processing_time.microseconds/1000000.0))
    #Log progress to wits_ftp_op_sys_cron.log.  Can be viewed (realtime) in terminal with: tail -f wits_ftp_op_sys_cron.log
    if ftp_data.f['p']: #if prices exist
       if isnull(ftp_data.f['p']) == False:
          logger_text = u"\u2713" + '|' + ftp_data.min5min + '|' + str(ftp_data.TP) + '|%ss|' % (str('%3.1f' % ftp_processing_time_2).rjust(5)) + ftp_data.m5
          logger.info(logger_text.center(msg_len))

