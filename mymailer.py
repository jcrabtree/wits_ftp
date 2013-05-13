'''
This is the MyMailer class.  
It is used to send SMS text messages as part of the spot price alert system implemented by the Electricty Authority.
This was my first serious attempt at using and implementing classes in Python so be warned...

There are essentially two parts to the spot price alert system.
1. A FTP python script which saves a file containing the 5 minute prices for the previous 5 minutes to live5.h5, and,
2. A price_stats_alert.py script that calculates various statistics on the five minute data and, if alert condictions are met, alerts people through the MyMailer class. 

This script, as current 10/04/2013, has been edited to now use the mean of all 5 minute periods from the file all_week_bytp.csv

22,52 * * * * /usr/bin/python /home/dave/python/wits_ftp/mymailer.py --GXP_trigger=1000 --Island_trigger=500 >> /home/dave/python/wits_ftp/mymailer_cron.log 2>&1

NOTE: This script must be run on a computer that has authentication to send email.  
    
David Hume, 13/05/2013

TODO:

This script needs work.  We want to be able to make this publicly available on github.
To do this we need to have an address book input file, rather than hard coded.
We also need command line inputs for the server,sender and sms domain.
It would be nice to have a testing mode: adds TESTING to msg header, reduces trigger level to $0/MWh

Weelky price text/email could be useful...
 
'''

import smtplib
from pandas import *
from email.mime.text import MIMEText
import logging
import logging.handlers
import datetime as dt
from datetime import timedelta,time
import time
import sys,os
import argparse

#############################################################################################################################################################################        
#Setup command line option and argument parsing
#############################################################################################################################################################################        

parser = argparse.ArgumentParser(add_help=False)
parser.add_argument('--host', action="store",dest='host',default='172.29.52.11') #This is the smtp server...'eaexch01.ecom.local'   
parser.add_argument('--sender', action="store",dest='sender',default='david.hume@ea.govt.nz')
parser.add_argument('--path', action="store",dest='path',default='/home/dave/python/wits_ftp/')
parser.add_argument('--GXP_trigger', action="store",dest='GXP_trigger',default = 1000)
parser.add_argument('--Island_trigger', action="store",dest='Island_trigger',default = 500)
parser.add_argument('--phonebook', action="store",dest='phonebook',default = 'phonebook.csv')
cmd_line = parser.parse_args()

#############################################################################################################################################################################        
#Setup logging
#############################################################################################################################################################################        

formatter = logging.Formatter('|%(asctime)-6s|%(levelname)s|%(message)s|','%Y-%m-%d %H:%M')
consoleLogger = logging.StreamHandler()
consoleLogger.setLevel(logging.INFO)
consoleLogger.setFormatter(formatter)
logging.getLogger('').addHandler(consoleLogger)

fileLogger = logging.handlers.RotatingFileHandler(filename='wits_mail.log',maxBytes = 1024*1024, backupCount = 9)
fileLogger.setLevel(logging.ERROR)
fileLogger.setFormatter(formatter)
logging.getLogger('').addHandler(fileLogger)

logger = logging.getLogger('WITS MAIL')
logger.setLevel(logging.INFO)

#############################################################################################################################################################################        
#Exception class pass...
#############################################################################################################################################################################        


class ConnectionError(Exception): pass
class SendError(Exception): pass
class OpenHDFFileError(Exception): pass


class MyMailer():
    """This class is used to test spot market prices and react to high prices by sending an email to a text alert system"""    
    def __init__(self,host,sender,path,GXP_trigger,Island_trigger,phonebook):
        self.host = host
        self.sender = sender
        self.path = path
        self.GXP_trigger = float(GXP_trigger)
        self.Island_trigger = float(Island_trigger)
        self.phonebook = phonebook
        self.receivers =[]
        self.l5w = None
        self.msg_text = None
        self.sub_text = None
        self.live5 = None
        self.TPDF = None
        self.hourDF = None
        self.dayDF = None
        self.msg = None
        self.i = 0
        self.most_recent_alert = datetime(1999,1,1,1,1)
 
    def get_receivers(self):
        pb=open(self.path + self.phonebook)
        for l in pb:
            if l[0] != '#':
                self.receivers.append(l.split(',')[1].replace('\n',''))
        
    def connect(self):
        try:
            self.server = smtplib.SMTP(self.host)
            
        except smtplib.socket.gaierror:
            error_text = "Error connecting to %s" % (self.host)
            logger.error(error_text)
            ConnectionError(error_text)
            
    def send_text(self):
        self.get_receivers()
        try:
            self.server.set_debuglevel(False) 
            self.server.sendmail(self.sender,self.receivers, self.msg.as_string())
        except smtplib.SMTPException, errormsg:
            error_text = "Couldn't send message: %s" % (errormsg)
            logger.error(error_text)
            SendError(error_text)
            
        except smtplib.socket.timeout:
            error_text = "Socket error while sending message"
            logger.error(error_text)
            ConnectionError(error_text)
            
    def send_alert_text(self):
        self.connect()
        self.msg = MIMEText(self.price_stats + ' '*140)         #Format msg string and add subject
        self.msg['Subject'] = '*Real-time price alert*'
        self.send_text()
        self.quit()
        
    def send_error_text(self):
        msg_text = 'Spot price alert has fallen over - needs restart...!'         #Format msg string and add subject
        sub_text = 'Spot price alert process has stopped!'
        msg = MIMEText(msg_text)
        msg['Subject'] = sub_text
        self.send_text(receivers,msg)
       
    def get_prices(self):
        try:
            all_week_bytp=read_csv(self.path + 'all_week_bytp.csv',index_col=0,parse_dates=True).reset_index().set_index(['Date','TP'])
            region_week_bytp=read_csv(self.path + 'region_week_bytp.csv',index_col=0,parse_dates=True).reset_index().set_index(['Date','TP'])
            island_week_bytp=read_csv(self.path + 'island_week_bytp.csv',index_col=0,parse_dates=True).reset_index().set_index(['Date','TP'])
            self.l5w = all_week_bytp.ix[-2:-1,:].T
            self.i5w = island_week_bytp.ix[-2:-1,:].T
            self.r5w = region_week_bytp.ix[-2:-1,:].T
        except:
            error_text = "Could not load live5.h5"
            logger.error(error_text)
            OpenHDFFileError(error_text)


    #############################################################################################################################################################################            
    def report_prices(self):    #Ok, report current prices, this seems way too long, and quite yuck really - sure this can be imporved in the future
    #############################################################################################################################################################################                    

        self.m5_mean = self.l5w.mean().values[0]        #Mean price over all GXPs for the peroid
        self.m5_max = {self.l5w.idxmax().values[0]:(self.l5w.max().values[0])}
        self.m5_min = {self.l5w.idxmin().values[0]:(self.l5w.min().values[0])}
        self.m5_std = (self.l5w.std().values[0])
        self.m5_skew = (self.l5w.skew().values[0])        
        self.m5_kurt = (self.l5w.kurt().values[0])
        #Do regional/island info
        dgs = 10
        self.sisland_txt = 'SI=$%.2f' % (self.i5w.T.SI.values[0])
        self.nisland_txt = 'NI=$%.2f' % (self.i5w.T.NI.values[0])
        self.price_stats = '%s=$%.2f, NI/SI=$%.2f/$%.2f, TP %i (ending %s)' % (self.l5w.idxmax(axis=0).values[0],\
                                                      self.l5w.max(axis=0).values[0],\
                                                      self.i5w.T.NI.values[0],\
                                                      self.i5w.T.SI.values[0],\
                                                      self.l5w.idxmax(axis=0).index[0][1],\
                                                      (datetime(2013,1,1)+timedelta(seconds=60*30*self.l5w.idxmax(axis=0).index[0][1])).time().isoformat()[:-3]   )              
        logger.info(self.price_stats)
    def quit(self):
        self.server.quit()

if __name__ == '__main__':
    send_mail = MyMailer(cmd_line.host,cmd_line.sender,cmd_line.path,cmd_line.GXP_trigger,cmd_line.Island_trigger,cmd_line.phonebook)      #get an instance of MyMailer
    send_mail.get_prices()      #get five minute data
    send_mail.report_prices()   #process the data

    if (send_mail.l5w.max() >= send_mail.GXP_trigger) or (send_mail.i5w.T.NI.values[0] >= send_mail.Island_trigger) or (send_mail.i5w.T.SI.values[0] >= send_mail.Island_trigger):
        if (send_mail.l5w.max() >= send_mail.GXP_trigger):
			logger.info('GXP price greater than $' + str(send_mail.GXP_trigger) + ', sending text')
        if (send_mail.i5w.T.NI.values[0] >= send_mail.Island_trigger) or (send_mail.i5w.T.SI.values[0] >= send_mail.Island_trigger):
			logger.info('Island price greater than $' + str(send_mail.Island_trigger) + ', sending text')
        send_mail.send_alert_text()
 
