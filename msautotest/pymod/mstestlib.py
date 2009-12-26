###############################################################################
# $Id$
#
# Project:  MapServer
# Purpose:  Test harnass for MapServer autotest.
# Author:   Frank Warmerdam, warmerdam@pobox.com
#
###############################################################################
#  Copyright (c) 2002, Frank Warmerdam <warmerdam@pobox.com>
# 
#  Permission is hereby granted, free of charge, to any person obtaining a
#  copy of this software and associated documentation files (the "Software"),
#  to deal in the Software without restriction, including without limitation
#  the rights to use, copy, modify, merge, publish, distribute, sublicense,
#  and/or sell copies of the Software, and to permit persons to whom the
#  Software is furnished to do so, subject to the following conditions:
# 
#  The above copyright notice and this permission notice shall be included
#  in all copies or substantial portions of the Software.
# 
#  THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS
#  OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
#  FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL
#  THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
#  LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
#  FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
#  DEALINGS IN THE SOFTWARE.
###############################################################################

import sys
import os
import string
from testlib import *

have_pdiff = None

###############################################################################
# get_mapfile_list()

def get_mapfile_list( argv ):

    map_files = []

    # use mapfile(s) passed in arg list if any.
    for arg in argv:
        if arg[-4:] == '.map':
            map_files.append( arg )

    if len(map_files) > 0:
        return map_files
    
    # scan the current directory for mapfiles. 
    files = os.listdir('.')

    for file in files:
        if file[-4:] == '.map':
            map_files.append( file )

    return map_files

###############################################################################
# has_requires()

def has_requires( version_info, requires_list ):

    for item in requires_list:
        if string.find( version_info, item ) == -1:
            return 0
        
    return 1

###############################################################################
# read_test_directives()

def read_test_directives( mapfile_name ):

    runparms_list = []
    require_list = []
    
    lines = open(mapfile_name).readlines()
    for line in lines:
        req_off = string.find( line, 'REQUIRES:' )
        if req_off != -1:
            items = string.split( line[req_off+9:] )
            for item in items:
                require_list.append( item )
                
        run_off = string.find( line, 'RUN_PARMS:' )
        if run_off != -1:
            items = string.split( line[run_off+10:], None, 1 )
            if len(items) == 2:
                runparms_list.append( (items[0], items[1]) )
            elif len(items) == 1:
                runparms_list.append( (items[0],
                                       '[SHP2IMG] -m [MAPFILE] -o [RESULT]') )
                                     
    if len(runparms_list) == 0:
        runparms_list.append( (mapfile_name[:-4] + '.png',
                               '[SHP2IMG] -m [MAPFILE] -o [RESULT]') )

    return (runparms_list, require_list)
            

###############################################################################
# Strip Content-type and other http headers off this file.

def demime_file( filename ):

    data = open(filename,'rb').read()

    for i in range(len(data)-1):
        if data[i] == '\n' and data[i+1] == '\n':
            open(filename,'wb').write(data[i+2:])
            return
    return

###############################################################################
# Strip MapServer version comment from file.

def deversion_file( filename ):

    data = open(filename,'rb').read()

    start = string.find( data, '<!-- MapServer version' )
    if start == -1:
        start = string.find( data, '<!--MapServer version' )
    if start == -1:
        return

    end = start+10
    length = len(data)
    while end < length - 5 and data[end:end+3] != '-->':
        end = end+1

    if data[end:end+3] != '-->':
        return

    new_data = data[:start-1] + data[end+4:]
    open(filename,'wb').write(new_data)
    return

###############################################################################
# Do windows exponential conversion on the file (e+0nn to e+nn).

def fixexponent_file( filename ):

    data = open(filename,'rb').read()
    orig_data = data

    start = string.find( data, 'e+0' )
    while start != -1:
        if data[start+3] in string.digits and data[start+4] in string.digits \
            and data[start+5] == '"':
            data = data[:start+2] + data[start+3:]
        start = string.find( data, 'e+0', start+3 )

    if data != orig_data:
        open(filename,'wb').write(data)

    return

###############################################################################
# Do windows number of decimal truncation.

def truncate_one_decimal( filename ):
    import re
    
    data = open(filename,'rb').read()

    numbers_found = re.compile('[0-9]+\.[0-9]{6,24}', re.M)

    start = 0
    new_data = ''
    for number in numbers_found.finditer(data):
        end = number.end() - 1
        new_data = new_data + data[start:end] 
        start = number.end()

    if new_data != '':
        new_data = new_data + data[start:] 


    if new_data != '' and new_data != data:
        open(filename,'wb').write(new_data)

    return
###############################################################################
# Replace CR+LF by CR

def crlf( filename ):
    
    try:
        file_stat = os.stat( filename )
    except OSError:
        return
    data = open(filename, "rb").read()

    #This is a binary file
    if '\0' in data:
        return
      
    newdata = data.replace("\r\n", "\n")
    if newdata != data:
        f = open(filename, "wb")
        f.write(newdata)
        f.close() 
###############################################################################
# run_tests()

def run_tests( argv ):

    skip_count = 0
    fail_count = 0
    succeed_count = 0
    init_count = 0
    keep_pass = 0
    valgrind = 0 
    shp2img = 'shp2img' 

    ###########################################################################
    # Process arguments.
    
    for i in range(len(argv)):
        if argv[i] == '-shp2img':
            shp2img = argv[i+1]
        if argv[i] == '-keep':
            keep_pass = 1
        if argv[i] == '-valgrind':
            valgrind = 1

    ###########################################################################
    # Create results directory if it does not already exist.
    if not os.path.exists("result"):
         os.mkdir("result")

    ###########################################################################
    # Get version info.
    version_info = os.popen( shp2img + ' -v' ).read()
    print 'version = %s' % version_info
    
    ###########################################################################
    # Check directory wide requirements.
    try:
        (runparms_list, requires_list) = read_test_directives( 'all_require.txt' )
        if not has_requires( version_info, requires_list ):
            print 'Some or all of the following requirements for this directory of tests\nare not available:'
            print requires_list
            return
    except:
        pass
    
    ###########################################################################
    # Process all mapfiles.
    map_files = get_mapfile_list( argv )

    for map in map_files:

        print ' Processing: %s' % map
        (runparms_list, requires_list) = read_test_directives( map )

        if not has_requires( version_info, requires_list ):
            print '    missing some or all of required components, skip.'
            skip_count += len(runparms_list)
            continue
        
        #######################################################################
        # Handle each RUN_PARMS item in this file.
        for run_item in runparms_list:
            out_file = run_item[0]
            command = run_item[1]

            if len(runparms_list) > 1:
                print '   test %s' % out_file

            if string.find(command,'[RESULT_DEMIME]') != -1:
                demime = 1
            else:
                demime = 0
                
            if string.find(command,'[RESULT_DEVERSION]') != -1:
                deversion = 1
            else:
                deversion = 0
                
            command = string.replace( command, '[RESULT]', 'result/'+out_file )
            command = string.replace( command, '[RESULT_DEMIME]', 'result/'+out_file )
            command = string.replace( command, '[RESULT_DEVERSION]', 'result/'+out_file )
            command = string.replace( command, '[MAPFILE]', map )
            command = string.replace( command, '[SHP2IMG]', shp2img )
            command = string.replace( command, '[MAPSERV]', 'mapserv' )
            command = string.replace( command, '[LEGEND]', 'legend' )
            command = string.replace( command, '[SCALEBAR]', 'scalebar' )
            
            if valgrind:
                command = command.strip()
                command = 'valgrind --tool=memcheck --leak-check=full %s 2>result/%s.txt'%(command, out_file+".vgrind.txt")
            os.system( command )
            if demime:
                demime_file( 'result/'+out_file )
            if deversion:
                deversion_file( 'result/'+out_file )
                fixexponent_file( 'result/'+out_file )
                truncate_one_decimal( 'result/'+out_file )
                
            crlf('result/'+out_file)
            cmp = compare_result( out_file )
            
            if cmp == 'match':
                succeed_count = succeed_count + 1
                if keep_pass == 0:
                    os.remove( 'result/' + out_file )
                print '     results match.'
            elif cmp ==  'files_differ_image_match':
                succeed_count = succeed_count + 1
                if keep_pass == 0:
                    os.remove( 'result/' + out_file )
                print '     result images match, though files differ.'
            elif cmp ==  'files_differ_image_nearly_match':
                succeed_count = succeed_count + 1
                if keep_pass == 0:
                    os.remove( 'result/' + out_file )
                print '     result images perceptually match, though files differ.'
            elif cmp ==  'nomatch':
                fail_count = fail_count + 1
                print '*    results dont match, TEST FAILED.'
            elif cmp == 'noresult':
                fail_count = fail_count + 1
                print '*    no result file generated, TEST FAILED.'
            elif cmp == 'noexpected':
                print '     no expected file exists, accepting result as expected.'
                init_count = init_count + 1
                os.rename( 'result/' + out_file, 'expected/' + out_file )

    try:
        print 'Test done (%.2f%% success):' % (float(succeed_count)/float(succeed_count+fail_count)*100)
    except:
        pass

    print '%d tested skipped' % skip_count
    print '%d tests succeeded' % succeed_count
    print '%d tests failed' %fail_count
    print '%d test results initialized' % init_count
