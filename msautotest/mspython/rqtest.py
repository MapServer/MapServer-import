#!/usr/bin/env python
###############################################################################
# $Id$
#
# Project:  MapServer
# Purpose:  Test suite for MapServer Raster Query capability.
# Author:   Frank Warmerdam, warmerdam@pobox.com
#
###############################################################################
#  Copyright (c) 2004, Frank Warmerdam <warmerdam@pobox.com>
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
# 
# $Log$
# Revision 1.3  2004/05/27 17:34:46  frank
# Updated to work with new or old APIs and names.
#
# Revision 1.2  2004/05/13 03:03:28  frank
# added header
#

import sys

sys.path.append( '../pymod' )
import pmstestlib

import mapscript

###############################################################################
# Dump query result set ... used when debugging this test script.

def dumpResultSet( layer ):
    layer.open()
    for i in range(1000):
        result = layer.getResult( i )
        if result is None:
            break
        
        print '(%d,%d)' % (result.shapeindex, result.tileindex)
        
        s = layer.getShape( result.shapeindex, result.tileindex )
        for i in range(layer.numitems):
            print '%s: %s' % (layer.getItem(i), s.getValue(i))
            
    layer.close()

def ngGetShape(layer, shapeindex, tileindex = 0):
    shape = mapscript.shapeObj(layer.type)
    layer.getShape( shape, tileindex, shapeindex )
    return shape
    
###############################################################################
# Open map and get working layer.

def rqtest_1():
    
    try:
        x = mapscript.Map
        mapscript.Layer.ngGetShape = mapscript.Layer.getShape
        
    except:
        mapscript.Map = mapscript.mapObj
        mapscript.Line = mapscript.lineObj
        mapscript.Point = mapscript.pointObj
        mapscript.Line.addPoint = mapscript.Line.add
        mapscript.Shape = mapscript.shapeObj
        mapscript.Shape.addLine = mapscript.Shape.add
        mapscript.layerObj.ngGetShape = ngGetShape
        mapscript.Rect = mapscript.rectObj
        
    pmstestlib.map = mapscript.Map('../gdal/tileindex.map')
    pmstestlib.layer = pmstestlib.map.getLayer(0)

    return 'success'

###############################################################################
# Execute region query.

def rqtest_2():

    line = mapscript.Line()
    line.addPoint( mapscript.Point( 35, 25 ) )
    line.addPoint( mapscript.Point( 45, 25 ) )
    line.addPoint( mapscript.Point( 45, 35 ) )
    line.addPoint( mapscript.Point( 35, 25 ) )

    poly = mapscript.Shape( mapscript.MS_SHAPE_POLYGON )
    poly.addLine( line )

    pmstestlib.layer.queryByShape( pmstestlib.map, poly )

    return 'success'

###############################################################################
# Scan results, checking count and the first shape information.

def rqtest_3():
    layer = pmstestlib.layer
    
    #########################################################################
    # Check result count.
    layer.open()
    count = 0
    for i in range(1000):
        result = layer.getResult( i )
        if result is None:
            break
    
        count = count + 1

    if count != 55:
        pmstestlib.post_reason( 'got %d results instead of expected %d.' \
                             % (count, 55) )
        return 'fail'

    #########################################################################
    # Check first shape attributes.
    
    result = layer.getResult( 0 )
    s = layer.ngGetShape( result.shapeindex, result.tileindex )
    
    if pmstestlib.check_items( layer, s,
                               [('value_0','115'),
                                ('red','115'),
                                ('green','115'),
                                ('blue','115'),
                                ('values','115'),
                                ('x','39.5'),
                                ('y','29.5')] ) == 0:
        return 'fail'

    #########################################################################
    # Check first shape geometry.
    if s.type != mapscript.MS_SHAPE_POINT:
        pmstestlib.post_reason( 'raster query result is not a point.' )
        return 'fail'

    if s.numlines != 1:
        pmstestlib.post_reason( 'raster query has other than 1 lines.' )
        return 'fail'

    try:
        l = s.getLine( 0 )
    except:
        l = s.get( 0 )
    if l.numpoints != 1:
        pmstestlib.post_reason( 'raster query has other than 1 points.' )
        return 'fail'

    try:
        p = l.getPoint(0)
    except:
        p = l.get(0)
    if p.x != 39.5 or p.y != 29.5:
        pmstestlib.post_reason( 'got wrong point location.' )
        return 'fail'
    
    #########################################################################
    # Check last shape attributes.

    result = layer.getResult( 54 )
    s = layer.ngGetShape( result.shapeindex, result.tileindex )

    if pmstestlib.check_items( layer, s,
                               [('value_0','132'),
                                ('x','44.5'),
                                ('y','25.5')] ) == 0:
        return 'fail'
    
    layer.close() 
    layer.close() # discard resultset.

    return 'success'
    
###############################################################################
# Execute multiple point query, and check result.

def rqtest_4():

    pnt = mapscript.Point()
    pnt.x = 35.5
    pnt.y = 25.5
    
    pmstestlib.layer.queryByPoint( pmstestlib.map, pnt, mapscript.MS_MULTIPLE,
                                   1.25 )

    return 'success'

###############################################################################
# Scan results, checking count and the first shape information.

def rqtest_5():
    layer = pmstestlib.layer
    
    #########################################################################
    # Check result count.
    layer.open()
    count = 0
    for i in range(1000):
        result = layer.getResult( i )
        if result is None:
            break
    
        count = count + 1

    if count != 9:
        pmstestlib.post_reason( 'got %d results instead of expected %d.' \
                             % (count, 9) )
        return 'fail'

    #########################################################################
    # Check first shape attributes.
    
    result = layer.getResult( 0 )
    s = layer.ngGetShape( result.shapeindex, result.tileindex )
    
    if pmstestlib.check_items( layer, s,
                               [('value_0','123'),
                                ('x','34.5'),
                                ('y','26.5')] ) == 0:
        return 'fail'
    
    #########################################################################
    # Check last shape attributes.

    result = layer.getResult( 8 )
    s = layer.ngGetShape( result.shapeindex, result.tileindex )

    if pmstestlib.check_items( layer, s,
                               [('value_0','107'),
                                ('x','36.5'),
                                ('y','24.5')] ) == 0:
        return 'fail'
    
    layer.close() 
    layer.close() # discard resultset.

    return 'success'
    
###############################################################################
# Execute multiple point query, and check result.

def rqtest_6():

    pnt = mapscript.Point()
    pnt.x = 35.2
    pnt.y = 25.3
    
    pmstestlib.layer.queryByPoint( pmstestlib.map, pnt, mapscript.MS_SINGLE,
                                   10.0 )

    return 'success'

###############################################################################
# Scan results, checking count and the first shape information.

def rqtest_7():
    layer = pmstestlib.layer
    
    #########################################################################
    # Check result count.
    layer.open()
    count = 0
    for i in range(1000):
        result = layer.getResult( i )
        if result is None:
            break
    
        count = count + 1

    if count != 1:
        pmstestlib.post_reason( 'got %d results instead of expected %d.' \
                             % (count, 1) )
        return 'fail'

    #########################################################################
    # Check first shape attributes.
    
    result = layer.getResult( 0 )
    s = layer.ngGetShape( result.shapeindex, result.tileindex )
    
    if pmstestlib.check_items( layer, s,
                               [('value_0','115'),
                                ('x','35.5'),
                                ('y','25.5')] ) == 0:
        return 'fail'
    
    layer.close() 
    layer.close() # discard resultset.

    return 'success'
    
###############################################################################
# Execute multiple point query, and check result.

def rqtest_8():

    rect = mapscript.Rect()
    rect.minx = 35
    rect.maxx = 45
    rect.miny = 25
    rect.maxy = 35
    
    pmstestlib.layer.queryByRect( pmstestlib.map, rect )

    return 'success'

###############################################################################
# Scan results, checking count and the first shape information.

def rqtest_9():
    layer = pmstestlib.layer
    
    #########################################################################
    # Check result count.
    layer.open()
    count = 0
    for i in range(1000):
        result = layer.getResult( i )
        if result is None:
            break
    
        count = count + 1

    if count != 100:
        pmstestlib.post_reason( 'got %d results instead of expected %d.' \
                             % (count, 100) )
        return 'fail'

    #########################################################################
    # Check first shape attributes.
    
    result = layer.getResult( 0 )
    s = layer.ngGetShape( result.shapeindex, result.tileindex )
    
    if pmstestlib.check_items( layer, s,
                               [('value_0','148'),
                                ('red','148'),
                                ('green','148'),
                                ('blue','148'),
                                ('values','148'),
                                ('x','35.5'),
                                ('y','34.5')] ) == 0:
        return 'fail'
    
    #########################################################################
    # Check last shape attributes.

    result = layer.getResult( 99 )
    s = layer.ngGetShape( result.shapeindex, result.tileindex )

    if pmstestlib.check_items( layer, s,
                               [('value_0','132'),
                                ('red','132'),
                                ('green','132'),
                                ('blue','132'),
                                ('values','132'),
                                ('x','44.5'),
                                ('y','25.5')] ) == 0:
        return 'fail'
    
    layer.close() 
    layer.close() # discard resultset.

    return 'success'
    
###############################################################################
# Close old map, and open a classified map and pst a point query.

def rqtest_10():

    pmstestlib.layer = None
    pmstestlib.map = None

    pmstestlib.map = mapscript.Map('../gdal/classtest1.map')
    pmstestlib.layer = pmstestlib.map.getLayer(0)
    
    pnt = mapscript.Point()
    pnt.x = 88.5
    pnt.y = 7.5
    
    pmstestlib.layer.queryByPoint( pmstestlib.map, pnt, mapscript.MS_SINGLE,
                                   10.0 )

    return 'success'

###############################################################################
# Scan results.  This query is for a transparent pixel within the "x" of
# the cubewerx logo.  In the future the raster query may well stop returning
# "offsite" pixels and we will need to update this test.

def rqtest_11():
    layer = pmstestlib.layer
    
    #########################################################################
    # Check result count.
    layer.open()
    count = 0
    for i in range(1000):
        result = layer.getResult( i )
        if result is None:
            break
    
        count = count + 1

    if count != 1:
        pmstestlib.post_reason( 'got %d results instead of expected %d.' \
                             % (count, 1) )
        return 'fail'

    #########################################################################
    # Check first shape attributes.
    
    result = layer.getResult( 0 )
    s = layer.ngGetShape( result.shapeindex, result.tileindex )
    
    if pmstestlib.check_items( layer, s,
                               [('value_0','0'),
                                ('red','-255'),
                                ('green','-255'),
                                ('blue','-255'),
                                ('class','Text'),
                                ('x','88.5'),
                                ('y','7.5')] ) == 0:
        return 'fail'
    
    layer.close() 
    layer.close() # discard resultset.

    return 'success'
    
###############################################################################
# Issue another point query, on colored text. 

def rqtest_12():

    pnt = mapscript.Point()
    pnt.x = 13.5
    pnt.y = 36.5
    
    pmstestlib.layer.queryByPoint( pmstestlib.map, pnt, mapscript.MS_SINGLE,
                                   2.0 )

    dumpResultSet( pmstestlib.layer )

    return 'success'

###############################################################################
# Scan results.  This query is for a transparent pixel within the "x" of
# the cubewerx logo.  In the future the raster query may well stop returning
# "offsite" pixels and we will need to update this test.

def rqtest_13():
    layer = pmstestlib.layer
    
    #########################################################################
    # Check result count.
    layer.open()
    count = 0
    for i in range(1000):
        result = layer.getResult( i )
        if result is None:
            break
    
        count = count + 1

    if count != 1:
        pmstestlib.post_reason( 'got %d results instead of expected %d.' \
                             % (count, 1) )
        return 'fail'

    #########################################################################
    # Check first shape attributes.
    
    result = layer.getResult( 0 )
    s = layer.ngGetShape( result.shapeindex, result.tileindex )
    
    if pmstestlib.check_items( layer, s,
                               [('value_0','0'),
                                ('red','-255'),
                                ('green','-255'),
                                ('blue','-255'),
                                ('class','Text'),
                                ('x','88.5'),
                                ('y','7.5')] ) == 0:
        return 'fail'
    
    layer.close() 
    layer.close() # discard resultset.

    return 'success'
    
###############################################################################
# Cleanup.

def rqtest_cleanup():
    pmstestlib.layer = None
    pmstestlib.map = None
    return 'success'

test_list = [
    rqtest_1,
    rqtest_2,
    rqtest_3,
    rqtest_4,
    rqtest_5,
    rqtest_6,
    rqtest_7,
    rqtest_8,
    rqtest_9,
    rqtest_10,
    rqtest_11,
#    rqtest_12,
    rqtest_cleanup ]

if __name__ == '__main__':

    pmstestlib.setup_run( 'rqtest' )

    pmstestlib.run_tests( test_list )

    pmstestlib.summarize()

