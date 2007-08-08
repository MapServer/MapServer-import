# $Id$
#
# Project:  MapServer
# Purpose:  xUnit style Python mapscript tests of Layer
# Author:   Sean Gillies, sgillies@frii.com
#
# ===========================================================================
# Copyright (c) 2004, Sean Gillies
# 
# Permission is hereby granted, free of charge, to any person obtaining a
# copy of this software and associated documentation files (the "Software"),
# to deal in the Software without restriction, including without limitation
# the rights to use, copy, modify, merge, publish, distribute, sublicense,
# and/or sell copies of the Software, and to permit persons to whom the
# Software is furnished to do so, subject to the following conditions:
#
# The above copyright notice and this permission notice shall be included
# in all copies or substantial portions of the Software.
#
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS
# OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
# FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL
# THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
# LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
# FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
# DEALINGS IN THE SOFTWARE.
# ===========================================================================
#
# Execute this module as a script from mapserver/mapscript/python
#
#     python tests/cases/layertest.py -v
#
# ===========================================================================

import os, sys
import unittest

# the testing module helps us import the pre-installed mapscript
from testing import mapscript
from testing import MapTestCase

# Base class
class MapLayerTestCase(MapTestCase):

    def setUp(self):
        MapTestCase.setUp(self)
        self.layer = self.map.getLayer(1)

# ===========================================================================
# Test begins now

class AlphaTransparencyTestCase(unittest.TestCase):
    
    def testMSGDALPHA(self):
        """test to make sure that no one has hidden ALPHA"""
        assert mapscript.MS_GD_ALPHA == 1000


class LayerConstructorTestCase(MapLayerTestCase):

    def testLayerConstructorNoArg(self):
        """test layer constructor with no argument"""
        layer = mapscript.layerObj()
        t = type(layer)
        assert str(t) == "<class 'mapscript.layerObj'>", t
        assert layer.thisown == 1
        assert layer.index == -1
	assert layer.map == None, layer.map
    
    def testLayerConstructorMapArg(self):
        """test layer constructor with map argument"""
        layer = mapscript.layerObj(self.map)
        t = type(layer)
        assert str(t) == "<class 'mapscript.layerObj'>", t
        assert layer.thisown == 1
        assert str(layer) == str(self.map.getLayer(self.map.numlayers-1))
	assert layer.map != None, layer.map
    
     

class LayerCloningTestCase(MapLayerTestCase):

    def testLayerCloning(self):
        """check attributes of a cloned layer"""
        clone = self.layer.clone()
        assert clone.thisown == 1
        assert str(clone) != str(self.layer)
        assert clone.name == self.layer.name
        assert clone.numclasses == self.layer.numclasses
        assert clone.map == None, clone.map
        assert clone.data == self.layer.data
        
class LayerExtentTestCase(MapTestCase):
   
    def setUp(self):
        MapTestCase.setUp(self)
        self.layer = self.map.getLayerByName('POLYGON')

    def testPolygonExtent(self):
        """retrieve the extent of a polygon layer"""
        e = mapscript.rectObj()
        self.assertRectsEqual(e, self.layer.extent)

    def testPolygonGetExtent(self):
        """retrieve the extent of a polygon layer"""
        e = mapscript.rectObj(-0.25, 51.227222, 0.25, 51.727222)
        self.assertRectsEqual(e, self.layer.getExtent())
        
    def testGetPresetExtent(self):
        """test layer.setExtent() and layer.getExtent() to return preset instead of calculating extents"""
        r = mapscript.rectObj(1.0, 1.0, 3.0, 3.0)
        self.layer.setExtent(r.minx, r.miny, r.maxx, r.maxy)
        rect = self.layer.extent
        assert r.minx == rect.minx, rect
        assert r.miny == rect.miny, rect.miny
        assert r.maxx == rect.maxx, rect.maxx
        assert r.maxy == rect.maxy, rect.maxy
        
    def testResetLayerExtent(self):
        """test resetting a layer's extent"""
        layer = self.map.getLayerByName('POLYGON')
        layer.setExtent()
        self.assertRectsEqual(layer.extent, mapscript.rectObj())

    def testDirectExtentAccess(self):
        """direct access to a layer's extent works properly"""
        pt_layer = self.map.getLayerByName('POINT')
        rect = pt_layer.extent
        assert str(pt_layer.extent) == str(rect), (pt_layer.extent, rect)
        e = mapscript.rectObj(-0.5, 51.0, 0.5, 52.0)
        self.assertRectsEqual(e, rect)
        
class LayerRasterProcessingTestCase(MapLayerTestCase):
    
    def testSetProcessing(self):
        """setting a layer's processing directive works"""
        self.layer.setProcessing('directive0=foo')
        assert self.layer.numprocessing == 1, self.layer.numprocessing
        self.layer.setProcessing('directive1=bar')
        assert self.layer.numprocessing == 2, self.layer.numprocessing
        directives = [self.layer.getProcessing(i) \
                      for i in range(self.layer.numprocessing)]
        assert directives == ['directive0=foo', 'directive1=bar']

    def testClearProcessing(self):
        """clearing a self.layer's processing directive works"""
        self.layer.setProcessing('directive0=foo')
        assert self.layer.numprocessing == 1, self.layer.numprocessing
        self.layer.setProcessing('directive1=bar')
        assert self.layer.numprocessing == 2, self.layer.numprocessing
        assert self.layer.clearProcessing() == mapscript.MS_SUCCESS

class RemoveClassTestCase(MapLayerTestCase):

    def testRemoveClass1NumClasses(self):
        """RemoveClassTestCase.testRemoveClass1NumClasses: removing the layer's first class by index leaves one class left"""
        c = self.layer.removeClass(0)
        assert c.thisown == 1
        assert self.layer.numclasses == 1
    
    def testRemoveClass1ClassName(self):
        """RemoveClassTestCase.testRemoveClass1ClassName: confirm removing the layer's first class reverts the name of the second class"""
        c2name = self.layer.getClass(1).name
        c = self.layer.removeClass(0)
        assert self.layer.getClass(0).name == c2name
    
    def testRemoveClass2NumClasses(self):
        """RemoveClassTestCase.testRemoveClass2NumClasses: removing the layer's second class by index leaves one class left"""
        c = self.layer.removeClass(1)
        assert self.layer.numclasses == 1
    
    def testRemoveClass2ClassName(self):
        """RemoveClassTestCase.testRemoveClass2ClassName: confirm removing the layer's second class reverts the name of the first class"""
        c1name = self.layer.getClass(0).name
        c = self.layer.removeClass(1)
        assert self.layer.getClass(0).name == c1name

class InsertClassTestCase(MapLayerTestCase):

    def testLayerInsertClass(self):
        """insert class at default index"""
        n = self.layer.numclasses
        new_class = mapscript.classObj()
        new_class.name = 'foo'
        new_index = self.layer.insertClass(new_class)
        assert new_index == n
        assert self.layer.numclasses == n + 1
        c = self.layer.getClass(new_index)
        assert c.thisown == 1 
        assert c.name == new_class.name
        
    def testLayerInsertClassAtZero(self):
        """insert class at index 0"""
        n = self.layer.numclasses
        new_class = mapscript.classObj()
        new_class.name = 'foo'
        new_index = self.layer.insertClass(new_class, 0)
        assert new_index == 0
        assert self.layer.numclasses == n + 1
        c = self.layer.getClass(new_index)
        assert c.thisown == 1 
        assert c.name == new_class.name

    def testInsertNULLClass(self):
        """inserting NULL class should raise an error"""
        self.assertRaises(mapscript.MapServerChildError,
                          self.layer.insertClass, None)
    
class LayerTestCase(MapTestCase):
    def testLayerConstructorOwnership(self):
        """LayerTestCase.testLayerConstructorOwnership: newly constructed layer has proper ownership"""
        layer = mapscript.layerObj(self.map)
        assert layer.thisown == 1
    def testGetLayerOrder(self):
        """LayerTestCase.testGetLayerOrder: get layer drawing order"""
        order = self.map.getLayerOrder()
        assert order == tuple(range(7)), order
    def testSetLayerOrder(self):
        """LayerTestCase.testSetLayerOrder: set layer drawing order"""
        ord = (1, 0, 2, 3, 4, 5, 6)
        self.map.setLayerOrder(ord)
        order = self.map.getLayerOrder()
        assert order == ord, order

# Layer removal tests
class RemoveLayerTestCase(MapTestCase):
    
    def testRemoveLayer1NumLayers(self):
        """removing the first layer by index from the mapfile leaves three"""
        self.map.removeLayer(0)
        assert self.map.numlayers == 6
    
    def testRemoveLayer1LayerName(self):
        """removing first layer reverts it to the second layer's name"""
        l2name = self.map.getLayer(1).name
        self.map.removeLayer(0)
        assert self.map.getLayer(0).name == l2name
    
    def testRemoveLayer2NumLayers(self):
        """removing second layer by index from mapfile leaves three layers"""
        self.map.removeLayer(1)
        assert self.map.numlayers == 6
    
    def testRemoveLayer2LayerName(self):
        """removing of the second layer reverts it to the first layer's name"""
        l1name = self.map.getLayer(0).name
        self.map.removeLayer(1)
        assert self.map.getLayer(0).name == l1name

class ExpressionTestCase(MapLayerTestCase):
    
    def testClearExpression(self):
        """layer expression can be properly cleared"""
        self.layer.setFilter('')
        fs = self.layer.getFilterString()
        assert fs == None, fs
    
    def testSetStringExpression(self):
        """layer expression can be set to string"""
        self.layer.setFilter('foo')
        fs = self.layer.getFilterString()
        self.layer.filteritem = 'fid'
        assert fs == '"foo"', fs
        self.map.draw()
    
    def testSetQuotedStringExpression(self):
        """layer expression string can be quoted"""
        self.layer.setFilter('"foo"')
        fs = self.layer.getFilterString()
        self.layer.filteritem = 'fid'
        assert fs == '"foo"', fs
        self.map.draw()
    
    def testSetRegularExpression(self):
        """layer expression can be regular expression"""
        self.layer.setFilter('/foo/')
        self.layer.filteritem = 'fid'
        fs = self.layer.getFilterString()
        assert fs == '/foo/', fs
        self.map.draw()
    
    def testSetLogicalExpression(self):
        """layer expression can be logical expression"""
        self.layer.setFilter('([fid] >= 2)')
        fs = self.layer.getFilterString()
        assert fs == '([fid] >= 2)', fs
        self.map.draw()
       
    def testSetCompoundLogicalExpression(self):
        """layer expression can be a compound logical expression"""
	#filter = '( ([fid] >= 2) AND (\'[fname]\' == \'A Polygon\' ))'
        flt = """( ([fid] >= 2) AND ("[fname]" == 'A Polygon' ))"""
        excode = self.layer.setFilter(flt)
        assert excode == mapscript.MS_SUCCESS, excode
        fs = self.layer.getFilterString()
        assert fs == flt, fs
        self.map.draw()
       

class LayerQueryTestCase(MapLayerTestCase):

    def setUp(self):
        MapLayerTestCase.setUp(self)
        self.layer = self.map.getLayerByName('POINT')
        self.layer.template = 'foo'

class SpatialLayerQueryTestCase(LayerQueryTestCase):

    def testRectQuery(self):
        qrect = mapscript.rectObj(-10.0, 45.0, 10.0, 55.0)
        self.layer.queryByRect(self.map, qrect)
        assert self.layer.getNumResults() == 1

    def testShapeQuery(self):
        qrect = mapscript.rectObj(-10.0, 45.0, 10.0, 55.0)
        qshape = qrect.toPolygon()
        self.layer.queryByShape(self.map, qshape)
        assert self.layer.getNumResults() == 1

    def testPointQuery(self):
        qpoint = mapscript.pointObj(0.0, 51.5)
        self.layer.queryByPoint(self.map, qpoint, mapscript.MS_MULTIPLE, 2.0)
        assert self.layer.getNumResults() == 1
   
    def testRectQueryNoResults(self):
        qrect = mapscript.rectObj(-101.0, 0.0, -100.0, 1.0)
        self.layer.queryByRect(self.map, qrect)
        assert self.layer.getNumResults() == 0

    def testShapeQueryNoResults(self):
        qrect = mapscript.rectObj(-101.0, 0.0, -100.0, 1.0)
        qshape = qrect.toPolygon()
        self.layer.queryByShape(self.map, qshape)
        assert self.layer.getNumResults() == 0

    def testPointQueryNoResults(self):
        qpoint = mapscript.pointObj(-100.0, 51.5)
        self.layer.queryByPoint(self.map, qpoint, mapscript.MS_MULTIPLE, 2.0)
        assert self.layer.getNumResults() == 0
    

class AttributeLayerQueryTestCase(LayerQueryTestCase):

    def testAttributeQuery(self):
        self.layer.queryByAttributes(self.map, "FNAME", '"A Point"',
                                     mapscript.MS_MULTIPLE)
        assert self.layer.getNumResults() == 1

    def testLogicalAttributeQuery(self):
        self.layer.queryByAttributes(self.map, None, '("[FNAME]" == "A Point")',
                                     mapscript.MS_MULTIPLE)
        assert self.layer.getNumResults() == 1

    def testAttributeQueryNoResults(self):
        self.layer.queryByAttributes(self.map, "FNAME", '"Bogus Point"',
                                     mapscript.MS_MULTIPLE)
        assert self.layer.getNumResults() == 0


class LayerVisibilityTestCase(MapLayerTestCase):
    
    def setUp(self):
        MapLayerTestCase.setUp(self)
        self.layer.minscaledenom = 1000
        self.layer.maxscaledenom = 2000
        self.layer.status = mapscript.MS_ON
        self.map.zoomScale(1500, mapscript.pointObj(100,100), 200, 200, self.map.extent, None)
    
    def testInitialVisibility(self):
        """expect visibility"""
        assert self.layer.isVisible() == mapscript.MS_TRUE

    def testStatusOffVisibility(self):
        """expect false visibility after switching status off"""
        self.layer.status = mapscript.MS_OFF
        assert self.layer.isVisible() == mapscript.MS_FALSE

    def testZoomOutVisibility(self):
        """expect false visibility after zooming out beyond maximum"""
        self.map.zoomScale(2500, mapscript.pointObj(100,100), 200, 200, self.map.extent, None)
        assert self.layer.isVisible() == mapscript.MS_FALSE
       

from random import random

class InlineLayerTestCase(unittest.TestCase):

    def setUp(self):
        # Inline feature layer
        self.ilayer = mapscript.layerObj()
        self.ilayer.type = mapscript.MS_LAYER_POLYGON
        self.ilayer.status = mapscript.MS_DEFAULT
        self.ilayer.connectiontype = mapscript.MS_INLINE

        cs = 'f7fcfd,e5f5f9,ccece6,99d8c9,66c2a4,41ae76,238b45,006d2c,00441b'
        colors = ['#' + h for h in cs.split(',')]
        #print colors
        
        for i in range(9):
            # Make a class for feature
            ci = self.ilayer.insertClass(mapscript.classObj())
            co = self.ilayer.getClass(ci)
            si = co.insertStyle(mapscript.styleObj())
            so = co.getStyle(si)
            so.color.setHex(colors[i])
            co.label.color.setHex('#000000')
            co.label.outlinecolor.setHex('#FFFFFF')
            co.label.type = mapscript.MS_BITMAP
            co.label.size = mapscript.MS_SMALL
            
            # The shape to add is randomly generated
            xc = 4.0*(random() - 0.5)
            yc = 4.0*(random() - 0.5)
            r = mapscript.rectObj(xc-0.25, yc-0.25, xc+0.25, yc+0.25)
            s = r.toPolygon()
            
            # Classify
            s.classindex = i
            s.text = "F%d" % (i)
            
            # Add to inline feature layer
            self.ilayer.addFeature(s)

    def testExternalClassification(self):
        mo = mapscript.mapObj()
        mo.setSize(400, 400)
        mo.setExtent(-2.5, -2.5, 2.5, 2.5)
        mo.selectOutputFormat('image/png')
        mo.insertLayer(self.ilayer)
        im = mo.draw()
        im.save('testExternalClassification.png')


# ===========================================================================
# Run the tests outside of the main suite

if __name__ == '__main__':
    unittest.main()
    
