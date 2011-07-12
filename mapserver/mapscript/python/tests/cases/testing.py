# $Id$
#
# Project:  MapServer
# Purpose:  xUnit style Python mapscript testing utilities
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
# Purpose of this module is to export the locally built mapscript module
# prior to installation, do some name normalization that allows testing of
# the so-called next generation class names, and define some classes 
# useful to many test cases.
#
# All test case modules should import mapscript from testing
#
#     from testing import mapscript
#
# ===========================================================================

import os
import sys
import distutils.util
import unittest

# define the path to mapserver test data
TESTS_PATH = '../../../../tests'

TESTMAPFILE = os.path.join(TESTS_PATH, 'test.map')
XMARKS_IMAGE = os.path.join(TESTS_PATH, 'xmarks.png')
HOME_IMAGE = os.path.join(TESTS_PATH, 'home.png')
TEST_IMAGE = os.path.join(TESTS_PATH, 'test.png')

INCOMING = '/tmp/'

# Put local build directory on head of python path
platformdir = '-'.join((distutils.util.get_platform(), 
                        '.'.join(map(str, sys.version_info[0:2]))))
sys.path.insert(0, os.path.join('../../build', 'lib.' + platformdir))

# import mapscript from the local build directory
import mapscript

# ==========================================================================
# Base testing classes

class MapscriptTestCase(unittest.TestCase):

    def assertAlmostEqual(self, first, second, places=7):
        """Copied from unittest for use with Python 2.1 or 2.2"""
        if round(second-first, places) != 0:
            raise AssertionError, \
                '%s != %s within %s places' % (`first`, `second`, `places`)
        
class MapPrimitivesTestCase(MapscriptTestCase):
    """Base class for testing primitives (points, lines, shapes)
    in stand-alone mode"""

    def addPointToLine(self, line, point):
        """Using either the standard or next_generation_api"""
        try:
            line.add(point)
        except AttributeError: # next_generation_api
            line.addPoint(point)
        except:
            raise

    def getPointFromLine(self, line, index):
        """Using either the standard or next_generation_api"""
        try:
            point = line.get(index)
            return point
        except AttributeError: # next_generation_api
            point = line.getPoint(index)
            return point
        except:
            raise

    def addLineToShape(self, shape, line):
        """Using either the standard or next_generation_api"""
        try:
            shape.add(line)
        except AttributeError: # next_generation_api
            shape.addLine(line)
        except:
            raise

    def getLineFromShape(self, shape, index):
        """Using either the standard or next_generation_api"""
        try:
            line = shape.get(index)
            return line
        except AttributeError: # next_generation_api
            line = shape.getLine(index)
            return line
        except:
            raise

    def assertPointsEqual(self, first, second):
        self.assertAlmostEqual(first.x, second.x)
        self.assertAlmostEqual(first.y, second.y)
     
    def assertLinesEqual(self, first, second):
        assert first.numpoints == second.numpoints
        for i in range(first.numpoints):
            point_first = self.getPointFromLine(first, i)
            point_second = self.getPointFromLine(second, i)
            self.assertPointsEqual(point_first, point_second)

    def assertShapesEqual(self, first, second):
        assert first.numlines == second.numlines
        for i in range(first.numlines):
            line_first = self.getLineFromShape(first, i)
            line_second = self.getLineFromShape(second, i)
            self.assertLinesEqual(line_first, line_second)

    def assertRectsEqual(self, first, second):
        self.assertAlmostEqual(first.minx, second.minx)
        self.assertAlmostEqual(first.miny, second.miny)
        self.assertAlmostEqual(first.maxx, second.maxx)
        self.assertAlmostEqual(first.maxy, second.maxy)

class MapTestCase(MapPrimitivesTestCase):
    """Base class for testing with a map fixture"""
    def setUp(self):
        self.map = mapscript.mapObj(TESTMAPFILE)
        #self.xmarks_image = xmarks_image
        #self.test_image = test_image
    def tearDown(self):
        self.map = None

class MapZoomTestCase(MapPrimitivesTestCase):
    "Testing new zoom* methods that we are adapting from the PHP MapScript"
    def setUp(self):
        self.mapobj1 = mapscript.mapObj(TESTMAPFILE)
        # Change the extent for purposes of zoom testing
        rect = mapscript.rectObj()
        rect.minx, rect.miny, rect.maxx, rect.maxy = (-50.0, -50.0, 50.0, 50.0)
        self.mapobj1.extent = rect
        # Change height/width as well
        self.mapobj1.width, self.mapobj1.height = (100, 100)
    def tearDown(self):
        self.mapobj1 = None

class ShapeObjTestCase(MapPrimitivesTestCase):
    """Base class for shapeObj tests"""
    pass

