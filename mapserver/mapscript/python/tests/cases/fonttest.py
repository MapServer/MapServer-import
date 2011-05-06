# $Id$
#
# Project:  MapServer
# Purpose:  xUnit style Python mapscript tests of hashTableObj
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
#     python tests/cases/hashtest.py -v
#
# ===========================================================================

import os, sys
import unittest

# the testing module helps us import the pre-installed mapscript
from testing import mapscript, TESTMAPFILE, TESTS_PATH


class FontTestCase(unittest.TestCase):

    def testSettingFonts(self):
        mo = mapscript.mapObj()
        assert mo.fontset.numfonts == 0
        mo.fontset.fonts.set('Vera', os.path.join(TESTS_PATH, 'vera',
                                                  'Vera.ttf'))
        # NB: this does *not* increment the fonset.numfonts -- new bug
                                                  
        mo.setSize(300, 300)
        mo.setExtent(-1.0, -1.0, 1.0, 1.0)
        
        lo = mapscript.layerObj()
        lo.type = mapscript.MS_LAYER_POINT
        lo.connectiontype = mapscript.MS_INLINE
        lo.status = mapscript.MS_DEFAULT

        co = mapscript.classObj()
        co.label.type = mapscript.MS_TRUETYPE
        co.label.font = 'Vera'
        co.label.size = 10
        co.label.color.setHex('#000000')

        so = mapscript.styleObj()
        so.symbol = 0
        so.color.setHex('#000000')
        
        co.insertStyle(so)
        lo.insertClass(co)
        li = mo.insertLayer(lo)
        lo = mo.getLayer(li)

        point = mapscript.pointObj(0,0)
        line = mapscript.lineObj()
        line.add(point)
        shape = mapscript.shapeObj(lo.type)
        shape.add(line)
        shape.setBounds()
        shape.text = 'Foo'
        shape.classindex = 0

        lo.addFeature(shape)
        im = mo.draw()
        
        #im = mo.prepareImage()
        #shape.draw(mo, lo, im)
        im.save('testSettingFonts.png')
        
        

# ===========================================================================
# Run the tests outside of the main suite

if __name__ == '__main__':
    unittest.main()
    
