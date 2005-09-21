.. $Id$

   ===========================================================================
   Copyright (c) 2005 Jeff McKenna, DM Solutions Group Inc.
   
   Permission is hereby granted, free of charge, to any person obtaining a
   copy of this software and associated documentation files (the "Software"),
   to deal in the Software without restriction, including without limitation
   the rights to use, copy, modify, merge, publish, distribute, sublicense,
   and/or sell copies of the Software, and to permit persons to whom the
   Software is furnished to do so, subject to the following conditions:
 
   The above copyright notice and this permission notice shall be included
   in all copies or substantial portions of the Software.
 
   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS
   OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL
   THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
   DEALINGS IN THE SOFTWARE.
   ===========================================================================
..

*****************************************************************************
 MapServer Styled Layer Descriptor (SLD) HOWTO - Version 4.6
*****************************************************************************

:Author: Jeff McKenna
:Contact: jmckenna@dmsolutions.ca
:Author: Yewondwossen Assefa
:Contact: assefa@dmsolutions.ca
:Revision: $Revision$
:Last Updated: $Date$

..  The next heading encountered becomes our H2
..

.. sectnum::

.. contents:: Table of Contents
    :depth: 2
    :backlinks: top


Introduction
============

This document describes the procedures for taking advantage of the Styled 
Layer Descriptor (SLD) support in WMS GetMap requests for MapServer 4.6.
SLD support has been developed for the server side support (ability to 
read an SLD and apply it with a GetMap request) and for the client side 
(includes sending SLD requests to server and generate SLD files on the fly 
from MapServer map file).

This document assumes that you are already familiar with the following 
aspects of MapServer:

- MapServer application development and setting up *.map* files.
- Familiarity with the WMS specification would be an asset. Links to the 
  MapServer WMS documents are included in the next section.

Links to SLD-related Information
--------------------------------

- `Styled Layer Descriptor Implementation Specification`_.
- `MapServer WMS Client HOWTO`_.
- `MapServer WMS Server HOWTO`_.
- `Open GIS Consortium (OGC) home page`_.

.. _`Styled Layer Descriptor Implementation Specification`: http://www.opengeospatial.org/docs/02-070.pdf
.. _`MapServer WMS Client HOWTO`: http://ms.gis.umn.edu/docs/howto/wms_client
.. _`MapServer WMS Server HOWTO`: http://ms.gis.umn.edu/docs/howto/wms_server
.. _`Open GIS Consortium (OGC) home page`: http://www.opengeospatial.org

Server Side Support
===================

General Information
-------------------

There are two ways a WMS request can pass an SLD document with a GetMap 
request to MapServer:

- SLD parameter pointing to remote SLD (SLD=http://URL_TO_SLD).
- SLD_BODY parameter to send the SLD definition in the URL.

These two methods are both available through MapServer. An example of a request 
would be:

http://www2.dmsolutions.ca/cgi-bin/mswms_world?SERVICE=WMS&amp;VeRsIoN=1.1.1&amp;Request=GetMap&amp;LAYERS=WorldGen_Outline&amp;SLD=http://www2.dmsolutions.ca/msapps/world_testdata/tests/sld_tests/sld_line_simple.xml

The SLD in the above request follows:

::

        <StyledLayerDescriptor version="1.0.0">
          <NamedLayer>
            <Name>WorldGen_Outline</Name>
            <UserStyle>
              <Title>xxx</Title>
              <FeatureTypeStyle>
                <Rule>
                <LineSymbolizer>
                 <Geometry>
                   <PropertyName>center-line</PropertyName>
                 </Geometry>
                 <Stroke>
                   <CssParameter name="stroke">#0000ff</CssParameter>
                 </Stroke>
                </LineSymbolizer>
                </Rule>
              </FeatureTypeStyle>
            </UserStyle>
          </NamedLayer>
        </StyledLayerDescriptor> 
        
When MapServer gets a valid SLD through a request, it parses this SLD to extract 
all the styles attached to the NamedLayers, and then it applies these styles to 
the map before it is returned to the client. When applying the SLD, MapServer 
compares the names used in the map files with the names of the NamedLayers in 
the SLD document.

Note: All the examples given in this document are live uses of valid SLDs and 
a MapServer installation with SLD support.

Additional WMS features related to SLDs have also been developed:

**Table1. Additional WMS Features**

=====================  ========= =============================
Features               Supported Notes
=====================  ========= =============================
Method GET : SLD URL   Yes
Method GET : SLD_BODY  Yes       Additional item
Describer Layer        Yes
GetLegendGraphic       Yes
GetStyles              Yes       Uses MapScript to get the SLD
=====================  ========= =============================

Note: As of MapServer version 4.2.3, the GetLegendGraphic request (see section 12 of the
`Styled Layer Descriptor Implementation Specification`_) 
works as follows: if the RULE keyword is absent from the request, an image containing the entire legend for the specified layer will be returned. 
This image consists of the layer name and a symbolization graphic and label for each class.  

Specific SLD Elements Supported
-------------------------------

The following tables give a lot of additional details about SLD support in MapServer.

**Table2. Named Layers and User Layers**

============ ========= =====
Features     Supported Notes
============ ========= =====
Named Layers Yes  
User Layers  No   
============ ========= =====

**Table3. Named Styles and User Styles**

============ ========= =====
Features     Supported Notes
============ ========= =====
Named Styles No  
User Styles  Yes  
============ ========= =====

**Table 4. User Styles**

================ ========= =====================================================================================================
Features         Supported Notes
================ ========= =====================================================================================================
Name             No        This was removed at implementation time, since it does not fit with MapServer
Title            No        No use in the MapServer environment
Abstract         No        No use in the MapServer environment
IsDefault        No        Only one style is available per layer
FeatureTypeStyle Yes       MapServer has a concept of one feature type style per layer (either point, line, polygon, or raster)
================ ========= =====================================================================================================

**Table 5. FeatureTypeStyle**

====================== ========= ========================================================
Features               Supported Notes
====================== ========= ========================================================
Name                   No        No use in the MapServer environment
Title                  No        No use in the MapServer environment
Abstract               No        No use in the MapServer environment
FeatureTypeName        No        No use in the MapServer environment
SemanticTypeIdentifier No        Still an experimental element in the SLD specifications
Rule                   Yes 
====================== ========= ======================================================== 

**Table 6. Rule**

=================== ========= ===================================
Features            Supported               Notes
=================== ========= ===================================
Name                Yes  
Title               Yes  
Abstract            No        No use in the MapServer environment 
LegendGraphic       Yes  
Filter              Yes  
ElseFilter          Yes  
MinScaleDenominator Yes  
MaxScaleDenominator Yes  
LineSymbolizer      Yes  
PolygonSymbolizer   Yes  
PointSymbolizer     Yes  
TextSymbolizer      Yes  
RasterSymbolizer    Yes       Applies for 8-bit rasters
=================== ========= ===================================

- Filter and ElseFilter

  For each rule containing a filter, there is a class created with the class 
  expression set to reflect that filter. Available filters that can be used 
  are Comparison Filters and Logical Filters (see the `Filter Encoding HOWTO`_).
  The ElseFilter parameters are converted into a class in MapServer and placed 
  at the end of the class list with no expression set. They are used to render 
  elements that did not fit into any other classes.
  
.. _`Filter Encoding HOWTO`: http://mapserver.gis.umn.edu/doc/filter-encoding-howto.html  
  
- MinScaleDenomibator and MaxScaleDenominator are translated in minscale and 
  maxscale in MapServer.
  
The following are examples of valid requests using the Filters:
 
- line with one filter: `sld 6a`_ / `full request 6a`_

.. _`sld 6a`: http://www2.dmsolutions.ca/msapps/world_testdata/tests/sld_tests/sld_line_one_filter.xml
.. _`full request 6a`: http://www2.dmsolutions.ca/cgi-bin/mswms_world?SERVICE=WMS&VeRsIoN=1.1.1&Request=GetMap&LAYERS=WorldGen_Outline&SLD=http://www2.dmsolutions.ca/msapps/world_testdata/tests/sld_tests/sld_line_one_filter.xml

- line with multiple filters: `sld 6b`_ / `full request 6b`_

.. _`sld 6b`: http://www2.dmsolutions.ca/msapps/world_testdata/tests/sld_tests/sld_line_multi_filter.xml
.. _`full request 6b`: http://www2.dmsolutions.ca/cgi-bin/mswms_world?SERVICE=WMS&VeRsIoN=1.1.1&Request=GetMap&LAYERS=WorldGen_Outline&SLD=http://www2.dmsolutions.ca/msapps/world_testdata/tests/sld_tests/sld_line_multi_filter.xml

- line with one filter and an else filter: `sld 6c`_ / `full request 6c`_

.. _`sld 6c`: http://www2.dmsolutions.ca/msapps/world_testdata/tests/sld_tests/sld_line_one_filter_and_else.xml
.. _`full request 6c`: http://www2.dmsolutions.ca/cgi-bin/mswms_world?SERVICE=WMS&VeRsIoN=1.1.1&Request=GetMap&LAYERS=WorldGen_Outline&SLD=http://www2.dmsolutions.ca/msapps/world_testdata/tests/sld_tests/sld_line_one_filter_and_else.xml

- spatial filter using BBOX: `sld 6d`_/ `full request 6d`_

.. _`sld 6d`: http://www2.dmsolutions.ca/msapps/world_testdata/tests/sld_tests/sld_line_simple_spatial3.xml
.. _`full request 6d`: http://www2.dmsolutions.ca/cgi-bin/mswms_world?SERVICE=WMS&VeRsIoN=1.1.1&Request=GetMap&LAYERS=WorldGen_Outline&SLD=http://www2.dmsolutions.ca/msapps/world_testdata/tests/sld_tests/sld_line_simple_spatial3.xml

  - The above example enables spatial filtering using the BBOX parameter as a 
    Filter for a selected area (Africa). Note that an ElseFilter will not work 
    with a spatial filter.
    
**Table 7. LineSymbolizer**

=========================================== ========= ====================================================
Features                                    Supported Notes
=========================================== ========= ====================================================
Geometry                                    No        MapServer uses the data geometry to do the rendering
Stroke: GraphicFill                         No        Solid color is used
Stroke: GraphicStroke                       No        Solid color is used
Stroke (CssParameter): stroke               Yes       RGB colors are supported
Stroke (CssParameter): width                Yes  
Stroke (CssParameter): opacity              No        Not supported in MapServer
Stroke (CssParameter): linejoin and linecap No        Not supported in MapServer
Stroke (CssParameter): dasharray            Yes  
Stroke (CssParameter): dashoffset           No 
=========================================== ========= ====================================================

The following are examples of valid requests using the LineSymbolizer:

- simple line: `sld 7a`_ / `full request 7a`_

.. _`sld 7a`: http://www2.dmsolutions.ca/msapps/world_testdata/tests/sld_tests/sld_line_simple.xml
.. _`full request 7a`: http://www2.dmsolutions.ca/cgi-bin/mswms_world?SERVICE=WMS&VeRsIoN=1.1.1&Request=GetMap&LAYERS=WorldGen_Outline&SLD=http://www2.dmsolutions.ca/msapps/world_testdata/tests/sld_tests/sld_line_simple.xml

- line with width: `sld 7b`_ / `full request 7b`_

.. _`sld 7b`: http://www2.dmsolutions.ca/msapps/world_testdata/tests/sld_tests/sld_line_width.xml
.. _`full request 7b`: http://www2.dmsolutions.ca/cgi-bin/mswms_world?SERVICE=WMS&VeRsIoN=1.1.1&Request=GetMap&LAYERS=WorldGen_Outline&SLD=http://www2.dmsolutions.ca/msapps/world_testdata/tests/sld_tests/sld_line_width.xml

- dashed line: `sld 7c`_ / `full request 7c`_

.. _`sld 7c`: http://www2.dmsolutions.ca/msapps/world_testdata/tests/sld_tests/sld_line_dash.xml
.. _`full request 7c`: http://www2.dmsolutions.ca/cgi-bin/mswms_world?SERVICE=WMS&VeRsIoN=1.1.1&Request=GetMap&LAYERS=WorldGen_Outline&SLD=http://www2.dmsolutions.ca/msapps/world_testdata/tests/sld_tests/sld_line_dash.xml

**Table 8. PolygonSymbolizer**

======== ========= ======================================================================
Features Supported Notes
======== ========= ======================================================================
Geometry No   
Stroke   Yes       Strokes are the same as for the LineSymbolizer
Fill     Yes       Was developed to support symbol fill polygons in addition to solid fill
======== ========= ======================================================================

A Fill can be a solid fill or be a Graphic Fill, which is either a well-known 
Mark symbol (e.g., square, circle, triangle, star, cross, x) or an 
ExternalGraphic element (e.g., gif, png) available through a URL.  When a Mark 
symbol is used in an SLD, MapServer creates a corresponding symbol in the map 
file and uses it to render the symbols.  When a ExternalGraphic is used, the 
file is saved locally and a pixmap symbol is created in the mapfile referring 
to the this file. Note that the Web object IMAGEPATH is used to save the file. 

The following are examples of valid requests using the PolygonSymbolizer:

- simple solid fill: `sld 8a`_ / `full request 8a`_

.. _`sld 8a`: http://www2.dmsolutions.ca/msapps/world_testdata/tests/sld_tests/sld_polygon_solid_fill.xml
.. _`full request 8a`: http://www2.dmsolutions.ca/cgi-bin/mswms_world?SERVICE=WMS&VeRsIoN=1.1.1&Request=GetMap&LAYERS=WorldGen&SLD=http://www2.dmsolutions.ca/msapps/world_testdata/tests/sld_tests/sld_polygon_solid_fill.xml

- solid fill with outline: `sld 8b`_ / `full request 8b`_

.. _`sld 8b`: http://www2.dmsolutions.ca/msapps/world_testdata/tests/sld_tests/sld_polygon_solid_fill_outline.xml
.. _`full request 8b`: http://www2.dmsolutions.ca/cgi-bin/mswms_world?SERVICE=WMS&VeRsIoN=1.1.1&Request=GetMap&LAYERS=WorldGen&SLD=http://www2.dmsolutions.ca/msapps/world_testdata/tests/sld_tests/sld_polygon_solid_fill_outline.xml

- fill with mark symbol: `sld 8c`_ / `full request 8c`_

.. _`sld 8c`: http://www2.dmsolutions.ca/msapps/world_testdata/tests/sld_tests/sld_polygon_fill_symbol.xml
.. _`full request 8c`: http://www2.dmsolutions.ca/cgi-bin/mswms_world?SERVICE=WMS&VeRsIoN=1.1.1&Request=GetMap&LAYERS=WorldGen&SLD=http://www2.dmsolutions.ca/msapps/world_testdata/tests/sld_tests/sld_polygon_fill_symbol.xml

- fill with external symbol: `sld 8d`_/ `full request 8d`_

.. _`sld 8d`: http://www2.dmsolutions.ca/msapps/world_testdata/tests/sld_tests/sld_polygon_fill_symbol_external.xml
.. _`full request 8d`: http://www2.dmsolutions.ca/cgi-bin/mswms_world?SERVICE=WMS&VeRsIoN=1.1.1&Request=GetMap&LAYERS=WorldGen&SLD=http://www2.dmsolutions.ca/msapps/world_testdata/tests/sld_tests/sld_polygon_fill_symbol_external.xml

**Table 9. PointSymbolizer**

======================== ========= ========================================================================= 
Features                 Supported Notes
======================== ========= ========================================================================= 
Geometry                 No   
Graphic: Mark symbol     Yes       Well-known names (square, circle, triangle, star, cross, X) are supported
Graphic: ExternalGraphic Yes       Was developed to support symbol fill polygons in addition to solid fill
Opacity                  No        Not supported in MapServer
Size                     Yes       Not supported in MapServer
Rotation                 No        Not supported in MapServer
======================== ========= ========================================================================= 

Note: refer to the PolygonSymbolizer notes for how the Mark and ExternalGraphic symbols are applied in MapServer.

The following are examples of valid requests using the PointSymbolizer:

- filled mark symbol: `sld 9a`_ / `full request 9a`_

.. _`sld 9a`: http://www2.dmsolutions.ca/msapps/world_testdata/tests/sld_tests/sld_symbol.xml
.. _`full request 9a`: http://www2.dmsolutions.ca/cgi-bin/mswms_world?SERVICE=WMS&VeRsIoN=1.1.1&Request=GetMap&LAYERS=WorldPOI&BBOX=-84.7978536015,41.440374,-75.737539764,45.97524&SLD=http://www2.dmsolutions.ca/msapps/world_testdata/tests/sld_tests/sld_symbol.xml

- default settings (square, size 6, color 128/128/128): `sld 9b`_ / `full request 9b`_

.. _`sld 9b`: http://www2.dmsolutions.ca/msapps/world_testdata/tests/sld_tests/sld_symbol_default_settings.xml
.. _`full request 9b`: http://www2.dmsolutions.ca/cgi-bin/mswms_world?SERVICE=WMS&VeRsIoN=1.1.1&Request=GetMap&LAYERS=WorldPOI&BBOX=-84.7978536015,41.440374,-75.737539764,45.97524&SLD=http://www2.dmsolutions.ca/msapps/world_testdata/tests/sld_tests/sld_symbol_default_settings.xml

- external symbol: `sld 9c`_ / `full request 9c`_

.. _`sld 9c`: http://www2.dmsolutions.ca/msapps/world_testdata/tests/sld_tests/sld_symbol_external.xml
.. _`full request 9c`: http://www2.dmsolutions.ca/cgi-bin/mswms_world?SERVICE=WMS&VeRsIoN=1.1.1&Request=GetMap&LAYERS=WorldPOI&BBOX=-84.7978536015,41.440374,-75.737539764,45.97524&SLD=http://www2.dmsolutions.ca/msapps/world_testdata/tests/sld_tests/sld_symbol_external.xml

**Table 10. TextSymbolizer**

======================== ========= ==========================================================================================================================
Features                 Supported Notes
======================== ========= ==========================================================================================================================
Geometry                 No   
Label                    Yes  
Font(font-family)        Yes       Font names used are those available in MapServer font file. If no fonts are available there, default bitmap fonts are used
Font-style (Italic, ...) Yes  
Font-weight              Yes  
Font-size                Yes       If true-type fonts are not used, default bitmap sizes are given
LabelPlacement           Yes       Only PointPlacement is supported
Halo                     No        Only solid color is available
Fill                     No        Only solid color is available
======================== ========= ==========================================================================================================================

Notes on the TextSymbolizer:

- Font names: when converting Font parameters to MapServer, the following rule
  is applied to get the font name: FontFamily-FontStyle-FontWeight.
  For example, if there is an SLD with a Font Family of arial, a Font Style of
  italic, and a Font weight equal to bold, the resulting MapServer font name 
  is arial-italic-bold.  Font Style and Weight are not mandatory and, if not 
  available, they are not used in building the font name.  When a Font Style or 
  a Font Weight is set to normal in an SLD, it is also ignored in building 
  the name. For example, if there is an SLD with a Font Family of arial, a Font 
  Style of normal and a Font weight equals to bold, the resulting MapServer font 
  name is arial-bold.

- A TextSymbolizer can be used in MapServer either on an Annotation layer or on a 
  Point, Line, or Polygon layer - in addition to other symbolizers used for these 
  layers.

- PointPacement: a point placement includes AnchorPoint (which is translated to 
  Position in MapServer) Displacement (which is translated to Offset) and Angle 
  (which is translated to Angle). 

The following are examples of valid requests using the TextSymbolizer:

- annotation layer : test for label, font, point placement, color, angle: `sld 10a`_ / `full request 10a`_

.. _`sld 10a`: http://www2.dmsolutions.ca/msapps/world_testdata/tests/sld_tests/sld_text_annotation.xml
.. _`full request 10a`: http://www2.dmsolutions.ca/cgi-bin/mswms_world?SERVICE=WMS&VeRsIoN=1.1.1&Request=GetMap&LAYERS=WorldPlaces&BBOX=-81.366241839,42.39269586,-77.8780568047,44.13861927&SLD=http://www2.dmsolutions.ca/msapps/world_testdata/tests/sld_tests/sld_text_annotation.xml

- annotation layer with text and symbols using 2 symbolizers: `sld 10b`_ / `full request 10b`_

.. _`sld 10b`: http://www2.dmsolutions.ca/msapps/world_testdata/tests/sld_tests/sld_text_with_symbols.xml
.. _`full request 10b`: http://www2.dmsolutions.ca/cgi-bin/mswms_world?SERVICE=WMS&VeRsIoN=1.1.1&Request=GetMap&LAYERS=WorldPlaces&BBOX=-81.366241839,42.39269586,-77.8780568047,44.13861927&SLD=http://www2.dmsolutions.ca/msapps/world_testdata/tests/sld_tests/sld_text_with_symbols.xml


- line layer with text using 2 symbolizers: `sld 10c`_ / `full request 10c`_

.. _`sld 10c`: http://www2.dmsolutions.ca/msapps/world_testdata/tests/sld_tests/sld_text_line.xml
.. _`full request 10c`: http://www2.dmsolutions.ca/cgi-bin/mswms_world?SERVICE=WMS&VeRsIoN=1.1.1&Request=GetMap&LAYERS=WorldRoads&BBOX=-81.366241839,42.39269586,-77.8780568047,44.13861927&SLD=http://www2.dmsolutions.ca/msapps/world_testdata/tests/sld_tests/sld_text_line.xml

**Table 11. RasterSymbolizer**

=================== ========= =====
Features            Supported Notes
=================== ========= =====
Geometry            No   
Opacity             Yes  
ChannelSelection    No   
OverlapBehaviour    No   
ColorMap            Yes  
ContrastEnhancement No   
ShadedRelief        No   
ImageOutline        No  
=================== ========= =====

The current support in MapServer includes only ColorMap parameter support. It 
can be used to classify 8-bit rasters. Inside the ColorMap parameters, the 
color and quantity parameters are extracted and used to do the classification. 

**Table 12. ColorMap**

======== ========= =====
Features Supported Notes
======== ========= =====
Color    Yes  
Opacity  No   
Quantity Yes  
Label    No 
======== ========= =====

The following is an example of ColorMap usage.

If we have following ColorMap in an SLD:

::

    <ColorMap>
      <ColorMapEntry color="#00ff00" quantity="22"/> 
      <ColorMapEntry color="#00bf3f" quantity="30"/> 
      <ColorMapEntry color="#007f7f" quantity="37"/> 
      <ColorMapEntry color="#003fbf" quantity="45"/> 
      <ColorMapEntry color="#0000ff" quantity="52"/>
      <ColorMapEntry color="#000000" quantity="60"/>
    </ColorMap>
          
The six classes that are created are:

::

    class 1: [pixel] >= 22 AND [pixel] < 30 with color 00ff00
    class 2: [pixel] >= 30 AND [pixel] < 37 with color 00bf3f 
    class 3: [pixel] >= 37 AND [pixel] < 45 with color 007f7f
    class 4: [pixel] >= 45 AND [pixel] < 52 with color 003fbf
    class 5: [pixel] >= 52 AND [pixel] < 60 with color 0000ff
    class 6: [pixel] = 60 with color 000000 

Note that the ColorMapEntry quantity parameters should be in increasing order.

Examples using 8 bits and 16 bits rasters can be seen at:

- http://www2.dmsolutions.ca/cgi-bin/mswms_landsat?SERVICE=WMS&VeRsIoN=1.1.1&Request=GetMap&LAYERS=landsat&BBOX=302100,5029281,530271,5166822&SLD=http://www2.dmsolutions.ca/msapps/world_testdata/tests/sld_tests/sld_raster.xml

- http://www2.dmsolutions.ca/cgi-bin/mswms_landsat2?SERVICE=WMS&VeRsIoN=1.1.1&Request=GetMap&LAYERS=golden_CO&SLD=http://www2.dmsolutions.ca/msapps/world_testdata/tests/sld_tests/sld_raster_16bits.xml

Client Side Support
===================

Client side support of the SLD consists of two parts:

- The first part is using MapServer as a WMS client to send a GetMap request 
  with an SLD. This is done using two metadata that can be placed at a layer 
  level in a MapServer mapfile. These two metadata are:

  - ``wms_sld_url``, which takes a valid URL as a value and appends SLD=xxx to the 
    GetMap request.

  - ``wms_sld_body``, which takes a valid SLD string and appends SLD_BODY=xxx to 
    the GetMap request. If the value of wms_sld_body is set to AUTO, MapServer 
    generates an SLD based on the classes found in the layer and send this SLD 
    as the value of the SLD_BODY parameter in the GetMap request. 

- The other major item is the generation of an SLD document from MapServer 
  classes. These functions are currently available through MapServer/MapScript 
  interface. Here are the functions available:
  
  - on a map object: ``generatesld``

  - on a layer object: ``generatesld``

  Additional MapScript functions have been added or will be added to complement these functions:

  - on a map object: ``applysld``
 
  - on a layer object: ``applysld`` 

*Note*: When generating an SLD from MapServer classes, if there is a pixmap symbol 
you need to have this symbol available through a URL so it can be converted as an 
ExternalGraphic symbol in the SLD. To do this, you need to define the URL through 
a web object level metadata called WMS_SLD_SYMBOL_URL in your map file. The SLD 
generated uses this URL and concatenates the name of the pixmap symbol file to get 
the value that is generated as the ExternaGraphic URL. 

Other Items Implemented
=======================

- Support of filled polygons with Mark and ExternalGraphic symbols.

- MapScript functions to parse and apply SLD.

- SLD_BODY request support on client and server side. 

Issues Found During Implementation
==================================

- Limitation of the FilterEncoding to comparison and logical filters. The 
  spatial filters were not made available since it required major changes in 
  MapServer WMS support. 

About This Document
===================

Copyright Information
---------------------

Copyright (c) 2005, Yewondwossen Assefa, Jeff McKenna.
                
This documentation is covered by the same Open Source license as the MapServer 
software itself.  See MapServer's `License and Credits`__ page for the complete 
text.
            
__ http://mapserver.gis.umn.edu/license.html   

Disclaimer
----------

No liability for the contents of this document can be accepted.
Use the concepts, examples and other content at your own risk.
As this is a new edition of this document, there may be errors
and inaccuracies that may be damaging to your system.
Although this is highly unlikely, the author(s) do not take any 
responsibility for that:  proceed with caution.

