/**********************************************************************
 * $Id$
 *
 * Project:  MapServer
 * Purpose:  OGC SLD implementation
 * Author:   Y. Assefa, DM Solutions Group (assefa@dmsolutions.ca)
 *
 **********************************************************************
 * Copyright (c) 2003, Y. Assefa, DM Solutions Group Inc
 *
 * Permission is hereby granted, free of charge, to any person obtaining a
 * copy of this software and associated documentation files (the "Software"),
 * to deal in the Software without restriction, including without limitation
 * the rights to use, copy, modify, merge, publish, distribute, sublicense,
 * and/or sell copies of the Software, and to permit persons to whom the
 * Software is furnished to do so, subject to the following conditions:
 * 
 * The above copyright notice and this permission notice shall be included in 
 * all copies of this Software or works derived from this Software.
 * 
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.  IN NO EVENT SHALL
 * THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER 
 ****************************************************************************/

#include "mapserver.h"

MS_DLL_EXPORT char *msSLDGenerateSLD(mapObj *map, int iLayer);
MS_DLL_EXPORT int msSLDApplySLDURL(mapObj *map, char *szURL, int iLayer,
                                   char *pszStyleLayerName);
MS_DLL_EXPORT int msSLDApplySLD(mapObj *map, char *psSLDXML, int iLayer, 
                                char *pszStyleLayerName);

#ifdef USE_OGR

/* There is a dependency to OGR for the MiniXML parser */
#include "cpl_minixml.h"


/* -------------------------------------------------------------------- */
/*      prototypes.                                                     */
/* -------------------------------------------------------------------- */
layerObj  *msSLDParseSLD(mapObj *map, char *psSLDXML, int *pnLayers);
void msSLDParseNamedLayer(CPLXMLNode *psRoot, layerObj *layer);
void msSLDParseRule(CPLXMLNode *psRoot, layerObj *psLayer);
void msSLDParseStroke(CPLXMLNode *psStroke, styleObj *psStyle,
                      mapObj *map, int iColorParam);
void msSLDParsePolygonFill(CPLXMLNode *psFill, styleObj *psStyle,
                           mapObj *map);

void msSLDParseLineSymbolizer(CPLXMLNode *psRoot, layerObj *psLayer,  
                              int bNewClass);
void msSLDParsePolygonSymbolizer(CPLXMLNode *psRoot, layerObj *psLayer,
                                  int bNewClass);
void msSLDParsePointSymbolizer(CPLXMLNode *psRoot, layerObj *psLayer, 
                               int bNewClass);
void msSLDParseTextSymbolizer(CPLXMLNode *psRoot, layerObj *psLayer,
                              int bOtherSymboliser);
void msSLDParseRasterSymbolizer(CPLXMLNode *psRoot, layerObj *psLayer);

void msSLDParseGraphicFillOrStroke(CPLXMLNode *psGraphicFill,
                                   char *pszDashValue,
                                   styleObj *psStyle, mapObj *map, int bPointLayer);
void msSLDParseExternalGraphic(CPLXMLNode *psExternalGraphic, styleObj *psStyle, 
                              mapObj *map);

int msSLDGetLineSymbol(mapObj *map);
int msSLDGetDashLineSymbol(mapObj *map, char *pszDashArray);
int msSLDGetMarkSymbol(mapObj *map, char *pszSymbolName, int bFilled,
                       char *pszDashValue);
int msSLDGetGraphicSymbol(mapObj *map, char *pszFileName, char *extGraphicName, int nGap);

void msSLDSetColorObject(char *psHexColor, colorObj *psColor);

void msSLDParseTextParams(CPLXMLNode *psRoot, layerObj *psLayer, classObj *psClass);
void ParseTextPointPlacement(CPLXMLNode *psRoot, classObj *psClass);
void ParseTextLinePlacement(CPLXMLNode *psRoot, classObj *psClass);

char *msSLDGenerateSLDLayer(layerObj *psLayer);

char *msSLDGetFilter(classObj *psClass, const char *pszWfsFilter);
char *msSLDGenerateLineSLD(styleObj *psStyle, layerObj *psLayer);
char *msSLDGeneratePolygonSLD(styleObj *psStyle, layerObj *psLayer);
char *msSLDGeneratePointSLD(styleObj *psStyle, layerObj *psLayer);
char *msSLDGenerateTextSLD(classObj *psClass, layerObj *psLayer);


#endif
