/******************************************************************************
 * $Id$
 *
 * Project:  MapServer
 * Purpose:  Interface file for MapServer PHP scripting extension 
 *           called MapScript. This file was originally based on 
 *           the SWIG interface file mapscript.i
 * Author:   Daniel Morissette, DM Solutions Group (dmorissette@dmsolutions.ca)
 *
 **********************************************************************
 * Copyright (c) 2000, 2007, Daniel Morissette, DM Solutions Group Inc.
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
 * DEALINGS IN THE SOFTWARE.
 **********************************************************************/ 

#include "php_mapscript.h"

/* grab mapserver declarations to wrap
 */
#include "../../mapserver.h"
#include "../../maperror.h"
#include "../../mapprimitive.h"
#include "../../mapsymbol.h"
#include "../../mapshape.h"
#include "../../mapproject.h"

/**********************************************************************
 * class extensions for mapObj
 **********************************************************************/
mapObj *mapObj_new(char *filename, char *new_path) {
    if(filename && strlen(filename))
      return msLoadMap(filename, new_path);
    else { /* create an empty map, no layers etc... */
      return msNewMapObj();
    } 
}

void  mapObj_destroy(mapObj* self) {
    msFreeMap(self);
  }

mapObj *mapObj_clone(mapObj* self) {
    mapObj *dstMap;
    dstMap = msNewMapObj();
    if (msCopyMap(dstMap, self) != MS_SUCCESS)
    {
        msFreeMap(dstMap);
        dstMap = NULL;
    }
    return dstMap;
  }

int mapObj_setRotation(mapObj* self, double rotation_angle ) {
        return msMapSetRotation( self, rotation_angle );
    }

layerObj *mapObj_getLayer(mapObj* self, int i) {
    if(i >= 0 && i < self->numlayers)	
      return (self->layers[i]); /* returns an EXISTING layer */
    else
      return NULL;
  }

layerObj *mapObj_getLayerByName(mapObj* self, char *name) {
    int i;

    i = msGetLayerIndex(self, name);

    if(i != -1)
      return (self->layers[i]); /* returns an EXISTING layer */
    else
      return NULL;
  }

int *mapObj_getLayersIndexByGroup(mapObj* self, char *groupname, 
                                 int *pnCount) {
    return msGetLayersIndexByGroup(self, groupname, pnCount);
}


int mapObj_getSymbolByName(mapObj* self, char *name) {
    return msGetSymbolIndex(&self->symbolset, name, MS_TRUE);
  }

void mapObj_prepareQuery(mapObj* self) {
    int status;

    status = msCalculateScale(self->extent, self->units, self->width, self->height, self->resolution, &self->scaledenom);
    if(status != MS_SUCCESS) self->scaledenom = -1; // degenerate extents ok here
  }

imageObj *mapObj_prepareImage(mapObj* self) {
    return msPrepareImage(self, MS_FALSE);
  }

imageObj *mapObj_draw(mapObj* self) {
    return msDrawMap(self, MS_FALSE);
  }

imageObj *mapObj_drawQuery(mapObj* self) {
    return msDrawMap(self, MS_TRUE);
  }

imageObj *mapObj_drawLegend(mapObj* self) {
    return msDrawLegend(self, MS_FALSE);
  }


imageObj *mapObj_drawScalebar(mapObj* self) {
    return msDrawScalebar(self);
  }

imageObj *mapObj_drawReferenceMap(mapObj* self) {
    return msDrawReferenceMap(self);
  }

//TODO
int mapObj_embedScalebar(mapObj* self, imageObj *img) {	
    return msEmbedScalebar(self, img);
  }

//TODO
int mapObj_embedLegend(mapObj* self, imageObj *img) {	
    return msEmbedLegend(self, img);
  }

int mapObj_drawLabelCache(mapObj* self, imageObj *img) {
    return msDrawLabelCache(img, self);
  }

int mapObj_queryByPoint(mapObj* self, pointObj *point, 
                         int mode, double buffer) {
    return msQueryByPoint(self, -1, mode, *point, buffer, 0);
  }

int mapObj_queryByRect(mapObj* self, rectObj rect) {
    return msQueryByRect(self, -1, rect);
  }

int mapObj_queryByFeatures(mapObj* self, int slayer) {
    return msQueryByFeatures(self, -1, slayer);
  }

int mapObj_queryByShape(mapObj *self, shapeObj *shape) {
    return msQueryByShape(self, -1, shape);
  }

int mapObj_queryByIndex(mapObj *self, int qlayer, int tileindex, int shapeindex,
                        int bAddToQuery) {
    if (bAddToQuery)
      return msQueryByIndexAdd(self, qlayer, tileindex, shapeindex);
    else
      return msQueryByIndex(self, qlayer, tileindex, shapeindex);
}

int mapObj_saveQuery(mapObj *self, char *filename) {
  return msSaveQuery(self, filename);
}
int mapObj_loadQuery(mapObj *self, char *filename) {
  return msLoadQuery(self, filename);
}
void mapObj_freeQuery(mapObj *self, int qlayer) {
  msQueryFree(self, qlayer);
}

int mapObj_setWKTProjection(mapObj *self, char *string) {
    return msOGCWKT2ProjectionObj(string, &(self->projection), self->debug);
  }

char *mapObj_getProjection(mapObj* self) {
    return msGetProjectionString(&self->projection);
 }

int mapObj_setProjection(mapObj* self, char *string) {
    return(msLoadProjectionString(&(self->projection), string));
  }

int mapObj_save(mapObj* self, char *filename) {
    return msSaveMap(self, filename);
  }

char *mapObj_getMetaData(mapObj *self, char *name) {
    return(msLookupHashTable(&(self->web.metadata), name));
  }

int mapObj_setMetaData(mapObj *self, char *name, char *value) {
    if (msInsertHashTable(&(self->web.metadata), name, value) == NULL)
	return MS_FAILURE;
    return MS_SUCCESS;
  }

int mapObj_removeMetaData(mapObj *self, char *name) {
    return(msRemoveHashTable(&(self->web.metadata), name));
}

int mapObj_moveLayerup(mapObj *self, int layerindex){
    return msMoveLayerUp(self, layerindex);
}

int mapObj_moveLayerdown(mapObj *self, int layerindex){
    return msMoveLayerDown(self, layerindex);
}

int *mapObj_getLayersdrawingOrder(mapObj *self){
    return self->layerorder;
}
 
int mapObj_setLayersdrawingOrder(mapObj *self, int *panIndexes){
    return msSetLayersdrawingOrder(self, panIndexes);
}

char *mapObj_processTemplate(mapObj *self, int bGenerateImages, 
                             char **names, char **values, 
                             int numentries)
{
    return msProcessTemplate(self, bGenerateImages,
                             names, values, numentries);
}
  
char *mapObj_processLegendTemplate(mapObj *self,
                                   char **names, char **values, 
                                   int numentries)
{
    return msProcessLegendTemplate(self, names, values, numentries);
}
  

char *mapObj_processQueryTemplate(mapObj *self, int bGenerateImages,
                                   char **names, char **values, 
                                   int numentries)
{
    return msProcessQueryTemplate(self, bGenerateImages, names, values, 
                                  numentries);
}

int mapObj_setSymbolSet(mapObj *self,
                        char *szFileName)
{
    msFreeSymbolSet(&self->symbolset);
    msInitSymbolSet(&self->symbolset);
   
    // Set symbolset filename
    self->symbolset.filename = strdup(szFileName);

    // Symbolset shares same fontset as main mapfile
    self->symbolset.fontset = &(self->fontset);

    return msLoadSymbolSet(&self->symbolset, self);
}

int mapObj_getNumSymbols(mapObj *self)
{
    return self->symbolset.numsymbols;
}

int mapObj_setFontSet(mapObj *self, char *szFileName)
{
    msFreeFontSet(&(self->fontset));
    msInitFontSet(&(self->fontset));
   
    // Set fontset filename
    self->fontset.filename = strdup(szFileName);

    return msLoadFontSet(&(self->fontset), self);
}

int mapObj_saveMapContext(mapObj *self, char *szFilename)
{
    return msSaveMapContext(self, szFilename);
}

int mapObj_loadMapContext(mapObj *self, char *szFilename, int bUniqueLayerName)
{
    return msLoadMapContext(self, szFilename, bUniqueLayerName);
}



int mapObj_selectOutputFormat(mapObj *self,
                              const char *imagetype)
{
    outputFormatObj *format = NULL;
    
    format = msSelectOutputFormat(self, imagetype);
    if (format)
    {
        msApplyOutputFormat( &(self->outputformat), format, 
                             self->transparent, self->interlace, 
                             self->imagequality );
        return(MS_SUCCESS);
    }
    return(MS_FAILURE);
    
}

int mapObj_applySLD(mapObj *self, char *sld)
{
    return msSLDApplySLD(self, sld, -1, NULL);
}
int mapObj_applySLDURL(mapObj *self, char *sld)
{
    return msSLDApplySLDURL(self, sld, -1, NULL);
}

char *mapObj_generateSLD(mapObj *self)
{
    return msSLDGenerateSLD(self, -1);
}


int mapObj_loadOWSParameters(mapObj *self, cgiRequestObj *request, 
                              char *wmtver_string)
{
    return msMapLoadOWSParameters(self, request, wmtver_string);
}

int mapObj_OWSDispatch(mapObj *self, cgiRequestObj *req )
{
    return msOWSDispatch( self, req, MS_TRUE);
}

int mapObj_insertLayer(mapObj *self, layerObj *layer, int index)
{
    if (self && layer)
      return msInsertLayer(self, layer, index);

    return -1;
}

/**********************************************************************
 * class extensions for layerObj, always within the context of a map
 **********************************************************************/
layerObj *layerObj_new(mapObj *map) {
    if(msGrowMapLayers(map) == NULL)
      return(NULL);

    if(initLayer((map->layers[map->numlayers]), map) == -1)
      return(NULL);

    map->layers[map->numlayers]->index = map->numlayers;
    //Update the layer order list with the layer's index.
    map->layerorder[map->numlayers] = map->numlayers;

    map->numlayers++;

    return (map->layers[map->numlayers-1]);
  }

void layerObj_destroy(layerObj *self) {
    return; // map deconstructor takes care of it
  }

int layerObj_open(layerObj *self) {
    return msLayerOpen(self);
  }


int layerObj_whichShapes(layerObj *self, rectObj *poRect) {
  msLayerGetItems(self);
  return msLayerWhichShapes(self, *poRect);
}


shapeObj *layerObj_nextShape(layerObj *self) {
  int status;
  shapeObj *shape;

  shape = (shapeObj *)malloc(sizeof(shapeObj));
  if (!shape) return NULL;
  msInitShape(shape);

  status = msLayerNextShape(self, shape);
  if(status != MS_SUCCESS) {
    msFreeShape(shape);
    free(shape);
    return NULL;
  } else
    return shape;
}

void layerObj_close(layerObj *self) {
    msLayerClose(self);
  }

int layerObj_getShape(layerObj *self, shapeObj *shape, 
                      int tileindex, int shapeindex) {
    return msLayerGetShape(self, shape, tileindex, shapeindex);
  }

resultCacheMemberObj *layerObj_getResult(layerObj *self, int i) {
    if(!self->resultcache) return NULL;

    if(i >= 0 && i < self->resultcache->numresults)
      return &self->resultcache->results[i]; 
    else
      return NULL;
  }

classObj *layerObj_getClass(layerObj *self, int i) { // returns an EXISTING class
    if(i >= 0 && i < self->numclasses)
      return (self->class[i]); 
    else
      return(NULL);
  }

int layerObj_draw(layerObj *self, mapObj *map, imageObj *img) {
    return msDrawLayer(map, self, img);
  }

int layerObj_drawQuery(layerObj *self, mapObj *map, imageObj *img) {
    return msDrawQueryLayer(map, self, img);    
  }

int layerObj_queryByAttributes(layerObj *self, mapObj *map, char *qitem, char *qstring, int mode) {
    int status;
    int retval;
        
    status = self->status;
    self->status = MS_ON;
    retval = msQueryByAttributes(map, self->index, qitem, qstring, mode);
    self->status = status;

    return retval;
  }

int layerObj_queryByPoint(layerObj *self, mapObj *map, 
                          pointObj *point, int mode, double buffer) {
    int status;
    int retval;
        
    status = self->status;
    self->status = MS_ON;
    retval = msQueryByPoint(map, self->index, mode, *point, buffer, 0);
    self->status = status;

    return retval;
  }

int layerObj_queryByRect(layerObj *self, mapObj *map, rectObj rect) {
    int status;
    int retval;
        
    status = self->status;
    self->status = MS_ON;
    retval = msQueryByRect(map, self->index, rect);
    self->status = status;

    return retval;
  }

int layerObj_queryByFeatures(layerObj *self, mapObj *map, int slayer) {
    int status;
    int retval;
        
    status = self->status;
    self->status = MS_ON;
    retval = msQueryByFeatures(map, self->index, slayer);
    self->status = status;

    return retval;
  }

int layerObj_queryByShape(layerObj *self, mapObj *map, shapeObj *shape) {
    int status;
    int retval;
        
    status = self->status;
    self->status = MS_ON;
    retval = msQueryByShape(map, self->index, shape);
    self->status = status;

    return retval;
  }

int layerObj_setFilter(layerObj *self, char *string) {
    if (!string || strlen(string) == 0) {
        freeExpression(&self->filter);
        return MS_SUCCESS;
    }
    else return msLoadExpressionString(&self->filter, string);
  }

char *layerObj_getFilter(layerObj *self) {
    return msGetExpressionString(&(self->filter));
  }

int layerObj_setWKTProjection(layerObj *self, char *string) {
    self->project = MS_TRUE;
    return msOGCWKT2ProjectionObj(string, &(self->projection), self->debug);
  }

char *layerObj_getProjection(layerObj* self) {
    return msGetProjectionString(&self->projection);
 }

int layerObj_setProjection(layerObj *self, char *string) {
  int nReturn;
  nReturn = msLoadProjectionString(&(self->projection), string);
  if (nReturn == 0)
    self->project = MS_TRUE;
  return nReturn;

  }

int layerObj_addFeature(layerObj *self, shapeObj *shape) {
    if(insertFeatureList(&(self->features), shape) == NULL) 
      return -1;
    else
      return 0;
  }

char *layerObj_getMetaData(layerObj *self, char *name) {
    return(msLookupHashTable(&(self->metadata), name));
  }


int layerObj_setMetaData(layerObj *self, char *name, char *value) {
    if (msInsertHashTable(&(self->metadata), name, value) == NULL)
	return MS_FAILURE;
    return MS_SUCCESS;
  }

int layerObj_removeMetaData(layerObj *self, char *name) {
    return(msRemoveHashTable(&(self->metadata), name));
  }

char *layerObj_getWMSFeatureInfoURL(layerObj *self, mapObj *map, int click_x, int click_y,     
                                    int feature_count, char *info_format) {
    // NOTE: the returned string should be freed by the caller but right 
    // now we're leaking it.
    return(msWMSGetFeatureInfoURL(map, self, click_x, click_y,
                                  feature_count, info_format));
  }

char *layerObj_executeWFSGetFeature(layerObj *self) {
  return (msWFSExecuteGetFeature(self));
}

int layerObj_applySLD(layerObj *self, char *sld, char *stylelayer)
{
    return msSLDApplySLD(self->map, sld, self->index, stylelayer);
}
int layerObj_applySLDURL(layerObj *self, char *sld, char *stylelayer)
{
    return msSLDApplySLDURL(self->map, sld, self->index, stylelayer);
}

char *layerObj_generateSLD(layerObj *self)
{
    return msSLDGenerateSLD(self->map, self->index);
}

int layerObj_moveClassUp(layerObj *self, int index)
{
    return msMoveClassUp(self, index);
}

int layerObj_moveClassDown(layerObj *self, int index)
{
    return msMoveClassDown(self, index);
}

classObj *layerObj_removeClass(layerObj *self, int index)
{
    return msRemoveClass(self, index);
}

int layerObj_setConnectionType(layerObj *self, int connectiontype, 
                               const char *library_str) 
{
    /* Caller is responsible to close previous layer correctly before calling
     * msConnectLayer() 
     */
    if (msLayerIsOpen(self))
        msLayerClose(self);

    return msConnectLayer(self, connectiontype, library_str);
}

/**********************************************************************
 * class extensions for classObj, always within the context of a layer
 **********************************************************************/
classObj *classObj_new(layerObj *layer, classObj *class) {
    if(msGrowLayerClasses(layer) == NULL)
      return NULL;

    if(initClass((layer->class[layer->numclasses])) == -1)
      return NULL;

    if (class){
      msCopyClass((layer->class[layer->numclasses]), class, layer);
      layer->class[layer->numclasses]->layer = layer;
    }

    layer->class[layer->numclasses]->type = layer->type;

    layer->numclasses++;

    return (layer->class[layer->numclasses-1]);
  }

void  classObj_destroy(classObj *self) {
    return; /* do nothing, map deconstrutor takes care of it all */
  }

int classObj_setExpression(classObj *self, char *string) {
    if (!string || strlen(string) == 0) {
        freeExpression(&self->expression);
        return MS_SUCCESS;
    }
    else return msLoadExpressionString(&self->expression, string);
  }

char *classObj_getExpressionString(classObj *self) {
    return msGetExpressionString(&(self->expression));
}

int classObj_setText(classObj *self, layerObj *layer, char *string) {
    return msLoadExpressionString(&self->text, string);
}

char *classObj_getTextString(classObj *self) {
    return msGetExpressionString(&(self->text));
}

int classObj_drawLegendIcon(classObj *self, mapObj *map, layerObj *layer, int width, int height, imageObj *dstImg, int dstX, int dstY) {
  msClearLayerPenValues(layer); // just in case the mapfile has already been processed
    return msDrawLegendIcon(map, layer, self, width, height, dstImg, dstX, dstY);
}

imageObj *classObj_createLegendIcon(classObj *self, mapObj *map, layerObj *layer, int width, int height) {
    return msCreateLegendIcon(map, layer, self, width, height);
  }


int classObj_setSymbolByName(classObj *self, mapObj *map, char* pszSymbolName) {
  /*
   self->symbol = msGetSymbolIndex(&map->symbolset, pszSymbolName, MS_TRUE);
    return self->symbol;
  */
  return -1;
}
  
int classObj_setOverlaySymbolByName(classObj *self, mapObj *map, char* pszOverlaySymbolName) {
  /*
    self->overlaysymbol = msGetSymbolIndex(&map->symbolset, pszOverlaySymbolName, MS_TRUE);
    return self->overlaysymbol;
  */
  return -1;

  }

classObj *classObj_clone(classObj *class, layerObj *layer)
{
    classObj *dstClass;
    dstClass = (classObj *)malloc(sizeof(classObj));
    
    initClass(dstClass);
    msCopyClass(dstClass, class, layer);

    dstClass->type = layer->type;

    return dstClass;
}

int classObj_moveStyleUp(classObj *self, int index)
{
    return msMoveStyleUp(self, index);
}

int classObj_moveStyleDown(classObj *self, int index)
{
    return msMoveStyleDown(self, index);
}

int classObj_deleteStyle(classObj *self, int index)
{
    return msDeleteStyle(self, index);
}

/**********************************************************************
 * class extensions for pointObj, useful many places
 **********************************************************************/
pointObj *pointObj_new() {
    return (pointObj *)malloc(sizeof(pointObj));
  }

void pointObj_destroy(pointObj *self) {
    free(self);
  }

int pointObj_project(pointObj *self, projectionObj *in, projectionObj *out) {
    return msProjectPoint(in, out, self);
  }	

int pointObj_draw(pointObj *self, mapObj *map, layerObj *layer, 
                  imageObj *img, int class_index, char *label_string) {
    return msDrawPoint(map, layer, self, img, class_index, label_string);
  }

double pointObj_distanceToPoint(pointObj *self, pointObj *point) {
    return msDistancePointToPoint(self, point);
  }

double pointObj_distanceToLine(pointObj *self, pointObj *a, pointObj *b) {
    return msDistancePointToSegment(self, a, b);
  }

double pointObj_distanceToShape(pointObj *self, shapeObj *shape) {
   return msDistancePointToShape(self, shape);
  }

/**********************************************************************
 * class extensions for lineObj (eg. a line or group of points), 
 * useful many places
 **********************************************************************/
lineObj *lineObj_new() {
    lineObj *line;

    line = (lineObj *)malloc(sizeof(lineObj));
    if(!line)
      return(NULL);

    line->numpoints=0;
    line->point=NULL;

    return line;
  }

void lineObj_destroy(lineObj *self) {
    free(self->point);
    free(self);		
  }

int lineObj_project(lineObj *self, projectionObj *in, projectionObj *out) {
    return msProjectLine(in, out, self);
  }

pointObj *lineObj_get(lineObj *self, int i) {
    if(i<0 || i>=self->numpoints)
      return NULL;
    else
      return &(self->point[i]);
  }

int lineObj_add(lineObj *self, pointObj *p) {
    if(self->numpoints == 0) { /* new */	
      self->point = (pointObj *)malloc(sizeof(pointObj));      
      if(!self->point)
	return -1;
    } else { /* extend array */
      self->point = (pointObj *)realloc(self->point, sizeof(pointObj)*(self->numpoints+1));
      if(!self->point)
	return -1;
    }

    self->point[self->numpoints].x = p->x;
    self->point[self->numpoints].y = p->y;
#ifdef USE_POINT_Z_M
    self->point[self->numpoints].m = p->m;
#endif
    self->numpoints++;

    return 0;
  }


/**********************************************************************
 * class extensions for shapeObj
 **********************************************************************/
shapeObj *shapeObj_new(int type) {
    shapeObj *shape;

    shape = (shapeObj *)malloc(sizeof(shapeObj));
    if(!shape)
      return NULL;

    msInitShape(shape);
    shape->type = type;
    return shape;
  }

void shapeObj_destroy(shapeObj *self) {
    msFreeShape(self);
    free(self);		
  }

int shapeObj_project(shapeObj *self, projectionObj *in, projectionObj *out) {
    return msProjectShape(in, out, self);
  }

lineObj *shapeObj_get(shapeObj *self, int i) {
    if(i<0 || i>=self->numlines)
      return NULL;
    else
      return &(self->line[i]);
  }

int shapeObj_add(shapeObj *self, lineObj *line) {
    return msAddLine(self, line);
  }

int shapeObj_draw(shapeObj *self, mapObj *map, layerObj *layer, 
                  imageObj *img) {
    return msDrawShape(map, layer, self, img, -1);
  }

void shapeObj_setBounds(shapeObj *self) {
    int i, j;

    self->bounds.minx = self->bounds.maxx = self->line[0].point[0].x;
    self->bounds.miny = self->bounds.maxy = self->line[0].point[0].y;
    
    for( i=0; i<self->numlines; i++ ) {
      for( j=0; j<self->line[i].numpoints; j++ ) {
	self->bounds.minx = MS_MIN(self->bounds.minx, self->line[i].point[j].x);
	self->bounds.maxx = MS_MAX(self->bounds.maxx, self->line[i].point[j].x);
	self->bounds.miny = MS_MIN(self->bounds.miny, self->line[i].point[j].y);
	self->bounds.maxy = MS_MAX(self->bounds.maxy, self->line[i].point[j].y);
      }
    }

    return;
  }

int shapeObj_copy(shapeObj *self, shapeObj *dest) {
    return(msCopyShape(self, dest));
  }

int shapeObj_contains(shapeObj *self, pointObj *point) {
    if(self->type == MS_SHAPE_POLYGON)
      return msIntersectPointPolygon(point, self);

    return -1;
  }

int shapeObj_intersects(shapeObj *self, shapeObj *shape) {
    switch(self->type) {
    case(MS_SHAPE_LINE):
      switch(shape->type) {
      case(MS_SHAPE_LINE):
	return msIntersectPolylines(self, shape);
      case(MS_SHAPE_POLYGON):
	return msIntersectPolylinePolygon(self, shape);
      }
      break;
    case(MS_SHAPE_POLYGON):
      switch(shape->type) {
      case(MS_SHAPE_LINE):
	return msIntersectPolylinePolygon(shape, self);
      case(MS_SHAPE_POLYGON):
	return msIntersectPolygons(self, shape);
      }
      break;
    }

    return -1;
  }

pointObj *shapeObj_getpointusingmeasure(shapeObj *self, double m) 
{       
   if (self)
     return msGetPointUsingMeasure(self, m);
   
   return NULL;
}

pointObj *shapeObj_getmeasureusingpoint(shapeObj *self, pointObj *point) 
{       
   if (self)
     return msGetMeasureUsingPoint(self, point);
   
   return NULL;
}


shapeObj *shapeObj_buffer(shapeObj *self, double width)
{
    return msGEOSBuffer(self, width);
}

 
shapeObj *shapeObj_convexHull(shapeObj *self)
{
    return msGEOSConvexHull(self);
}

shapeObj *shapeObj_boundary(shapeObj *self)
{
    return msGEOSBoundary(self);
}

int shapeObj_contains_geos(shapeObj *self, shapeObj *shape)
{
    return msGEOSContains(self, shape);
}

shapeObj *shapeObj_Union(shapeObj *self, shapeObj *shape)
{
     return msGEOSUnion(self, shape);
}

shapeObj *shapeObj_intersection(shapeObj *self, shapeObj *shape)
{
     return msGEOSIntersection(self, shape);
}

shapeObj *shapeObj_difference(shapeObj *self, shapeObj *shape)
{
     return msGEOSDifference(self, shape);
}
 
shapeObj *shapeObj_symdifference(shapeObj *self, shapeObj *shape)
{
     return msGEOSSymDifference(self, shape);
}

int shapeObj_overlaps(shapeObj *self, shapeObj *shape)
{
    return msGEOSOverlaps(self, shape);
}
 
int shapeObj_within(shapeObj *self, shapeObj *shape)
{
    return msGEOSWithin(self, shape);
}

int shapeObj_crosses(shapeObj *self, shapeObj *shape)
{
    return msGEOSCrosses(self, shape);
}

int shapeObj_touches(shapeObj *self, shapeObj *shape)
{
    return msGEOSTouches(self, shape);
}
 
int shapeObj_equals(shapeObj *self, shapeObj *shape)
{
    return msGEOSEquals(self, shape);
}
 
int shapeObj_disjoint(shapeObj *self, shapeObj *shape)
{
    return msGEOSDisjoint(self, shape);
}
 

pointObj *shapeObj_getcentroid(shapeObj *self)
{
    return msGEOSGetCentroid(self);
}

double shapeObj_getarea(shapeObj *self)
{
    return msGEOSArea(self);
}

double shapeObj_getlength(shapeObj *self)
{
    return msGEOSLength(self);
}

pointObj *shapeObj_getLabelPoint(shapeObj *self)
{
    pointObj *point = (pointObj *)calloc(1, sizeof(pointObj));
    if (point == NULL) {
        msSetError(MS_MEMERR, "Failed to allocate memory for point", "getLabelPoint()");
        return NULL;
    }

    if(self->type == MS_SHAPE_POLYGON && msPolygonLabelPoint(self, point, -1) == MS_SUCCESS)
        return point;

    free(point);
    return NULL;
}


/**********************************************************************
 * class extensions for rectObj
 **********************************************************************/
rectObj *rectObj_new() {	
    rectObj *rect;

    rect = (rectObj *)calloc(1, sizeof(rectObj));
    if(!rect)
      return(NULL);
    
    rect->minx = -1;
    rect->miny = -1;
    rect->maxx = -1;
    rect->maxy = -1;
    
    return(rect);    	
  }

void rectObj_destroy(rectObj *self) {
    free(self);
  }

int rectObj_project(rectObj *self, projectionObj *in, projectionObj *out) {
    return msProjectRect(in, out, self);
  }

double rectObj_fit(rectObj *self, int width, int height) {
    return  msAdjustExtent(self, width, height);
  } 

int rectObj_draw(rectObj *self, mapObj *map, layerObj *layer,
                 imageObj *img, int classindex, char *text) {
    shapeObj shape;

    msInitShape(&shape);
    msRectToPolygon(*self, &shape);
    shape.classindex = classindex;
    shape.text = strdup(text);

    msDrawShape(map, layer, &shape, img, -1);

    msFreeShape(&shape);
    
    return 0;
  }

/**********************************************************************
 * class extensions for shapefileObj
 **********************************************************************/
shapefileObj *shapefileObj_new(char *filename, int type) {    
    shapefileObj *shapefile;
    int status;

    shapefile = (shapefileObj *)calloc(1,sizeof(shapefileObj));
    if(!shapefile)
      return NULL;

    if(type == -1)
      status = msShapefileOpen(shapefile, "rb", filename);
    else if (type == -2)
      status = msShapefileOpen(shapefile, "rb+", filename);
    else
      status = msShapefileCreate(shapefile, filename, type);

    if(status == -1) {
      msShapefileClose(shapefile);
      free(shapefile);
      return NULL;
    }
 
    return(shapefile);
  }

void shapefileObj_destroy(shapefileObj *self) {
    msShapefileClose(self);
    free(self);  
  }

int shapefileObj_get(shapefileObj *self, int i, shapeObj *shape) {
    if(i<0 || i>=self->numshapes)
      return -1;

    msFreeShape(shape); /* frees all lines and points before re-filling */
    msSHPReadShape(self->hSHP, i, shape);

    return 0;
  }

int shapefileObj_getPoint(shapefileObj *self, int i, pointObj *point) {
    if(i<0 || i>=self->numshapes)
      return -1;

    msSHPReadPoint(self->hSHP, i, point);
    return 0;
  }

int shapefileObj_getTransformed(shapefileObj *self, mapObj *map, 
                                int i, shapeObj *shape) {
    if(i<0 || i>=self->numshapes)
      return -1;

    msFreeShape(shape); /* frees all lines and points before re-filling */
    msSHPReadShape(self->hSHP, i, shape);
    msTransformShapeToPixel(shape, map->extent, map->cellsize);

    return 0;
  }

void shapefileObj_getExtent(shapefileObj *self, int i, rectObj *rect) {
    msSHPReadBounds(self->hSHP, i, rect);
  }

int shapefileObj_add(shapefileObj *self, shapeObj *shape) {
    return msSHPWriteShape(self->hSHP, shape);	
  }	

int shapefileObj_addPoint(shapefileObj *self, pointObj *point) {    
    return msSHPWritePoint(self->hSHP, point);	
  }

/**********************************************************************
 * class extensions for projectionObj
 **********************************************************************/
projectionObj *projectionObj_new(char *string) {	

    int status;
    projectionObj *proj=NULL;

    proj = (projectionObj *)malloc(sizeof(projectionObj));
    if(!proj) return NULL;
    msInitProjection(proj);

    status = msLoadProjectionString(proj, string);
    if(status == -1) {
      msFreeProjection(proj);
      free(proj);
      return NULL;
    }

    return proj;
  }


void projectionObj_destroy(projectionObj *self) {
    msFreeProjection(self);
    free(self);
  }

/**********************************************************************
 * class extensions for labelCacheObj - TP mods
 **********************************************************************/
void labelCacheObj_freeCache(labelCacheObj *self) {
  msFreeLabelCache(self);    
  
  }

/**********************************************************************
 * class extensions for DBFInfo - TP mods
 **********************************************************************/
char *DBFInfo_getFieldName(DBFInfo *self, int iField) {
        static char pszFieldName[1000];
	int pnWidth;
	int pnDecimals;
	msDBFGetFieldInfo(self, iField, &pszFieldName[0], &pnWidth, &pnDecimals);
	return pszFieldName;
    }

int DBFInfo_getFieldWidth(DBFInfo *self, int iField) {
        char pszFieldName[1000];
	int pnWidth;
	int pnDecimals;
	msDBFGetFieldInfo(self, iField, &pszFieldName[0], &pnWidth, &pnDecimals);
	return pnWidth;
    }

int DBFInfo_getFieldDecimals(DBFInfo *self, int iField) {
        char pszFieldName[1000];
	int pnWidth;
	int pnDecimals;
	msDBFGetFieldInfo(self, iField, &pszFieldName[0], &pnWidth, &pnDecimals);
	return pnDecimals;
    }
    
DBFFieldType DBFInfo_getFieldType(DBFInfo *self, int iField) {
	return msDBFGetFieldInfo(self, iField, NULL, NULL, NULL);
    }    

/**********************************************************************
 * class extensions for styleObj, always within the context of a class
 **********************************************************************/
styleObj *styleObj_new(classObj *class, styleObj *style) {
    if(msGrowClassStyles(class) == NULL)
      return NULL;

    if(initStyle(class->styles[class->numstyles]) == -1)
      return NULL;

    if (style)
      msCopyStyle(class->styles[class->numstyles], style);
        
    class->numstyles++;

    return class->styles[class->numstyles-1];
  }

void  styleObj_destroy(styleObj *self) {
    return; /* do nothing, map deconstrutor takes care of it all */
  }


int styleObj_setSymbolByName(styleObj *self, mapObj *map, char* pszSymbolName) {
    self->symbol = msGetSymbolIndex(&map->symbolset, pszSymbolName, MS_TRUE);
    return self->symbol;
}

styleObj *styleObj_clone(styleObj *style){
  styleObj *newstyle = NULL;
  if (!style)
    return NULL;

  newstyle = (styleObj *)malloc(sizeof(styleObj));
  initStyle(newstyle);

  msCopyStyle(newstyle, style);
  
  return newstyle;
}


cgiRequestObj *cgirequestObj_new()
{
    cgiRequestObj *request;
    request = msAllocCgiObj();

    request->ParamNames = (char **) malloc(MS_MAX_CGI_PARAMS*sizeof(char*));
    request->ParamValues = (char **) malloc(MS_MAX_CGI_PARAMS*sizeof(char*));

    return request;
}

int cgirequestObj_loadParams(cgiRequestObj *self)
{
  self->NumParams = loadParams(self);
  return self->NumParams;
}


void cgirequestObj_setParameter(cgiRequestObj *self, char *name, char *value)
{
    int i;
        
    if (self->NumParams == MS_MAX_CGI_PARAMS) {
      msSetError(MS_CHILDERR, "Maximum number of items, %d, has been reached", "setItem()", MS_MAX_CGI_PARAMS);
    }
        
    for (i=0; i<self->NumParams; i++) {
      if (strcasecmp(self->ParamNames[i], name) == 0) {
        free(self->ParamValues[i]);
                self->ParamValues[i] = strdup(value);
                break;
      }
    }
    if (i == self->NumParams) {
      self->ParamNames[self->NumParams] = strdup(name);
      self->ParamValues[self->NumParams] = strdup(value);
      self->NumParams++;
    }
}

char *cgirequestObj_getName(cgiRequestObj *self, int index)
{
    if (index < 0 || index >= self->NumParams) {
            msSetError(MS_CHILDERR, "Invalid index, valid range is [0, %d]", "getName()", self->NumParams-1);
            return NULL;
        }
        return self->ParamNames[index];
}

char *cgirequestObj_getValue(cgiRequestObj *self, int index) 
{
    if (index < 0 || index >= self->NumParams) {
            msSetError(MS_CHILDERR, "Invalid index, valid range is [0, %d]", "getValue()", self->NumParams-1);
            return NULL;
        }
        return self->ParamValues[index];
}
 
char *cgirequestObj_getValueByName(cgiRequestObj *self, const char *name) 
{
    int i;
    for (i=0; i<self->NumParams; i++) {
        if (strcasecmp(self->ParamNames[i], name) == 0) {
            return self->ParamValues[i];
        }
    }
    return NULL;
}
void cgirequestObj_destroy(cgiRequestObj *self)
{
    msFreeCharArray(self->ParamNames, self->NumParams);
    msFreeCharArray(self->ParamValues, self->NumParams);
    free(self);
}
