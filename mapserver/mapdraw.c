/******************************************************************************
 * $Id$
 *
 * Project:  MapServer
 * Purpose:  High level msDrawMap() implementation and related functions.
 * Author:   Steve Lime and the MapServer team.
 *
 ******************************************************************************
 * Copyright (c) 1996-2005 Regents of the University of Minnesota.
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
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS
 * OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL
 * THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
 * DEALINGS IN THE SOFTWARE.
 *****************************************************************************/

#include <assert.h>
#include "mapserver.h"
#include "maptime.h"
#include "mapcopy.h"

MS_CVSID("$Id$")

/*
 * Functions to reset any pen (color index) values previously set. Used primarily to reset things when
 * using MapScript to create multiple images. How the pen values are set is irrelevant (definitely output
 * format type specific) which is why this function is here instead of the GD, PDF or SWF source files.
*/
void msClearLayerPenValues(layerObj *layer) {
  int i, j;  

  for(i=0; i<layer->numclasses; i++) {
    layer->class[i]->label.backgroundcolor.pen = MS_PEN_UNSET; /* set in billboardXX function */
    layer->class[i]->label.backgroundshadowcolor.pen = MS_PEN_UNSET;
    layer->class[i]->label.color.pen = MS_PEN_UNSET; /* set in MSXXDrawText function */
    layer->class[i]->label.outlinecolor.pen = MS_PEN_UNSET;
    layer->class[i]->label.shadowcolor.pen = MS_PEN_UNSET;      

    for(j=0; j<layer->class[i]->numstyles; j++) {
      layer->class[i]->styles[j]->backgroundcolor.pen = MS_PEN_UNSET; /* set in various symbol drawing functions */
	  layer->class[i]->styles[j]->color.pen = MS_PEN_UNSET;
      layer->class[i]->styles[j]->outlinecolor.pen = MS_PEN_UNSET; 
    }
  }
}

void msClearScalebarPenValues(scalebarObj *scalebar)
{
    if (scalebar)
    {
       scalebar->color.pen = MS_PEN_UNSET;
       scalebar->backgroundcolor.pen = MS_PEN_UNSET;
       scalebar->outlinecolor.pen = MS_PEN_UNSET;
       scalebar->imagecolor.pen = MS_PEN_UNSET;

       scalebar->label.color.pen = MS_PEN_UNSET;
       scalebar->label.outlinecolor.pen = MS_PEN_UNSET;
       scalebar->label.shadowcolor.pen = MS_PEN_UNSET;
       scalebar->label.backgroundcolor.pen = MS_PEN_UNSET;
       scalebar->label.backgroundshadowcolor.pen = MS_PEN_UNSET;
    }
}

void msClearLegendPenValues(legendObj *legend)
{
    if (legend)
    {
       legend->outlinecolor.pen = MS_PEN_UNSET;
       legend->imagecolor.pen = MS_PEN_UNSET;

       legend->label.color.pen = MS_PEN_UNSET;
       legend->label.outlinecolor.pen = MS_PEN_UNSET;
       legend->label.shadowcolor.pen = MS_PEN_UNSET;
       legend->label.backgroundcolor.pen = MS_PEN_UNSET;
       legend->label.backgroundshadowcolor.pen = MS_PEN_UNSET;
    }
}

void msClearReferenceMapPenValues(referenceMapObj *referencemap)
{
    if (referencemap)
    {
        referencemap->outlinecolor.pen = MS_PEN_UNSET;
        referencemap->color.pen = MS_PEN_UNSET;
    }
}


void msClearQueryMapPenValues(queryMapObj *querymap)
{
    if (querymap)
      querymap->color.pen = MS_PEN_UNSET;
}


void msClearPenValues(mapObj *map) {
  int i;

  for(i=0; i<map->numlayers; i++)
    msClearLayerPenValues((GET_LAYER(map, i)));

  msClearLegendPenValues(&(map->legend));
  msClearScalebarPenValues(&(map->scalebar));
  msClearReferenceMapPenValues(&(map->reference));
  msClearQueryMapPenValues(&(map->querymap));
  
}

/* msPrepareImage()
 *
 * Returns a new imageObj ready for rendering the current map.
 *
 * If allow_nonsquare is set to MS_TRUE then the caller should call
 * msMapRestoreRealExtent() once they are done with the image.
 * This should be set to MS_TRUE only when called from msDrawMap(), see bug 945.
 */
imageObj *msPrepareImage(mapObj *map, int allow_nonsquare) 
{
    int i, status;
    imageObj *image=NULL;
    double geo_cellsize;

    if(map->width == -1 || map->height == -1) {
        msSetError(MS_MISCERR, "Image dimensions not specified.", "msPrepareImage()");
        return(NULL);
    }

    msInitLabelCache(&(map->labelcache)); /* this clears any previously allocated cache */

    status = msValidateContexts(map); /* make sure there are no recursive REQUIRES or LABELREQUIRES expressions */
    if(status != MS_SUCCESS) return NULL;

    if(!map->outputformat) {
        msSetError(MS_GDERR, "Map outputformat not set!", "msPrepareImage()");
        return(NULL);
    }
    else if( MS_RENDERER_GD(map->outputformat) )
    {
        image = msImageCreateGD(map->width, map->height, map->outputformat, 
				map->web.imagepath, map->web.imageurl);        
        if( image != NULL ) msImageInitGD( image, &map->imagecolor );
        msPreAllocateColorsGD(image, map);
    }
#ifdef USE_AGG
    else if( MS_RENDERER_AGG(map->outputformat) )
    {
        image = msImageCreateAGG(map->width, map->height, map->outputformat, 
				map->web.imagepath, map->web.imageurl);        
        if( image != NULL ) msImageInitAGG( image, &map->imagecolor );
    }
#endif
    else if( MS_RENDERER_IMAGEMAP(map->outputformat) )
    {
        image = msImageCreateIM(map->width, map->height, map->outputformat, 
				map->web.imagepath, map->web.imageurl);        
        if( image != NULL ) msImageInitIM( image );
    }
    else if( MS_RENDERER_RAWDATA(map->outputformat) )
    {
        image = msImageCreate(map->width, map->height, map->outputformat,
                              map->web.imagepath, map->web.imageurl, map);
    }
#ifdef USE_MING_FLASH
    else if( MS_RENDERER_SWF(map->outputformat) )
    {
        image = msImageCreateSWF(map->width, map->height, map->outputformat,
                                 map->web.imagepath, map->web.imageurl,
                                 map);
    }
#endif
#ifdef USE_PDF
    else if( MS_RENDERER_PDF(map->outputformat) )
    {
        image = msImageCreatePDF(map->width, map->height, map->outputformat,
                                 map->web.imagepath, map->web.imageurl,
                                 map);
	}
#endif
    else if( MS_RENDERER_SVG(map->outputformat) )
    {
        image = msImageCreateSVG(map->width, map->height, map->outputformat,
                                 map->web.imagepath, map->web.imageurl,
                                 map);
    }
    else
    {
        image = NULL;
    }
  
    if(!image) {
        msSetError(MS_GDERR, "Unable to initialize image.", "msPrepareImage()");
        return(NULL);
    }

    /*
     * If we want to support nonsquare pixels, note that now, otherwise
     * adjust the extent size to have square pixels.
     *
     * If allow_nonsquare is set to MS_TRUE then the caller should call
     * msMapRestoreRealExtent() once they are done with the image.
     * This should be set to MS_TRUE only when called from msDrawMap(), see bug 945.
     */
    if( allow_nonsquare && msTestConfigOption( map, "MS_NONSQUARE", MS_FALSE ) )
    {
        double cellsize_x = (map->extent.maxx - map->extent.minx)/map->width;
        double cellsize_y = (map->extent.maxy - map->extent.miny)/map->height;

        if( cellsize_y != 0.0 
            && (fabs(cellsize_x/cellsize_y) > 1.00001
                || fabs(cellsize_x/cellsize_y) < 0.99999) )
        {
            map->gt.need_geotransform = MS_TRUE;
            if (map->debug)
                msDebug( "msDrawMap(): kicking into non-square pixel preserving mode." );
        }
        map->cellsize = (cellsize_x*0.5 + cellsize_y*0.5);
    }
    else
        map->cellsize = msAdjustExtent(&(map->extent),map->width,map->height);

    status = msCalculateScale(map->extent,map->units,map->width,map->height, map->resolution, &map->scaledenom);
    if(status != MS_SUCCESS) {
        msFreeImage(image);
        return(NULL);
    }

   /* update geotransform based on adjusted extent. */
    msMapComputeGeotransform( map );

    /* Do we need to fake out stuff for rotated support? */
    if( map->gt.need_geotransform )
        msMapSetFakedExtent( map );

    /* We will need a cellsize that represents a real georeferenced */
    /* coordinate cellsize here, so compute it from saved extents.   */

    geo_cellsize = map->cellsize;
    if( map->gt.need_geotransform == MS_TRUE ) {
        double cellsize_x = (map->saved_extent.maxx - map->saved_extent.minx)
            / map->width;
        double cellsize_y = (map->saved_extent.maxy - map->saved_extent.miny)
            / map->height;

        geo_cellsize = sqrt(cellsize_x*cellsize_x + cellsize_y*cellsize_y)
            / sqrt(2.0);
    } 

    /* compute layer scale factors now */
    for(i=0;i<map->numlayers; i++) {
      if(GET_LAYER(map, i)->sizeunits != MS_PIXELS)
        GET_LAYER(map, i)->scalefactor = (msInchesPerUnit(GET_LAYER(map, i)->sizeunits,0)/msInchesPerUnit(map->units,0)) / geo_cellsize;
      else if(GET_LAYER(map, i)->symbolscaledenom > 0 && map->scaledenom > 0)
        GET_LAYER(map, i)->scalefactor = GET_LAYER(map, i)->symbolscaledenom/map->scaledenom;
      else
        GET_LAYER(map, i)->scalefactor = 1;
    }

    return image;
}


/*
 * Generic function to render the map file.
 * The type of the image created is based on the imagetype parameter in the map file.
 *
 * mapObj *map - map object loaded in MapScript or via a mapfile to use
 * int querymap - is this map the result of a query operation, MS_TRUE|MS_FALSE 
*/
imageObj *msDrawMap(mapObj *map, int querymap)
{
  int i;
  layerObj *lp=NULL;
  int status = MS_FAILURE;
  imageObj *image = NULL;
  struct mstimeval mapstarttime, mapendtime;
  struct mstimeval starttime, endtime;
  int oldAlphaBlending;  /* allows toggling of gd alpha blending (bug 490) */

#if defined(USE_WMS_LYR) || defined(USE_WFS_LYR)
  enum MS_CONNECTION_TYPE lastconnectiontype;
  httpRequestObj *pasOWSReqInfo=NULL;
  int numOWSLayers=0, numOWSRequests=0;
  wmsParamsObj sLastWMSParams;
#endif

  if(map->debug >= MS_DEBUGLEVEL_TUNING) msGettimeofday(&mapstarttime, NULL);

  if(querymap) { /* use queryMapObj image dimensions */
    if(map->querymap.width != -1) map->width = map->querymap.width;
    if(map->querymap.height != -1) map->height = map->querymap.height;
    if(map->querymap.style == MS_NORMAL) querymap = MS_FALSE; /* draw as normal */
  }

  msApplyMapConfigOptions(map);
  image = msPrepareImage(map, MS_TRUE);

  if(!image) {
    msSetError(MS_IMGERR, "Unable to initialize image.", "msDrawMap()");
    return(NULL);
  }

#if defined(USE_WMS_LYR) || defined(USE_WFS_LYR)
  /* How many OWS (WMS/WFS) layers do we have to draw?
   * Note: numOWSLayers is the number of actual layers and numOWSRequests is
   * the number of HTTP requests which could be lower if multiple layers 
   * are merged into the same request.
   */
  numOWSLayers=0;
  for(i=0; i<map->numlayers; i++) {
    if(map->layerorder[i] != -1 && 
       msLayerIsVisible(map, GET_LAYER(map,map->layerorder[i])))
        numOWSLayers++;
  }

  if (numOWSLayers > 0) {
    /* Alloc and init pasOWSReqInfo...
     */
    pasOWSReqInfo = (httpRequestObj *)malloc((numOWSLayers+1)*sizeof(httpRequestObj));
    if (pasOWSReqInfo == NULL) {
      msSetError(MS_MEMERR, "Allocation of httpRequestObj failed.", "msDrawMap()");
      return NULL;
    }
    msHTTPInitRequestObj(pasOWSReqInfo, numOWSLayers+1);
    msInitWmsParamsObj(&sLastWMSParams);

    /* Pre-download all WMS/WFS layers in parallel before starting to draw map */
    lastconnectiontype = MS_SHAPEFILE;
    for(i=0; numOWSLayers && i<map->numlayers; i++) {
      if(map->layerorder[i] == -1 || !msLayerIsVisible(map, GET_LAYER(map,map->layerorder[i])))
        continue;

      lp = GET_LAYER(map,map->layerorder[i]);

#ifdef USE_WMS_LYR
      if(lp->connectiontype == MS_WMS) {
        if(msPrepareWMSLayerRequest(map->layerorder[i], map, lp, lastconnectiontype, &sLastWMSParams, pasOWSReqInfo, &numOWSRequests) == MS_FAILURE) {
          msFreeWmsParamsObj(&sLastWMSParams);
          msFreeImage(image);
          msFree(pasOWSReqInfo);
          return NULL;
        }
      }
#endif

#ifdef USE_WFS_LYR
      if(lp->connectiontype == MS_WFS) {
        if(msPrepareWFSLayerRequest(map->layerorder[i], map, lp, pasOWSReqInfo, &numOWSRequests) == MS_FAILURE) {
          msFreeWmsParamsObj(&sLastWMSParams);
          msFreeImage(image);
          msFree(pasOWSReqInfo);
          return NULL;
        }
      }
#endif

      lastconnectiontype = lp->connectiontype;
    }

#ifdef USE_WMS_LYR
  msFreeWmsParamsObj(&sLastWMSParams);
#endif
  } /* if numOWSLayers > 0 */

  if(numOWSRequests && msOWSExecuteRequests(pasOWSReqInfo, numOWSRequests, map, MS_TRUE) == MS_FAILURE) {
    msFreeImage(image);
    msFree(pasOWSReqInfo);
    return NULL;
  }
#endif /* USE_WMS_LYR || USE_WFS_LYR */

  /* OK, now we can start drawing */
  for(i=0; i<map->numlayers; i++) {

    if(map->layerorder[i] != -1) {
      lp = (GET_LAYER(map,  map->layerorder[i]));

      if(lp->postlabelcache) /* wait to draw */
        continue;

      if(map->debug >= MS_DEBUGLEVEL_TUNING || lp->debug >= MS_DEBUGLEVEL_TUNING ) msGettimeofday(&starttime, NULL);

      if(!msLayerIsVisible(map, lp)) continue;

      if(lp->connectiontype == MS_WMS) {
#ifdef USE_WMS_LYR 
        if(MS_RENDERER_GD(image->format) || MS_RENDERER_RAWDATA(image->format))
          status = msDrawWMSLayerLow(map->layerorder[i], pasOWSReqInfo, numOWSRequests,  map, lp, image);
#ifdef USE_AGG
        else if(MS_RENDERER_AGG(image->format))
          status = msDrawWMSLayerLow(map->layerorder[i], pasOWSReqInfo, numOWSRequests, map, lp, image);
#endif
#ifdef USE_MING_FLASH                
        else if(MS_RENDERER_SWF(image->format))
          status = msDrawWMSLayerSWF(map->layerorder[i], pasOWSReqInfo, numOWSRequests, map, lp, image);
#endif
#ifdef USE_PDF
        else if(MS_RENDERER_PDF(image->format))
          status = msDrawWMSLayerPDF(map->layerorder[i], pasOWSReqInfo, numOWSRequests, map, lp, image);
#endif
        else {
          msSetError(MS_WMSCONNERR, "Output format '%s' doesn't support WMS layers.", "msDrawMap()", image->format->name);
          status = MS_FAILURE;
        }
                
        if(status == MS_FAILURE) {
          msSetError(MS_WMSCONNERR, 
                     "Failed to draw WMS layer named '%s'. This most likely happened because "
                     "the remote WMS server returned an invalid image, and XML exception "
                     "or another unexpected result in response to the GetMap request. Also check "
                     "and make sure that the layer's connection URL is valid.",
                     "msDrawMap()", lp->name);
          msFreeImage(image);
          msHTTPFreeRequestObj(pasOWSReqInfo, numOWSRequests);
          msFree(pasOWSReqInfo);
          return(NULL);
        }


#else /* ndef USE_WMS_LYR */
        msSetError(MS_WMSCONNERR, "MapServer not built with WMS Client support, unable to render layer '%s'.", "msDrawMap()", lp->name);
        msFreeImage(image);
        return(NULL);
#endif
      } else { /* Default case: anything but WMS layers */
        if(querymap)
          status = msDrawQueryLayer(map, lp, image);
        else
          status = msDrawLayer(map, lp, image);
        if(status == MS_FAILURE) {
          msSetError(MS_IMGERR, "Failed to draw layer named '%s'.", "msDrawMap()", lp->name);
          msFreeImage(image);
#if defined(USE_WMS_LYR) || defined(USE_WFS_LYR)
          if (pasOWSReqInfo) {
            msHTTPFreeRequestObj(pasOWSReqInfo, numOWSRequests);
            msFree(pasOWSReqInfo);
          }
#endif /* USE_WMS_LYR || USE_WFS_LYR */
          return(NULL);
        }
      }
    }

    if(map->debug >= MS_DEBUGLEVEL_TUNING || lp->debug >= MS_DEBUGLEVEL_TUNING) {
      msGettimeofday(&endtime, NULL);
      msDebug("msDrawMap(): Layer %d (%s), %.3fs\n", 
              map->layerorder[i], lp->name?lp->name:"(null)",
              (endtime.tv_sec+endtime.tv_usec/1.0e6)-
              (starttime.tv_sec+starttime.tv_usec/1.0e6) );
    }
  }

  if(map->scalebar.status == MS_EMBED && !map->scalebar.postlabelcache) {

    /* We need to temporarily restore the original extent for drawing */
    /* the scalebar as it uses the extent to recompute cellsize. */
    if(map->gt.need_geotransform)
      msMapRestoreRealExtent(map);

    /* fix for bug 490 - turn on alpha blending for embedded scalebar */
    oldAlphaBlending = (image->img.gd)->alphaBlendingFlag;
    gdImageAlphaBlending(image->img.gd, 1);

    msEmbedScalebar(map, image); /* TODO   */

    /* restore original alpha blending */
    gdImageAlphaBlending(image->img.gd, oldAlphaBlending);

    if(map->gt.need_geotransform)
      msMapSetFakedExtent(map);
  }

  if(map->legend.status == MS_EMBED && !map->legend.postlabelcache)
    msEmbedLegend(map, image);

  if(map->debug >= MS_DEBUGLEVEL_TUNING) msGettimeofday(&starttime, NULL);

  if(msDrawLabelCache(image, map) == -1) {
    msFreeImage(image);
#if defined(USE_WMS_LYR) || defined(USE_WFS_LYR)
    if (pasOWSReqInfo) {
      msHTTPFreeRequestObj(pasOWSReqInfo, numOWSRequests);
      msFree(pasOWSReqInfo);
    }
#endif /* USE_WMS_LYR || USE_WFS_LYR */
    return(NULL);
  }

  if(map->debug >= MS_DEBUGLEVEL_TUNING) {
    msGettimeofday(&endtime, NULL);
    msDebug("msDrawMap(): Drawing Label Cache, %.3fs\n", 
            (endtime.tv_sec+endtime.tv_usec/1.0e6)-
            (starttime.tv_sec+starttime.tv_usec/1.0e6) );
  }

  for(i=0; i<map->numlayers; i++) { /* for each layer, check for postlabelcache layers */

    lp = (GET_LAYER(map, map->layerorder[i]));

    if(!lp->postlabelcache) continue;
    if(!msLayerIsVisible(map, lp)) continue;

    if(map->debug >= MS_DEBUGLEVEL_TUNING || lp->debug >= MS_DEBUGLEVEL_TUNING) msGettimeofday(&starttime, NULL);

    if(lp->connectiontype == MS_WMS) {
#ifdef USE_WMS_LYR 
      if(MS_RENDERER_GD(image->format) || MS_RENDERER_RAWDATA(image->format))
        status = msDrawWMSLayerLow(map->layerorder[i], pasOWSReqInfo, numOWSRequests, map, lp, image);
#ifdef USE_AGG               
      else if(MS_RENDERER_AGG(image->format))
        status = msDrawWMSLayerLow(map->layerorder[i], pasOWSReqInfo, numOWSRequests, map, lp, image);
#endif
#ifdef USE_MING_FLASH
      else if(MS_RENDERER_SWF(image->format) )
        status = msDrawWMSLayerSWF(map->layerorder[i], pasOWSReqInfo, numOWSRequests, map, lp, image);
#endif
#ifdef USE_PDF
      else if(MS_RENDERER_PDF(image->format) )
        status = msDrawWMSLayerPDF(map->layerorder[i], pasOWSReqInfo, numOWSRequests, map, lp, image);
#endif

#else
      status = MS_FAILURE;
#endif
    } else {
      if(querymap)
        status = msDrawQueryLayer(map, lp, image);
      else
        status = msDrawLayer(map, lp, image);
    }

    if(status == MS_FAILURE) {
      msFreeImage(image);
#if defined(USE_WMS_LYR) || defined(USE_WFS_LYR)
      if (pasOWSReqInfo) {
        msHTTPFreeRequestObj(pasOWSReqInfo, numOWSRequests);
        msFree(pasOWSReqInfo);
      }
#endif /* USE_WMS_LYR || USE_WFS_LYR */
      return(NULL);
    }

    if(map->debug >= MS_DEBUGLEVEL_TUNING || lp->debug >= MS_DEBUGLEVEL_TUNING) {
      msGettimeofday(&endtime, NULL);
      msDebug("msDrawMap(): Layer %d (%s), %.3fs\n", 
              map->layerorder[i], lp->name?lp->name:"(null)",
              (endtime.tv_sec+endtime.tv_usec/1.0e6)-
              (starttime.tv_sec+starttime.tv_usec/1.0e6) );
    }

  }
  
  /* Do we need to fake out stuff for rotated support? */
  /* This really needs to be done on every preceeding exit point too... */
  if(map->gt.need_geotransform)
    msMapRestoreRealExtent(map);

  if(map->scalebar.status == MS_EMBED && map->scalebar.postlabelcache) {

    /* fix for bug 490 - turn on alpha blending for embedded scalebar */
    oldAlphaBlending = (image->img.gd)->alphaBlendingFlag;
    gdImageAlphaBlending(image->img.gd, 1);

    msEmbedScalebar(map, image); /* TODO   */

    /* restore original alpha blending */
    gdImageAlphaBlending(image->img.gd, oldAlphaBlending);
  }

  if(map->legend.status == MS_EMBED && map->legend.postlabelcache)
    msEmbedLegend(map, image); /* TODO */

#if defined(USE_WMS_LYR) || defined(USE_WFS_LYR)
  /* Cleanup WMS/WFS Request stuff */
  if (pasOWSReqInfo) {
    msHTTPFreeRequestObj(pasOWSReqInfo, numOWSRequests);
    msFree(pasOWSReqInfo);
  }
#endif

  if(map->debug >= MS_DEBUGLEVEL_TUNING) {
    msGettimeofday(&mapendtime, NULL);
    msDebug("msDrawMap() total time: %.3fs\n", 
            (mapendtime.tv_sec+mapendtime.tv_usec/1.0e6)-
            (mapstarttime.tv_sec+mapstarttime.tv_usec/1.0e6) );
  }

  return(image);
}

/*
 * Test whether a layer should be drawn or not in the current map view and
 * at the current scale.  
 * Returns TRUE if layer is visible, FALSE if not.
*/
int msLayerIsVisible(mapObj *map, layerObj *layer)
{
  int i;

  if(!layer->data && !layer->tileindex && !layer->connection && !layer->features && !layer->layerinfo)
    return(MS_FALSE); /* no data associated with this layer, not an error since layer may be used as a template from MapScript */

  if(layer->type == MS_LAYER_QUERY || layer->type == MS_LAYER_TILEINDEX) return(MS_FALSE);
  if((layer->status != MS_ON) && (layer->status != MS_DEFAULT)) return(MS_FALSE);
  if(msEvalContext(map, layer, layer->requires) == MS_FALSE) return(MS_FALSE);

  if(map->scaledenom > 0) {
    
    /* layer scale boundaries should be checked first */
    if((layer->maxscaledenom > 0) && (map->scaledenom > layer->maxscaledenom)) return(MS_FALSE);
    if((layer->minscaledenom > 0) && (map->scaledenom <= layer->minscaledenom)) return(MS_FALSE);

    /* now check class scale boundaries (all layers *must* pass these tests) */
    if(layer->numclasses > 0) {
      for(i=0; i<layer->numclasses; i++) {
        if((layer->class[i]->maxscaledenom > 0) && (map->scaledenom > layer->class[i]->maxscaledenom))
          continue; /* can skip this one, next class */
        if((layer->class[i]->minscaledenom > 0) && (map->scaledenom <= layer->class[i]->minscaledenom))
          continue; /* can skip this one, next class */

        break; /* can't skip this class (or layer for that matter) */
      } 
      if(i == layer->numclasses) return(MS_FALSE);
    }

  }

  return MS_TRUE;  /* All tests passed.  Layer is visible. */
}
/*
 * Generic function to render a layer object.
*/
int msDrawLayer(mapObj *map, layerObj *layer, imageObj *image)
{
  imageObj *image_draw = image;
  outputFormatObj *transFormat = NULL;
  int retcode=MS_SUCCESS;
  int oldAlphaBlending=0;  /* allow toggling of gd alpha blending (bug 490) */

  if(!msLayerIsVisible(map, layer))
    return MS_SUCCESS;  

  if(layer->opacity == 0) return MS_SUCCESS; /* layer is completely transparent, skip it */

  /* conditions may have changed since this layer last drawn, so set
     layer->project true to recheck projection needs (Bug #673) */
  layer->project = MS_TRUE;

  /* inform the rendering device that layer draw is starting. */
  msImageStartLayer(map, layer, image);

  if(MS_RENDERER_GD(image_draw->format)) {

    /* 
    ** for layer-level opacity we render to a temp image
    */
    if(layer->opacity > 0 && layer->opacity < 100) {
      msApplyOutputFormat(&transFormat, image->format, MS_TRUE, MS_NOOVERRIDE, MS_NOOVERRIDE);
      
      image_draw = msImageCreateGD( image->width, image->height, transFormat, image->imagepath, image->imageurl );
      if(!image_draw) {
        msSetError(MS_GDERR, "Unable to initialize image.", "msDrawLayer()");
        return(MS_FAILURE);
      }
      msImageInitGD(image_draw, &map->imagecolor);
      
      if(image_draw->format->imagemode == MS_IMAGEMODE_PC256) /* gdImageCopyMerge() needs this later */
        gdImageColorTransparent(image_draw->img.gd, 0);
    }

    /* Bug 490 - switch alpha blending on for a layer that requires it */
    else if (layer->opacity == MS_GD_ALPHA) {
        oldAlphaBlending = (image->img.gd)->alphaBlendingFlag;
        gdImageAlphaBlending(image->img.gd, 1);
    }
  }
#ifdef USE_AGG
  else if(MS_RENDERER_AGG(image_draw->format)) {
    
    /* 
    ** for layer-level opacity we render to a temp image
    */
    if(layer->opacity > 0 && layer->opacity < 100) {
      msApplyOutputFormat(&transFormat, image->format, MS_TRUE, MS_NOOVERRIDE, MS_NOOVERRIDE);

      image_draw = msImageCreateAGG(image->width, image->height, transFormat, image->imagepath, image->imageurl);
      if(!image_draw) {
        msSetError(MS_GDERR, "Unable to initialize image.", "msDrawLayer()");
        return(MS_FAILURE);
      }
      msImageInitAGG(image_draw, &map->imagecolor);
    }
  }
#endif

  /* 
  ** redirect procesing of some layer types. 
  */
  if(layer->connectiontype == MS_WMS) {
#ifdef USE_WMS_LYR
#ifdef USE_AGG
      if( MS_RENDERER_AGG(image_draw->format))
          msAlphaAGG2GD(image_draw);
#endif
    retcode = msDrawWMSLayer(map, layer, image_draw);
#else  
    retcode = MS_FAILURE;
#endif
  } else if(layer->type == MS_LAYER_RASTER) {
#ifdef USE_AGG
      if( MS_RENDERER_AGG(image_draw->format))
          msAlphaAGG2GD(image_draw);
#endif
    retcode = msDrawRasterLayer(map, layer, image_draw);
  } else if(layer->type == MS_LAYER_CHART) {
#ifdef USE_AGG
      if( MS_RENDERER_AGG(image_draw->format))
          msAlphaGD2AGG(image_draw);
#endif
    retcode = msDrawChartLayer(map, layer, image_draw);
  } else {   /* must be a Vector layer */
#ifdef USE_AGG
      if( MS_RENDERER_AGG(image_draw->format))
          msAlphaGD2AGG(image_draw);
#endif
    retcode = msDrawVectorLayer(map, layer, image_draw);
  }

  /* Destroy the temp image for this layer tranparency */
  if( MS_RENDERER_GD(image_draw->format) && layer->opacity > 0 && layer->opacity < 100 ) {

      if(layer->type == MS_LAYER_RASTER)
          msImageCopyMerge(image->img.gd, image_draw->img.gd, 0, 0, 0, 0, image->img.gd->sx, image->img.gd->sy, layer->opacity);
      else {
          msImageCopyMergeNoAlpha(image->img.gd, image_draw->img.gd, 0, 0, 0, 0, image->img.gd->sx, image->img.gd->sy, layer->opacity, &map->imagecolor);
      }
      msFreeImage(image_draw);

    /* deref and possibly free temporary transparent output format.  */
    msApplyOutputFormat( &transFormat, NULL, MS_NOOVERRIDE, MS_NOOVERRIDE, MS_NOOVERRIDE );
  }
#ifdef USE_AGG
  else if( MS_RENDERER_AGG(image_draw->format) && layer->opacity > 0 && layer->opacity < 100 ) {
      msAlphaGD2AGG(image_draw);
      msAlphaGD2AGG(image);
    msImageCopyMergeAGG(image, image_draw, layer->opacity);
    msFreeImage( image_draw );

    /* deref and possibly free temporary transparent output format.  */
    msApplyOutputFormat( &transFormat, NULL, MS_NOOVERRIDE, MS_NOOVERRIDE, MS_NOOVERRIDE );
  }
#endif

  /* restore original alpha blending */
  else if (layer->opacity == MS_GD_ALPHA && MS_RENDERER_GD(image_draw->format)) {
    gdImageAlphaBlending(image->img.gd, oldAlphaBlending);
  } else {
    assert( image == image_draw );
  }

  return(retcode);
}

int msDrawVectorLayer(mapObj *map, layerObj *layer, imageObj *image)
{
  int         status, retcode=MS_SUCCESS;
  char        annotate=MS_TRUE;
  shapeObj    shape;
  rectObj     searchrect;
  char        cache=MS_FALSE;
  int         maxnumstyles=1;
  featureListNodeObjPtr shpcache=NULL, current=NULL;
  int nclasses = 0;
  int *classgroup = NULL;

/* ==================================================================== */
/*      For Flash, we use a metadata called SWFOUTPUT that              */
/*      is used to render vector layers as rasters. It is also true     */
/*      if  the output movie  format indicated in the map file is       */
/*      SINGLE.                                                         */
/* ==================================================================== */
#ifdef USE_MING_FLASH
  if(image &&  MS_RENDERER_SWF(image->format))
  {
    if ((msLookupHashTable(&(layer->metadata), "SWFOUTPUT") &&
        strcasecmp(msLookupHashTable(&(layer->metadata), "SWFOUTPUT"),"RASTER")==0) ||
        strcasecmp(msGetOutputFormatOption(image->format,"OUTPUT_MOVIE", ""),  
                   "MULTIPLE") != 0)
    return msDrawVectorLayerAsRasterSWF(map, layer, image);
  }
#endif
  

/* ==================================================================== */
/*      For PDF if the output_type is set to raster, draw the vector    */
/*      into a gd image.                                                */
/* ==================================================================== */
#ifdef USE_PDF
  if(image &&  MS_RENDERER_PDF(image->format))
  {
    if (strcasecmp(msGetOutputFormatOption(image->format,"OUTPUT_TYPE", ""),  
                   "RASTER") == 0)
    return msDrawVectorLayerAsRasterPDF(map, layer, image);
  }
#endif

  annotate = msEvalContext(map, layer, layer->labelrequires);
  if(map->scaledenom > 0) {
    if((layer->labelmaxscaledenom != -1) && (map->scaledenom >= layer->labelmaxscaledenom)) annotate = MS_FALSE;
    if((layer->labelminscaledenom != -1) && (map->scaledenom < layer->labelminscaledenom)) annotate = MS_FALSE;
  }

  /* reset layer pen values just in case the map has been previously processed */
  msClearLayerPenValues(layer);
  
  /* open this layer */
  status = msLayerOpen(layer);
  if(status != MS_SUCCESS) return MS_FAILURE;
  
  /* build item list */
/* ==================================================================== */
/*      For Flash, we use a metadata called SWFDUMPATTRIBUTES that      */
/*      contains a list of attributes that we want to write to the      */
/*      flash movie for query purpose.                                  */
/* ==================================================================== */
  if(image && MS_RENDERER_SWF(image->format))
    status = msLayerWhichItems(layer, MS_TRUE, annotate, msLookupHashTable(&(layer->metadata), "SWFDUMPATTRIBUTES"));                                
  else        
    status = msLayerWhichItems(layer, MS_TRUE, annotate, NULL);

  if(status != MS_SUCCESS) {
    msLayerClose(layer);
    return MS_FAILURE;
  }
  
  /* identify target shapes */
  if(layer->transform == MS_TRUE)
    searchrect = map->extent;
  else {
    searchrect.minx = searchrect.miny = 0;
    searchrect.maxx = map->width-1;
    searchrect.maxy = map->height-1;
  }
  
#ifdef USE_PROJ
  if((map->projection.numargs > 0) && (layer->projection.numargs > 0))
    msProjectRect(&map->projection, &layer->projection, &searchrect); /* project the searchrect to source coords */
#endif
    
  status = msLayerWhichShapes(layer, searchrect);
  if(status == MS_DONE) { /* no overlap */
    msLayerClose(layer);
    return MS_SUCCESS;
  } else if(status != MS_SUCCESS) {
    msLayerClose(layer);
    return MS_FAILURE;
  }
  
  /* step through the target shapes */
  msInitShape(&shape);
  
  nclasses = 0;
  classgroup = NULL;
  if (layer->classgroup && layer->numclasses > 0)
      classgroup = msAllocateValidClassGroups(layer, &nclasses);

  while((status = msLayerNextShape(layer, &shape)) == MS_SUCCESS) {

      shape.classindex = msShapeGetClass(layer, &shape, map->scaledenom, classgroup, nclasses);
    if((shape.classindex == -1) || (layer->class[shape.classindex]->status == MS_OFF)) {
       msFreeShape(&shape);
       continue;
    }
  
    cache = MS_FALSE;
    if(layer->type == MS_LAYER_LINE && layer->class[shape.classindex]->numstyles > 1) 
      cache = MS_TRUE; /* only line layers with multiple styles need be cached (I don't think POLYLINE layers need caching - SDL) */
         
    /* With 'STYLEITEM AUTO', we will have the datasource fill the class' */
    /* style parameters for this shape. */
    if(layer->styleitem && strcasecmp(layer->styleitem, "AUTO") == 0) {
      if(msLayerGetAutoStyle(map, layer, layer->class[shape.classindex], shape.tileindex, shape.index) != MS_SUCCESS) {
        retcode = MS_FAILURE;
        break;
      }
                  
      /* __TODO__ For now, we can't cache features with 'AUTO' style */
      cache = MS_FALSE;
    }
  
    if(annotate && (layer->class[shape.classindex]->text.string || layer->labelitem) && layer->class[shape.classindex]->label.size != -1)
      shape.text = msShapeGetAnnotation(layer, &shape);

    if(cache)
      status = msDrawShape(map, layer, &shape, image, 0); /* draw only the first style */
    else
      status = msDrawShape(map, layer, &shape, image, -1); /* all styles  */
    if(status != MS_SUCCESS) {
      msFreeShape(&shape);
      retcode = MS_FAILURE;
      break;
    }

    if(shape.numlines == 0) { /* once clipped the shape didn't need to be drawn */
      msFreeShape(&shape);
      continue;
    }
  
    if(cache) {
      if(insertFeatureList(&shpcache, &shape) == NULL) {
        retcode = MS_FAILURE; /* problem adding to the cache */
        break;
      }
    }  

    maxnumstyles = MS_MAX(maxnumstyles, layer->class[shape.classindex]->numstyles);
    msFreeShape(&shape);
  }
    
  if (classgroup)
    msFree(classgroup);

  if(status != MS_DONE) {
    msLayerClose(layer);
    return MS_FAILURE;
  }
  
  if(shpcache) {
    int s;
      
    for(s=1; s<maxnumstyles; s++) {
      for(current=shpcache; current; current=current->next) {        
        if(layer->class[current->shape.classindex]->numstyles > s)
	  msDrawLineSymbol(&map->symbolset, image, &current->shape, layer->class[current->shape.classindex]->styles[s], layer->scalefactor);
      }
    }
    
    freeFeatureList(shpcache);
    shpcache = NULL;  
  }

  msLayerClose(layer);  
  return MS_SUCCESS;
  
}

/*
** Function to draw a layer IF it already has a result cache associated with it. Called by msDrawQueryMap and via MapScript.
*/
int msDrawQueryLayer(mapObj *map, layerObj *layer, imageObj *image)
{
  int i, status;
  char annotate=MS_TRUE, cache=MS_FALSE;
  shapeObj shape;
  int maxnumstyles=1;

  featureListNodeObjPtr shpcache=NULL, current=NULL;

  colorObj *colorbuffer = NULL;
  int *mindistancebuffer = NULL;

  if(!layer->resultcache || map->querymap.style == MS_NORMAL)
    return(msDrawLayer(map, layer, image));

  if(!layer->data && !layer->tileindex && !layer->connection && !layer->features) 
   return(MS_SUCCESS); /* no data associated with this layer, not an error since layer may be used as a template from MapScript */

  if(layer->type == MS_LAYER_QUERY || layer->type == MS_LAYER_TILEINDEX) return(MS_SUCCESS); /* query and tileindex layers simply can't be drawn, not an error */
  
  if( layer->type == MS_LAYER_RASTER ) {
      msSetError( MS_QUERYERR, "Unable to draw raster layers (such as %s) as part of a query result.", "msDrawQueryLayer()", layer->name );
      return MS_FAILURE;
  }


  if(map->querymap.style == MS_HILITE) { /* first, draw normally, but don't return */
    status = msDrawLayer(map, layer, image);
    if(status != MS_SUCCESS) return(MS_FAILURE); /* oops */
  }

  if((layer->status != MS_ON) && (layer->status != MS_DEFAULT)) return(MS_SUCCESS);

  if(msEvalContext(map, layer, layer->requires) == MS_FALSE) return(MS_SUCCESS);
  annotate = msEvalContext(map, layer, layer->labelrequires);

  if(map->scaledenom > 0) {
    if((layer->maxscaledenom > 0) && (map->scaledenom > layer->maxscaledenom)) return(MS_SUCCESS);
    if((layer->minscaledenom > 0) && (map->scaledenom <= layer->minscaledenom)) return(MS_SUCCESS);

    if((layer->labelmaxscaledenom != -1) && (map->scaledenom >= layer->labelmaxscaledenom)) annotate = MS_FALSE;
    if((layer->labelminscaledenom != -1) && (map->scaledenom < layer->labelminscaledenom)) annotate = MS_FALSE;
  }

  /* reset layer pen values just in case the map has been previously processed */
  msClearLayerPenValues(layer);

  /* if MS_HILITE, alter the one style (always at least 1 style), and set a MINDISTANCE for the labelObj to avoid duplicates */
  if(map->querymap.style == MS_HILITE) {
    if (layer->numclasses > 0) {
        colorbuffer = (colorObj*)malloc(layer->numclasses*sizeof(colorObj));
        mindistancebuffer = (int*)malloc(layer->numclasses*sizeof(int));

        if (colorbuffer == NULL || mindistancebuffer == NULL) {
            msSetError(MS_MEMERR, "Failed to allocate memory for colorbuffer/mindistancebuffer", "msDrawQueryLayer()");
            return MS_FAILURE;
        }
    }

    for(i=0; i<layer->numclasses; i++) {
      if(layer->type == MS_LAYER_POLYGON) { /* alter BOTTOM style since that's almost always the fill */
        if(MS_VALID_COLOR(layer->class[i]->styles[0]->color)) {
          colorbuffer[i] = layer->class[i]->styles[0]->color; /* save the color from the BOTTOM style */
          layer->class[i]->styles[0]->color = map->querymap.color;
        } else if(MS_VALID_COLOR(layer->class[i]->styles[0]->outlinecolor)) {
          colorbuffer[i] = layer->class[i]->styles[0]->outlinecolor; /* if no color, save the outlinecolor from the BOTTOM style */
          layer->class[i]->styles[0]->outlinecolor = map->querymap.color;
        }
      } else {
        if(MS_VALID_COLOR(layer->class[i]->styles[layer->class[i]->numstyles-1]->color)) {
          colorbuffer[i] = layer->class[i]->styles[layer->class[i]->numstyles-1]->color; /* save the color from the TOP style */
          layer->class[i]->styles[layer->class[i]->numstyles-1]->color = map->querymap.color;
        } else if(MS_VALID_COLOR(layer->class[i]->styles[layer->class[i]->numstyles-1]->outlinecolor)) {
	  colorbuffer[i] = layer->class[i]->styles[layer->class[i]->numstyles-1]->outlinecolor; /* if no color, save the outlinecolor from the TOP style */
          layer->class[i]->styles[layer->class[i]->numstyles-1]->outlinecolor = map->querymap.color;
        }
      }

      mindistancebuffer[i] = layer->class[i]->label.mindistance;
      layer->class[i]->label.mindistance = MS_MAX(0, layer->class[i]->label.mindistance);
    }
  }

  /* open this layer */
  status = msLayerOpen(layer);
  if(status != MS_SUCCESS) {
      msFree(colorbuffer);
      msFree(mindistancebuffer);
      return(MS_FAILURE);
  }

  /* build item list */
  status = msLayerWhichItems(layer, MS_TRUE, annotate, NULL); /* FIX: results have already been classified (this may change) */
  if(status != MS_SUCCESS) {
      msFree(colorbuffer);
      msFree(mindistancebuffer);
      return(MS_FAILURE);
  }
#ifdef USE_AGG
  if(MS_RENDERER_AGG(map->outputformat))
      msAlphaGD2AGG(image);
#endif

  msInitShape(&shape);

  for(i=0; i<layer->resultcache->numresults; i++) {
    status = msLayerGetShape(layer, &shape, layer->resultcache->results[i].tileindex, layer->resultcache->results[i].shapeindex);
    if(status != MS_SUCCESS) {
        msFree(colorbuffer);
        msFree(mindistancebuffer);
        return(MS_FAILURE);
    }

    shape.classindex = layer->resultcache->results[i].classindex;
    /* classindex may be -1 here if there was a template at the top level
     * in this layer and the current shape selected even if it didn't
     * match any class 
     *
     * FrankW: classindex is also sometimes 0 even if there are no classes, so 
     * we are careful not to use out of range class values as an index.
     */
    if(shape.classindex==-1 
       || shape.classindex >= layer->numclasses
       || layer->class[shape.classindex]->status == MS_OFF) {
      msFreeShape(&shape);
      continue;
    }

    cache = MS_FALSE;
    if(layer->type == MS_LAYER_LINE && layer->class[shape.classindex]->numstyles > 1) 
      cache = MS_TRUE; /* only line layers with multiple styles need be cached (I don't think POLYLINE layers need caching - SDL) */

    if(annotate && (layer->class[shape.classindex]->text.string || layer->labelitem) && layer->class[shape.classindex]->label.size != -1)
      shape.text = msShapeGetAnnotation(layer, &shape);

    if(cache)
      status = msDrawShape(map, layer, &shape, image, 0); /* draw only the first style */
    else
      status = msDrawShape(map, layer, &shape, image, -1); /* all styles  */
    if(status != MS_SUCCESS) {
      msLayerClose(layer);
      msFree(colorbuffer);
      msFree(mindistancebuffer);
      return(MS_FAILURE);
    }

    if(shape.numlines == 0) { /* once clipped the shape didn't need to be drawn */
      msFreeShape(&shape);
      continue;
    }

    if(cache) {
      if(insertFeatureList(&shpcache, &shape) == NULL) return(MS_FAILURE); /* problem adding to the cache */
    }

    maxnumstyles = MS_MAX(maxnumstyles, layer->class[shape.classindex]->numstyles);
    msFreeShape(&shape);
  }

  if(shpcache) {
    int s;
  
    for(s=1; s<maxnumstyles; s++) {
      for(current=shpcache; current; current=current->next) {        
        if(layer->class[current->shape.classindex]->numstyles > s)
	  msDrawLineSymbol(&map->symbolset, image, &current->shape, (layer->class[current->shape.classindex]->styles[s]), layer->scalefactor);
      }
    }
    
    freeFeatureList(shpcache);
    shpcache = NULL;  
  }

  /* if MS_HILITE, restore color and mindistance values */
  if(map->querymap.style == MS_HILITE) {
    for(i=0; i<layer->numclasses; i++) {
      if(layer->type == MS_LAYER_POLYGON) {
	if(MS_VALID_COLOR(layer->class[i]->styles[0]->color))
          layer->class[i]->styles[0]->color = colorbuffer[i];
        else if(MS_VALID_COLOR(layer->class[i]->styles[0]->outlinecolor))
          layer->class[i]->styles[0]->outlinecolor = colorbuffer[i]; /* if no color, restore outlinecolor for the BOTTOM style */
      } else {
        if(MS_VALID_COLOR(layer->class[i]->styles[layer->class[i]->numstyles-1]->color))
          layer->class[i]->styles[layer->class[i]->numstyles-1]->color = colorbuffer[i];        
        else if(MS_VALID_COLOR(layer->class[i]->styles[layer->class[i]->numstyles-1]->outlinecolor))
	  layer->class[i]->styles[layer->class[i]->numstyles-1]->outlinecolor = colorbuffer[i]; /* if no color, restore outlinecolor for the TOP style */
      }
    
      layer->class[i]->label.mindistance = mindistancebuffer[i];
    }

    msFree(colorbuffer);
    msFree(mindistancebuffer);
  }

  msLayerClose(layer);

  return(MS_SUCCESS);
}

/**
 * Generic function to render raster layers.
 */
int msDrawRasterLayer(mapObj *map, layerObj *layer, imageObj *image) 
{
    if (image && map && layer)
    {
        if( MS_RENDERER_GD(image->format) )
            return msDrawRasterLayerLow(map, layer, image);
#ifdef USE_AGG
        else if( MS_RENDERER_AGG(image->format) )
            return msDrawRasterLayerLow(map, layer, image);
#endif
        else if( MS_RENDERER_RAWDATA(image->format) )
            return msDrawRasterLayerLow(map, layer, image);
#ifdef USE_MING_FLASH
        else if( MS_RENDERER_SWF(image->format) )
            return  msDrawRasterLayerSWF(map, layer, image);
#endif
#ifdef USE_PDF
        else if( MS_RENDERER_PDF(image->format) )
            return  msDrawRasterLayerPDF(map, layer, image);
#endif
        else if( MS_RENDERER_SVG(image->format) )
            return  msDrawRasterLayerSVG(map, layer, image);
    }

    return MS_FAILURE;
}


/**
 * msDrawWMSLayer()
 *
 * Draw a single WMS layer.  
 * Multiple WMS layers in a map are preloaded and then drawn using
 * msDrawWMSLayerLow()
 */

#ifdef USE_WMS_LYR
int msDrawWMSLayer(mapObj *map, layerObj *layer, imageObj *image)
{
    int nStatus = MS_FAILURE;

    if (image && map && layer)
    {
/* ------------------------------------------------------------------
 * Start by downloading the layer
 * ------------------------------------------------------------------ */
        httpRequestObj asReqInfo[2];
        int numReq = 0;

        msHTTPInitRequestObj(asReqInfo, 2);

        if ( msPrepareWMSLayerRequest(1, map, layer,
                                      0, NULL,
                                      asReqInfo, &numReq) == MS_FAILURE  ||
             msOWSExecuteRequests(asReqInfo, numReq, map, MS_TRUE) == MS_FAILURE )
        {
            return MS_FAILURE;
        }

/* ------------------------------------------------------------------
 * Then draw layer based on output format
 * ------------------------------------------------------------------ */
        if( MS_RENDERER_GD(image->format) )
            nStatus = msDrawWMSLayerLow(1, asReqInfo, numReq,
                                        map, layer, image) ;
#ifdef USE_AGG
        else if( MS_RENDERER_AGG(image->format) )
            nStatus = msDrawWMSLayerLow(1, asReqInfo, numReq,
                                        map, layer, image) ;
#endif
        else if( MS_RENDERER_RAWDATA(image->format) )
            nStatus = msDrawWMSLayerLow(1, asReqInfo, numReq,
                                        map, layer, image) ;

#ifdef USE_MING_FLASH                
        else if( MS_RENDERER_SWF(image->format) )
            nStatus = msDrawWMSLayerSWF(1, asReqInfo, numReq,
                                        map, layer, image);
#endif
#ifdef USE_PDF
/* PDF doesn't support WMS yet so return failure
        else if( MS_RENDERER_PDF(image->format) )
        {
            nReturnVal = msDrawWMSLayerPDF(image, labelPnt, string, label, 
                                      fontset, scalefactor);
			nStatus = MS_FAILURE;
		}
*/
#endif
        else
        {
            msSetError(MS_WMSCONNERR, 
                       "Output format '%s' doesn't support WMS layers.", 
                       "msDrawWMSLayer()", image->format->name);
            nStatus = MS_SUCCESS; /* Should we fail if output doesn't support WMS? */
        }
        /* Cleanup */
        msHTTPFreeRequestObj(asReqInfo, numReq);
    }

    return nStatus;
}
#endif


/*
** Function to render an individual shape, the style variable enables/disables the drawing of a single style
** versus a single style. This is necessary when drawing entire layers as proper overlay can only be achived
** through caching. 
*/
int msDrawShape(mapObj *map, layerObj *layer, shapeObj *shape, imageObj *image, int style)
{
  int i,j,c,s;
  rectObj cliprect;
  pointObj annopnt, *point;
  double angle, length = 0.0;
  int bLabelNoClip = MS_FALSE;
  int annocallret = MS_FAILURE; /* Retvals for find-label-pnt calls */
 
  pointObj center; /* circle origin */
  double r; /* circle radius */
  int csz; /* clip over size */
  double buffer;
  int status = MS_FAILURE;
  
  labelPathObj *annopath = NULL; /* Curved label path. Bug #1620 implementation */


  /* set clipping rectangle just a bit larger than the map extent */
/* Steve's original code 
  cliprect.minx = map->extent.minx - 2*map->cellsize; 
  cliprect.miny = map->extent.miny - 2*map->cellsize;
  cliprect.maxx = map->extent.maxx + 2*map->cellsize;
  cliprect.maxy = map->extent.maxy + 2*map->cellsize;
*/

  msDrawStartShape(map, layer, image, shape);

  c = shape->classindex;

  /* Before we do anything else, we will check for a rangeitem.
     If its there, we need to change the style's color to map
     the range to the shape */
  for(s=0; s<layer->class[c]->numstyles; s++) {
    if(layer->class[c]->styles[s]->rangeitem !=  NULL)
      msShapeToRange((layer->class[c]->styles[s]), shape);
  }
  
  /* changed when Tomas added CARTOLINE symbols
   * adjust the clipping rectangle so that clipped polygon shapes with thick lines
   * do not enter the image */
  if(layer->class[c]->numstyles > 0 && layer->class[c]->styles[0] != NULL) {
      double maxsize;
      if(layer->class[c]->styles[0]->size == -1)
          maxsize=MS_MAX(
                  msSymbolGetDefaultSize(map->symbolset.symbol[layer->class[c]->styles[0]->symbol]),
                  layer->class[c]->styles[0]->width);
      else
          maxsize=MS_MAX(
                  layer->class[c]->styles[0]->size,
                  layer->class[c]->styles[0]->width);
      csz = MS_NINT((maxsize*layer->scalefactor)/2.0);
  } else {
      csz = 0;
  }
  cliprect.minx = map->extent.minx - csz*map->cellsize;
  cliprect.miny = map->extent.miny - csz*map->cellsize;
  cliprect.maxx = map->extent.maxx + csz*map->cellsize;
  cliprect.maxy = map->extent.maxy + csz*map->cellsize;

  if(msBindLayerToShape(layer, shape) != MS_SUCCESS)
    return MS_FAILURE; /* error message is set in msBindLayerToShape() */
  
  if(shape->text && (layer->class[c]->label.encoding || layer->class[c]->label.wrap)) {
      char *newtext=msTransformLabelText(&(layer->class[c]->label),shape->text);
      if(!newtext) return MS_FAILURE;
      free(shape->text);
      shape->text = newtext;
  }

  switch(layer->type) {
  case MS_LAYER_CIRCLE:
    if(shape->numlines != 1) return(MS_SUCCESS); /* invalid shape */
    if(shape->line[0].numpoints != 2) return(MS_SUCCESS); /* invalid shape */

    center.x = (shape->line[0].point[0].x + shape->line[0].point[1].x)/2.0;
    center.y = (shape->line[0].point[0].y + shape->line[0].point[1].y)/2.0;
    r = MS_ABS(center.x - shape->line[0].point[0].x);

#ifdef USE_PROJ
    if(layer->project && msProjectionsDiffer(&(layer->projection), &(map->projection)))
      msProjectPoint(&layer->projection, &map->projection, &center);
    else
      layer->project = MS_FALSE;
#endif

    if(layer->transform == MS_TRUE) {
      center.x = MS_MAP2IMAGE_X(center.x, map->extent.minx, map->cellsize);
      center.y = MS_MAP2IMAGE_Y(center.y, map->extent.maxy, map->cellsize);
      r /= map->cellsize;      
    } else
      msOffsetPointRelativeTo(&center, layer);

    /* shade symbol drawing will call outline function if color not set */
    if(style != -1)
      msCircleDrawShadeSymbol(&map->symbolset, image, &center, r, (layer->class[c]->styles[style]), layer->scalefactor);
    else {
      for(s=0; s<layer->class[c]->numstyles; s++)
        msCircleDrawShadeSymbol(&map->symbolset, image, &center, r, (layer->class[c]->styles[s]), layer->scalefactor);
    }

    /* TO DO: need to handle circle annotation */

    break;
  case MS_LAYER_ANNOTATION:
    if(!shape->text) return(MS_SUCCESS); /* nothing to draw */

#ifdef USE_PROJ
    if(layer->project && msProjectionsDiffer(&(layer->projection), &(map->projection)))
       msProjectShape(&layer->projection, &map->projection, shape);
    else
      layer->project = MS_FALSE;
#endif

    switch(shape->type) {
    case(MS_SHAPE_LINE):

      /* No-clip labeling support. For lines we copy the shape, though this is */
      /* inefficient. msPolylineLabelPath/msPolylineLabelPoint require that    */
      /* the shape is transformed prior to calling them                        */
      if(msLayerGetProcessingKey(layer, "LABEL_NO_CLIP") != NULL) {
        shapeObj annoshape;
        bLabelNoClip = MS_TRUE;

        msInitShape(&annoshape);
        msCopyShape(shape, &annoshape);
        msTransformShape(&annoshape, map->extent, map->cellsize, image);

        if(layer->class[c]->label.autofollow == MS_TRUE ) {
          annopath = msPolylineLabelPath(&annoshape, layer->class[c]->label.minfeaturesize, &(map->fontset), shape->text, &(layer->class[c]->label), layer->scalefactor, &status);
        } else {
          annocallret = msPolylineLabelPoint(&annoshape, &annopnt, layer->class[c]->label.minfeaturesize, &angle, &length);
        }

        msFreeShape(&annoshape);
      }
    
      if(layer->transform == MS_TRUE) {
        msClipPolylineRect(shape, cliprect);
        if(shape->numlines == 0) return(MS_SUCCESS);
        msTransformShape(shape, map->extent, map->cellsize, image);
      } else
        msOffsetShapeRelativeTo(shape, layer);

      /* Bug #1620 implementation */
      if ( layer->class[c]->label.autofollow == MS_TRUE ) {
        layer->class[c]->label.position = MS_CC; /* Force all label positions to MS_CC regardless if a path is computed */

        /* Determine the label path if it has not been computed above */
        if(bLabelNoClip == MS_FALSE)
          annopath = msPolylineLabelPath(shape, layer->class[c]->label.minfeaturesize, &(map->fontset), shape->text, &(layer->class[c]->label), layer->scalefactor, &status);

        if( annopath ) {
          labelObj label = layer->class[c]->label;
          
          if(layer->labelcache) {
            if(msAddLabel(map, layer->index, c, shape->index, shape->tileindex, NULL, annopath, shape->text, length, &label) != MS_SUCCESS) return(MS_FAILURE);
          } else {
            /* FIXME: Not sure how this should work with the label path yet */
            /*
              if(MS_VALID_COLOR(layer->class[c]->styles[0]->color)) {
              for(s=0; s<layer->class[c]->numstyles; s++)
              msDrawMarkerSymbol(&map->symbolset, image, &(label_line->point[0]), (layer->class[c]->styles[s]), layer->scalefactor);
              }
            */
            /* FIXME: need to call msDrawTextLineGD() from here eventually */
            /* msDrawLabel(image, label_line->point[0], shape->text, &label, &map->fontset, layer->scalefactor); */

            msFreeLabelPathObj(annopath);
          }
        }
      }

      /* Use regular label algorithm if angle is AUTO or a number, or if ANGLE FOLLOW failed */
      if ( layer->class[c]->label.autofollow == MS_FALSE || (!annopath && status != MS_FAILURE) ) {

        /* Regular labels: Only attempt to find the label point if we have not */
        /* succesfully calculated it previously                                */
        if ((bLabelNoClip == MS_TRUE && annocallret == MS_SUCCESS) ||
            (msPolylineLabelPoint(shape, &annopnt, layer->class[c]->label.minfeaturesize, &angle, &length) == MS_SUCCESS)) {
        labelObj label = layer->class[c]->label;
          
        if(label.angle != 0)
          label.angle -= map->gt.rotation_angle;

        /* Angle derived from line overrides even the rotation value. */
	if(label.autoangle) label.angle = angle;

        if(layer->labelcache) {
            if(msAddLabel(map, layer->index, c, shape->index, shape->tileindex, &annopnt, NULL, shape->text, length, &label) != MS_SUCCESS) return(MS_FAILURE);
	} else {
          if(layer->class[c]->numstyles > 0 && MS_VALID_COLOR(layer->class[c]->styles[0]->color)) {
            for(s=0; s<layer->class[c]->numstyles; s++)
              msDrawMarkerSymbol(&map->symbolset, image, &annopnt, (layer->class[c]->styles[s]), layer->scalefactor);
	  }
	  msDrawLabel(image, annopnt, shape->text, &label, &map->fontset, layer->scalefactor);

        }
      }
      }

      break;
    case(MS_SHAPE_POLYGON):
      /* No-clip labeling support */
      if(shape->text && msLayerGetProcessingKey(layer, "LABEL_NO_CLIP") != NULL) {
        bLabelNoClip = MS_TRUE;
        annocallret = msPolygonLabelPoint(shape, &annopnt, layer->class[c]->label.minfeaturesize);
        annopnt.x = MS_MAP2IMAGE_X(annopnt.x, map->extent.minx, map->cellsize);
        annopnt.y = MS_MAP2IMAGE_Y(annopnt.y, map->extent.maxy, map->cellsize);
      }

      if(layer->transform == MS_TRUE) {
        msClipPolygonRect(shape, cliprect);
        if(shape->numlines == 0) return(MS_SUCCESS);
        msTransformShape(shape, map->extent, map->cellsize, image);
      } else
	msOffsetShapeRelativeTo(shape, layer);

      if ((bLabelNoClip == MS_TRUE && annocallret == MS_SUCCESS) ||
          (msPolygonLabelPoint(shape, &annopnt, layer->class[c]->label.minfeaturesize) == MS_SUCCESS)) {
        labelObj label = layer->class[c]->label;

        if(label.angle != 0)
          label.angle -= map->gt.rotation_angle;

        if(layer->labelcache) {
          if(msAddLabel(map, layer->index, c, shape->index, shape->tileindex, &annopnt, NULL, shape->text, MS_MIN(shape->bounds.maxx-shape->bounds.minx,shape->bounds.maxy-shape->bounds.miny), &label) != MS_SUCCESS) return(MS_FAILURE);
        } else {
	  if(layer->class[c]->numstyles > 0 && MS_VALID_COLOR(layer->class[c]->styles[0]->color)) {
            for(s=0; s<layer->class[c]->numstyles; s++)
	      msDrawMarkerSymbol(&map->symbolset, image, &annopnt, (layer->class[c]->styles[s]), layer->scalefactor);
	  }
	  msDrawLabel(image, annopnt, shape->text, &label, &map->fontset, layer->scalefactor);
        }
      }
      break;
    default: /* points and anything with out a proper type */
      for(j=0; j<shape->numlines;j++) {
	for(i=0; i<shape->line[j].numpoints;i++) {
          labelObj label = layer->class[c]->label;

	  point = &(shape->line[j].point[i]);

	  if(layer->transform == MS_TRUE) {
	    if(!msPointInRect(point, &map->extent)) return(MS_SUCCESS);
	    point->x = MS_MAP2IMAGE_X(point->x, map->extent.minx, map->cellsize);
	    point->y = MS_MAP2IMAGE_Y(point->y, map->extent.maxy, map->cellsize);
	  } else
            msOffsetPointRelativeTo(point, layer);

          if(label.angle != 0)
            label.angle -= map->gt.rotation_angle;

	  if(shape->text) {
	    if(layer->labelcache) {
	      if(msAddLabel(map, layer->index, c, shape->index, shape->tileindex, point, NULL, shape->text, -1, &label) != MS_SUCCESS) return(MS_FAILURE);
	    } else {
	      if(layer->class[c]->numstyles > 0 && MS_VALID_COLOR(layer->class[c]->styles[0]->color)) {
                for(s=0; s<layer->class[c]->numstyles; s++)
	          msDrawMarkerSymbol(&map->symbolset, image, point, (layer->class[c]->styles[s]), layer->scalefactor);
	      }
	      msDrawLabel(image, *point, shape->text, &label, &map->fontset, layer->scalefactor);
	    }
	  }
	}
      }
    }
    break;  /* end MS_LAYER_ANNOTATION */

  case MS_LAYER_POINT:

#ifdef USE_PROJ
    if(layer->project && msProjectionsDiffer(&(layer->projection), &(map->projection)))
      msProjectShape(&layer->projection, &map->projection, shape);
    else
      layer->project = MS_FALSE;
#endif

    for(j=0; j<shape->numlines;j++) {
      for(i=0; i<shape->line[j].numpoints;i++) {
	point = &(shape->line[j].point[i]);

	if(layer->transform == MS_TRUE) {
	  if(!msPointInRect(point, &map->extent)) continue; /* next point */
	  point->x = MS_MAP2IMAGE_X(point->x, map->extent.minx, map->cellsize);
	  point->y = MS_MAP2IMAGE_Y(point->y, map->extent.maxy, map->cellsize);
	} else
          msOffsetPointRelativeTo(point, layer);

	for(s=0; s<layer->class[c]->numstyles; s++)
  	  msDrawMarkerSymbol(&map->symbolset, image, point, (layer->class[c]->styles[s]), layer->scalefactor);

	if(shape->text) {
          labelObj label = layer->class[c]->label;

          if(label.angle != 0)
            label.angle -= map->gt.rotation_angle;

	  if(layer->labelcache) {
	    if(msAddLabel(map, layer->index, c, shape->index, shape->tileindex, point, NULL, shape->text, -1, &label) != MS_SUCCESS) return(MS_FAILURE);
	  } else
	    msDrawLabel(image, *point, shape->text, &label, &map->fontset, layer->scalefactor);
	}
      }
    }
    break; /* end MS_LAYER_POINT */

  case MS_LAYER_LINE:
    if(shape->type != MS_SHAPE_POLYGON && shape->type != MS_SHAPE_LINE){
      msSetError(MS_MISCERR, "Only polygon or line shapes can be drawn using a line layer definition.", "msDrawShape()");
      return(MS_FAILURE);
    }

#ifdef USE_PROJ
    if(layer->project && msProjectionsDiffer(&(layer->projection), &(map->projection)))
      msProjectShape(&layer->projection, &map->projection, shape);
    else
      layer->project = MS_FALSE;
#endif

    /* No-clip labeling support. For lines we copy the shape, though this is */
    /* inefficient. msPolylineLabelPath/msPolylineLabelPoint require that    */
    /* the shape is transformed prior to calling them                        */
    if(shape->text && msLayerGetProcessingKey(layer, "LABEL_NO_CLIP") != NULL) {
      shapeObj annoshape;
      bLabelNoClip = MS_TRUE;

      msInitShape(&annoshape);
      msCopyShape(shape, &annoshape);
      msTransformShape(&annoshape, map->extent, map->cellsize, image);

      if(layer->class[c]->label.autofollow == MS_TRUE) {
        annopath = msPolylineLabelPath(&annoshape, layer->class[c]->label.minfeaturesize, &(map->fontset), shape->text, &(layer->class[c]->label), layer->scalefactor, &status);
      } else {
        annocallret = msPolylineLabelPoint(&annoshape, &annopnt, layer->class[c]->label.minfeaturesize, &angle, &length);
      }

      msFreeShape(&annoshape);
    }


    if(layer->transform == MS_TRUE) {
      msClipPolylineRect(shape, cliprect);
      if(shape->numlines == 0) return(MS_SUCCESS);
      msTransformShape(shape, map->extent, map->cellsize, image);
    } else
      msOffsetShapeRelativeTo(shape, layer);
 
    if(style != -1)
      msDrawLineSymbol(&map->symbolset, image, shape, (layer->class[c]->styles[style]), layer->scalefactor);
    else {
      for(s=0; s<layer->class[c]->numstyles; s++)
        msDrawLineSymbol(&map->symbolset, image, shape, (layer->class[c]->styles[s]), layer->scalefactor);
    }

    if(shape->text) {

      /* Bug #1620 implementation */
      if(layer->class[c]->label.autofollow == MS_TRUE) {
        layer->class[c]->label.position = MS_CC; /* Force all label positions to MS_CC regardless if a path is computed */

        if (bLabelNoClip == MS_FALSE)
          annopath = msPolylineLabelPath(shape, layer->class[c]->label.minfeaturesize, &(map->fontset), shape->text, &(layer->class[c]->label), layer->scalefactor, &status);

        if(annopath) {
          labelObj label = layer->class[c]->label;

          if(layer->labelcache) {
            if(msAddLabel(map, layer->index, c, shape->index, shape->tileindex, NULL, annopath, shape->text, length, &label) != MS_SUCCESS) return(MS_FAILURE);
          } else {
            /* FIXME: need to call msDrawTextLineGD() from here eventually */
            /* msDrawLabel(image, label_line->point[0], shape->text, &label, &map->fontset, layer->scalefactor); */
            
            msFreeLabelPathObj(annopath);
          }
        }
      }

      /* Use regular label algorithm if angle is AUTO or a number, or if ANGLE FOLLOW failed */
      if ( layer->class[c]->label.autofollow == MS_FALSE || (!annopath && status != MS_FAILURE) ) {

      if((bLabelNoClip == MS_TRUE && annocallret == MS_SUCCESS) || 
         (msPolylineLabelPoint(shape, &annopnt, layer->class[c]->label.minfeaturesize, &angle, &length) == MS_SUCCESS)) {
        labelObj label = layer->class[c]->label;

        if(label.angle != 0)
          label.angle -= map->gt.rotation_angle;

	if(label.autoangle) label.angle = angle;

	if(layer->labelcache) {
            if(msAddLabel(map, layer->index, c, shape->index, shape->tileindex, &annopnt, NULL, shape->text, length, &label) != MS_SUCCESS) return(MS_FAILURE);
	} else
          msDrawLabel(image, annopnt, shape->text, &label, &map->fontset, layer->scalefactor);
      }
    }
    }
    break;

  case MS_LAYER_POLYGON:
    if(shape->type != MS_SHAPE_POLYGON){
      msSetError(MS_MISCERR, "Only polygon shapes can be drawn using a POLYGON layer definition.", "msDrawShape()");
      return(MS_FAILURE);
    }

#ifdef USE_PROJ
    if(layer->project && msProjectionsDiffer(&(layer->projection), &(map->projection))) {
      if(msProjectShape(&layer->projection, &map->projection, shape) == MS_FAILURE ) {
#ifdef notdef 
        msSetError(MS_PROJERR, "Reprojecting a shape failed.", "msDrawShape()" );
        return MS_FAILURE;
#else
        return MS_SUCCESS;
#endif
      }
    } else
      layer->project = MS_FALSE;
#endif

    /* No-clip labeling support */
    if(shape->text && msLayerGetProcessingKey(layer, "LABEL_NO_CLIP") != NULL) {
      bLabelNoClip = MS_TRUE;
      annocallret = msPolygonLabelPoint(shape, &annopnt, layer->class[c]->label.minfeaturesize);
      annopnt.x = MS_MAP2IMAGE_X(annopnt.x, map->extent.minx, map->cellsize);
      annopnt.y = MS_MAP2IMAGE_Y(annopnt.y, map->extent.maxy, map->cellsize);
    }

    if(layer->transform == MS_TRUE) {
      /*
       * add a small buffer around the cliping rectangle to
       * avoid lines around the edges : Bug 179
       */
      buffer = (map->extent.maxx -  map->extent.minx)/map->width;
      buffer = buffer *2;
      cliprect.minx -= buffer;
      cliprect.miny -= buffer;
      cliprect.maxx += buffer;
      cliprect.maxy += buffer;

      msClipPolygonRect(shape, cliprect);
      if(shape->numlines == 0) return(MS_SUCCESS);
      msTransformShape(shape, map->extent, map->cellsize, image);
    } else
      msOffsetShapeRelativeTo(shape, layer);
 
    for(s=0; s<layer->class[c]->numstyles; s++)
      msDrawShadeSymbol(&map->symbolset, image, shape, (layer->class[c]->styles[s]), layer->scalefactor);

    if(shape->text) {
      if((bLabelNoClip == MS_TRUE && annocallret == MS_SUCCESS) ||
         (msPolygonLabelPoint(shape, &annopnt, layer->class[c]->label.minfeaturesize) == MS_SUCCESS)) {
        labelObj label = layer->class[c]->label;

        if(label.angle != 0)
          label.angle -= map->gt.rotation_angle;

	if(layer->labelcache) {
	  if(msAddLabel(map, layer->index, c, shape->index, shape->tileindex, &annopnt, NULL, shape->text, MS_MIN(shape->bounds.maxx-shape->bounds.minx,shape->bounds.maxy-shape->bounds.miny), &label) != MS_SUCCESS) return(MS_FAILURE);
	} else
	  msDrawLabel(image, annopnt, shape->text, &label, &map->fontset, layer->scalefactor);
      }
    }
    break;
  default:
    msSetError(MS_MISCERR, "Unknown layer type.", "msDrawShape()");
    return(MS_FAILURE);
  }


  return(MS_SUCCESS);
}

/*
** Function to render an individual point, used as a helper function for mapscript only. Since a point
** can't carry attributes you can't do attribute based font size or angle.
*/
int msDrawPoint(mapObj *map, layerObj *layer, pointObj *point, imageObj *image, 
                int classindex, char *labeltext)
{
  int s;
  char *newtext;
  classObj *theclass=layer->class[classindex];
  labelObj *label=&(theclass->label);
 
#ifdef USE_PROJ
  if(layer->project && msProjectionsDiffer(&(layer->projection), &(map->projection)))
    msProjectPoint(&layer->projection, &map->projection, point);
  else
    layer->project = MS_FALSE;
#endif
  
  /*apply wrap character and encoding to the label text*/
  if(labeltext &&(label->encoding || label->wrap))
      newtext = msTransformLabelText(label,labeltext);
  else
      newtext=labeltext;
  switch(layer->type) {
  case MS_LAYER_ANNOTATION:
    if(layer->transform == MS_TRUE) {
      if(!msPointInRect(point, &map->extent)) return(0);
      point->x = MS_MAP2IMAGE_X(point->x, map->extent.minx, map->cellsize);
      point->y = MS_MAP2IMAGE_Y(point->y, map->extent.maxy, map->cellsize);
    } else
      msOffsetPointRelativeTo(point, layer);

    if(labeltext) {
      if(layer->labelcache) {
        if(msAddLabel(map, layer->index, classindex, -1, -1, point, NULL, newtext, -1,NULL) != MS_SUCCESS) return(MS_FAILURE);
      } else {
	if(theclass->numstyles > 0 && MS_VALID_COLOR(theclass->styles[0]->color)) {
          for(s=0; s<theclass->numstyles; s++)
  	    msDrawMarkerSymbol(&map->symbolset, image, point, (theclass->styles[s]), layer->scalefactor);
	}
	msDrawLabel(image, *point, newtext, label, &map->fontset, layer->scalefactor);
      }
    }
    break;

  case MS_LAYER_POINT:
    if(layer->transform == MS_TRUE) {
      if(!msPointInRect(point, &map->extent)) return(0);
      point->x = MS_MAP2IMAGE_X(point->x, map->extent.minx, map->cellsize);
      point->y = MS_MAP2IMAGE_Y(point->y, map->extent.maxy, map->cellsize);
    } else
      msOffsetPointRelativeTo(point, layer);

    for(s=0; s<theclass->numstyles; s++)
      msDrawMarkerSymbol(&map->symbolset, image, point, (theclass->styles[s]), layer->scalefactor);

    if(labeltext) {
      if(layer->labelcache) {
        if(msAddLabel(map, layer->index, classindex, -1, -1, point, NULL, newtext, -1,NULL) != MS_SUCCESS) return(MS_FAILURE);
      } else
	msDrawLabel(image, *point, newtext, label, &map->fontset, layer->scalefactor);
    }
    break;
  default:
    break; /* don't do anything with layer of other types */
  }
  
  if(newtext!=labeltext) /*free the transformed text if necessary*/
    free(newtext);

  return(MS_SUCCESS); /* all done, no cleanup */
}


/************************************************************************/
/*                          msCircleDrawLineSymbol                      */
/*                                                                      */
/*      Note : the map parameter is only used to be able to converet    */
/*      the color index to rgb values.                                  */
/************************************************************************/
void msCircleDrawLineSymbol(symbolSetObj *symbolset, imageObj *image, pointObj *p, double r, styleObj *style, double scalefactor)
{
    if (image)
    {
        if( MS_RENDERER_GD(image->format) )
            msCircleDrawLineSymbolGD(symbolset, image->img.gd, p, r, style, scalefactor);
#ifdef USE_AGG
        else if( MS_RENDERER_AGG(image->format) )
            msCircleDrawLineSymbolAGG(symbolset, image, p, r, style, scalefactor);
#endif
	else if( MS_RENDERER_IMAGEMAP(image->format) )
            msCircleDrawLineSymbolIM(symbolset, image, p, r, style, scalefactor);
        else
            msSetError(MS_MISCERR, "Unknown image type", 
                       "msCircleDrawLineSymbol()");
    }
}

void msCircleDrawShadeSymbol(symbolSetObj *symbolset, imageObj *image, pointObj *p, double r, styleObj *style, double scalefactor)
{
    if (image)
    {
        if( MS_RENDERER_GD(image->format) )
            msCircleDrawShadeSymbolGD(symbolset, image->img.gd, p, r, style, scalefactor);
#ifdef USE_AGG
        else if( MS_RENDERER_AGG(image->format) )
            msCircleDrawShadeSymbolAGG(symbolset, image, p, r, style, scalefactor);
#endif
	else if( MS_RENDERER_IMAGEMAP(image->format) )
            msCircleDrawShadeSymbolIM(symbolset, image, p, r, style, scalefactor);
              
        else
             msSetError(MS_MISCERR, "Unknown image type", 
                        "msCircleDrawShadeSymbol()"); 
    }
}


void msDrawMarkerSymbol(symbolSetObj *symbolset,imageObj *image, pointObj *p, styleObj *style, double scalefactor)
{    
   if (image)
   {
       if( MS_RENDERER_GD(image->format) )
           msDrawMarkerSymbolGD(symbolset, image->img.gd, p, style, scalefactor);
#ifdef USE_AGG
       else if( MS_RENDERER_AGG(image->format) )
           msDrawMarkerSymbolAGG(symbolset, image, p, style, scalefactor);
#endif
       else if( MS_RENDERER_IMAGEMAP(image->format) )
           msDrawMarkerSymbolIM(symbolset, image, p, style, scalefactor);
       
#ifdef USE_MING_FLASH              
       else if( MS_RENDERER_SWF(image->format) )
           msDrawMarkerSymbolSWF(symbolset, image, p, style, scalefactor);
#endif
#ifdef USE_PDF
       else if( MS_RENDERER_PDF(image->format) )
           msDrawMarkerSymbolPDF(symbolset, image, p, style, scalefactor);
#endif
       else if( MS_RENDERER_SVG(image->format) )
           msDrawMarkerSymbolSVG(symbolset, image, p, style, scalefactor);

    }
}

void msDrawLineSymbol(symbolSetObj *symbolset, imageObj *image, shapeObj *p, styleObj *style, double scalefactor)
{
    if (image)
    {
        if( MS_RENDERER_GD(image->format) )
            msDrawLineSymbolGD(symbolset, image->img.gd, p, style, scalefactor);
#ifdef USE_AGG
        else if( MS_RENDERER_AGG(image->format) )
            msDrawLineSymbolAGG(symbolset, image, p, style, scalefactor);
#endif
	else if( MS_RENDERER_IMAGEMAP(image->format) )
            msDrawLineSymbolIM(symbolset, image, p, style, scalefactor);

#ifdef USE_MING_FLASH
        else if( MS_RENDERER_SWF(image->format) )
            msDrawLineSymbolSWF(symbolset, image, p,  style, scalefactor);
#endif
#ifdef USE_PDF
        else if( MS_RENDERER_PDF(image->format) )
            msDrawLineSymbolPDF(symbolset, image, p,  style, scalefactor);
#endif
        else if( MS_RENDERER_SVG(image->format) )
            msDrawLineSymbolSVG(symbolset, image, p,  style, scalefactor);

    }
}

void msDrawShadeSymbol(symbolSetObj *symbolset, imageObj *image, shapeObj *p, styleObj *style, double scalefactor)
{
    if (image)
    {
        if( MS_RENDERER_GD(image->format) )
            msDrawShadeSymbolGD(symbolset, image->img.gd, p, style, scalefactor);
#ifdef USE_AGG
        else if( MS_RENDERER_AGG(image->format) )
            msDrawShadeSymbolAGG(symbolset, image, p, style, scalefactor);
#endif
	else if( MS_RENDERER_IMAGEMAP(image->format) )
            msDrawShadeSymbolIM(symbolset, image, p, style, scalefactor);

#ifdef USE_MING_FLASH
        else if( MS_RENDERER_SWF(image->format) )
            msDrawShadeSymbolSWF(symbolset, image, p, style, scalefactor);
#endif
#ifdef USE_PDF
        else if( MS_RENDERER_PDF(image->format) )
            msDrawShadeSymbolPDF(symbolset, image, p, style, scalefactor);
#endif
        else if( MS_RENDERER_SVG(image->format) )
            msDrawShadeSymbolSVG(symbolset, image, p, style, scalefactor);
    }
}

int msDrawLabel(imageObj *image, pointObj labelPnt, char *string, 
                labelObj *label, fontSetObj *fontset, double scalefactor)
{
  if(!string)
    return(0); /* not an error, just don't want to do anything */

  if(strlen(string) == 0)
    return(0); /* not an error, just don't want to do anything */


/* ======================================================================= */
/*      TODO : This is a temporary hack to call the drawlableswf directly. */
/*      Normally the only functions that should be wrapped here is         */
/*      draw_text. We did this since msGetLabelSize has not yet been       */
/*      implemented for MING FDB fonts.                                    */
/* ======================================================================= */

#ifdef USE_MING_FLASH
  if ( MS_RENDERER_SWF(image->format) )
      return msDrawLabelSWF(image, labelPnt, string, label, fontset, scalefactor);
#endif
  
  
 if(label->position != MS_XY) {
    pointObj p;
    rectObj r;

    if(msGetLabelSize(image,string, label, &r, fontset, scalefactor, MS_FALSE) == -1) return(-1);
    p = get_metrics(&labelPnt, label->position, r, label->offsetx, label->offsety, label->angle, 0, NULL);
    msDrawText(image, p, string, label, fontset, scalefactor); /* actually draw the label */
  } else {
    labelPnt.x += label->offsetx;
    labelPnt.y += label->offsety;
    msDrawText(image, labelPnt, string, label, fontset, scalefactor); /* actually draw the label */
  }

  return(0);
}


int msDrawText(imageObj *image, pointObj labelPnt, char *string, labelObj *label, fontSetObj *fontset, double scalefactor)
{
    int nReturnVal = -1;

    if (image)
    {
        if( MS_RENDERER_GD(image->format) )
            nReturnVal = msDrawTextGD(image->img.gd, labelPnt, string, 
                                     label, fontset, scalefactor);
#ifdef USE_AGG
        else if( MS_RENDERER_AGG(image->format) )
            nReturnVal = msDrawTextAGG(image, labelPnt, string, 
                                     label, fontset, scalefactor);
#endif
	else if( MS_RENDERER_IMAGEMAP(image->format) )
            nReturnVal = msDrawTextIM(image, labelPnt, string, 
                                     label, fontset, scalefactor);
#ifdef USE_MING_FLASH
        else if( MS_RENDERER_SWF(image->format) )
            nReturnVal = draw_textSWF(image, labelPnt, string, label, 
                                      fontset, scalefactor); 
#endif
#ifdef USE_PDF
        else if( MS_RENDERER_PDF(image->format) )
            nReturnVal = msDrawTextPDF(image, labelPnt, string, label, 
                                      fontset, scalefactor); 
#endif
        else if( MS_RENDERER_SVG(image->format) )
            nReturnVal = msDrawTextSVG(image, labelPnt, string, label, 
                                      fontset, scalefactor); 
    }

    return nReturnVal;
}

int msDrawTextLine(imageObj *image, char *string, labelObj *label, labelPathObj *labelpath, fontSetObj *fontset, double scalefactor) 
{
    int nReturnVal = -1;

    if (image)
    {
        if( MS_RENDERER_GD(image->format) )
            nReturnVal = msDrawTextLineGD(image->img.gd, string, 
                    label, labelpath, fontset, scalefactor);
#ifdef USE_AGG
        else if( MS_RENDERER_AGG(image->format) )
            nReturnVal = msDrawTextLineAGG(image, string, 
                    label, labelpath, fontset, scalefactor);
#endif
    }

    return nReturnVal;
}

int msDrawLabelCache(imageObj *image, mapObj *map)
{
    int nReturnVal = MS_SUCCESS;
    if (image)
    {
        if( MS_RENDERER_GD(image->format) || MS_RENDERER_AGG(image->format)) {          
            pointObj p;
            int i, l, priority;
            int oldAlphaBlending=0;
            rectObj r;
            shapeObj billboard;
            lineObj billboard_line;
            pointObj billboard_points[5];
            labelCacheMemberObj *cachePtr=NULL;
            layerObj *layerPtr=NULL;
            labelObj *labelPtr=NULL;

            int marker_width, marker_height;
            int marker_offset_x, marker_offset_y;
            rectObj marker_rect;
            int map_edge_buffer=0;
            const char *value;
#ifdef USE_AGG
            if( MS_RENDERER_AGG(image->format) ) 
                msAlphaGD2AGG(image);
            else
#endif
            {/* bug 490 - switch on alpha blending for label cache */
                oldAlphaBlending = image->img.gd->alphaBlendingFlag;
                gdImageAlphaBlending( image->img.gd, 1);
            }
            
            billboard.numlines=1;
            billboard.line=&billboard_line;
            billboard.line->numpoints=5;
            billboard.line->point=billboard_points;
            /* Look for labelcache_map_edge_buffer map metadata
             * If set then the value defines a buffer (in pixels) along the edge of the
             * map image where labels can't fall
             */
            if ((value = msLookupHashTable(&(map->web.metadata),
                    "labelcache_map_edge_buffer")) != NULL)
            {
                map_edge_buffer = atoi(value);
                if (map->debug)
                    msDebug("msDrawLabelCache(): labelcache_map_edge_buffer = %d\n", map_edge_buffer);
            }

            

            for(priority=MS_MAX_LABEL_PRIORITY-1; priority>=0; priority--) {
                labelCacheSlotObj *cacheslot;
                cacheslot = &(map->labelcache.slots[priority]);

                for(l=cacheslot->numlabels-1; l>=0; l--) {

                    cachePtr = &(cacheslot->labels[l]); /* point to right spot in the label cache */

                    layerPtr = (GET_LAYER(map, cachePtr->layerindex)); /* set a couple of other pointers, avoids nasty references */
                    labelPtr = &(cachePtr->label);

                    if(!cachePtr->text || strlen(cachePtr->text) == 0)
                        continue; /* not an error, just don't want to do anything */

                    if(msGetLabelSize(image,cachePtr->text, labelPtr, &r, &(map->fontset), layerPtr->scalefactor, MS_TRUE) == -1)
                        return(-1);

                    if(labelPtr->autominfeaturesize && ((r.maxx-r.minx) > cachePtr->featuresize))
                        continue; /* label too large relative to the feature */

                    marker_offset_x = marker_offset_y = 0; /* assume no marker */
                    if((layerPtr->type == MS_LAYER_ANNOTATION && cachePtr->numstyles > 0) || layerPtr->type == MS_LAYER_POINT) { /* there *is* a marker       */

                        /* TO DO: at the moment only checks the bottom style, perhaps should check all of them */
                        if(msGetMarkerSize(&map->symbolset, &(cachePtr->styles[0]), &marker_width, &marker_height, layerPtr->scalefactor) != MS_SUCCESS)
                            return(-1);

                        marker_offset_x = MS_NINT(marker_width/2.0);
                        marker_offset_y = MS_NINT(marker_height/2.0);      

                        marker_rect.minx = MS_NINT(cachePtr->point.x - .5 * marker_width);
                        marker_rect.miny = MS_NINT(cachePtr->point.y - .5 * marker_height);
                        marker_rect.maxx = marker_rect.minx + (marker_width-1);
                        marker_rect.maxy = marker_rect.miny + (marker_height-1); 
                    }

                    if(labelPtr->position == MS_AUTO) {
                      int first_pos, pos, last_pos;

                      if(labelPtr->type == MS_LAYER_LINE) {                        
                        first_pos = MS_UC; /* There are three possible positions: UC, CC, LC */
                        last_pos = MS_CC;
                      } else {
                        first_pos = MS_UL; /* There are 8 possible outer positions: UL, LR, UR, LL, CR, CL, UC, LC */
                        last_pos = MS_LC;
                      }

                      for(pos = first_pos; pos <= last_pos; pos++) {
                        msFreeShape(cachePtr->poly);
                        cachePtr->status = MS_TRUE; /* assume label *can* be drawn */

                        p = get_metrics(&(cachePtr->point), pos, r, (marker_offset_x + labelPtr->offsetx), (marker_offset_y + labelPtr->offsety), labelPtr->angle, labelPtr->buffer, cachePtr->poly);
                        if(layerPtr->type == MS_LAYER_ANNOTATION && cachePtr->numstyles > 0)
                          msRectToPolygon(marker_rect, cachePtr->poly); /* save marker bounding polygon */

                        /* Compare against image bounds, rendered labels and markers (sets cachePtr->status) */
                        msTestLabelCacheCollisions(&(map->labelcache), labelPtr, image->width, image->height, 
                        labelPtr->buffer + map_edge_buffer, cachePtr, priority, l);

                        if(cachePtr->status) /* found a suitable place for this label */ {
                          if(MS_VALID_COLOR(labelPtr->backgroundcolor))
                            get_metrics_line(&(cachePtr->point), pos, r, (marker_offset_x + labelPtr->offsetx), (marker_offset_y + labelPtr->offsety), labelPtr->angle, 1, billboard.line);
                          break;
                        }

                      } /* next position */

                      if(labelPtr->force) cachePtr->status = MS_TRUE; /* draw in spite of collisions based on last position, need a *best* position */

                    } else {

                      cachePtr->status = MS_TRUE; /* assume label *can* be drawn */

		      if(cachePtr->labelpath ) {

			/* Copy the bounds into the cache's polygon */
			msCopyShape(&(cachePtr->labelpath->bounds), cachePtr->poly);
		        msFreeShape(&(cachePtr->labelpath->bounds));

		        /* Compare against image bounds, rendered labels and markers (sets cachePtr->status) */
		        msTestLabelCacheCollisions(&(map->labelcache), labelPtr, image->width, image->height, labelPtr->buffer + map_edge_buffer, cachePtr, priority, l);

                      } else {

                        if(labelPtr->position == MS_CC) { /* don't need the marker_offset */
                          p = get_metrics(&(cachePtr->point), labelPtr->position, r, labelPtr->offsetx, labelPtr->offsety, labelPtr->angle, labelPtr->buffer, cachePtr->poly);
                          if(MS_VALID_COLOR(labelPtr->backgroundcolor))
                            get_metrics_line(&(cachePtr->point), labelPtr->position, r, labelPtr->offsetx, labelPtr->offsety, labelPtr->angle, 1, billboard.line);
                        } else {
                          p = get_metrics(&(cachePtr->point), labelPtr->position, r, (marker_offset_x + labelPtr->offsetx), (marker_offset_y + labelPtr->offsety), labelPtr->angle, labelPtr->buffer, cachePtr->poly);
                          if(MS_VALID_COLOR(labelPtr->backgroundcolor))
                            get_metrics_line(&(cachePtr->point), labelPtr->position, r, (marker_offset_x + labelPtr->offsetx), (marker_offset_y + labelPtr->offsety), labelPtr->angle, 1, billboard.line);
                        }
                        if(layerPtr->type == MS_LAYER_ANNOTATION && cachePtr->numstyles > 0)
                          msRectToPolygon(marker_rect, cachePtr->poly); /* save marker bounding polygon, part of overlap tests */

                        if(!labelPtr->force) { /* no need to check anything else */
                          /* Compare against image bounds, rendered labels and markers (sets cachePtr->status) */
                          msTestLabelCacheCollisions(&(map->labelcache), labelPtr, image->width, image->height, labelPtr->buffer + map_edge_buffer, cachePtr, priority, l);
                        }
		      }
                    } /* end position if-then-else */

                    /* imagePolyline(img, cachePtr->poly, 1, 0, 0); */

                    if(!cachePtr->status)
                      continue; /* next label */

                    if(layerPtr->type == MS_LAYER_ANNOTATION && cachePtr->numstyles > 0) { /* need to draw a marker */
                      for(i=0; i<cachePtr->numstyles; i++)
                        msDrawMarkerSymbol(&map->symbolset, image, &(cachePtr->point), &(cachePtr->styles[i]), layerPtr->scalefactor);
                    }

                    if(MS_VALID_COLOR(labelPtr->backgroundcolor)) {
                        styleObj style;
                        initStyle(&style);                    
                        if(MS_VALID_COLOR(labelPtr->backgroundshadowcolor)) {
                            MS_COPYCOLOR(&(style.color),&(labelPtr->backgroundshadowcolor));
                            style.offsetx=labelPtr->backgroundshadowsizex;
                            style.offsety=labelPtr->backgroundshadowsizey;
                            msDrawShadeSymbol(&map->symbolset,image,&billboard,&style,1);
                            style.offsetx=0;
                            style.offsety=0;
                        }
                        MS_COPYCOLOR(&(style.color),&(labelPtr->backgroundcolor));
                        msDrawShadeSymbol(&map->symbolset,image,&billboard,&style,1);
                    }

                    if ( cachePtr->labelpath ) {
                        msDrawTextLine(image, cachePtr->text, labelPtr, cachePtr->labelpath, &(map->fontset), layerPtr->scalefactor); /* Draw the curved label */
                    } else {
                        msDrawText(image, p, cachePtr->text, labelPtr, &(map->fontset), layerPtr->scalefactor); /* actually draw the label */
                    }

                } /* next label */
            } /* next priority */

            /* bug 490 - alpha blending back */
            if(MS_RENDERER_GD(image->format))
                gdImageAlphaBlending( image->img.gd, oldAlphaBlending);

            return(0);
        } /*end test for gd or agg renderers*/
	else if( MS_RENDERER_IMAGEMAP(image->format) )
            nReturnVal = msDrawLabelCacheIM(image, map);

#ifdef USE_MING_FLASH
        else if( MS_RENDERER_SWF(image->format) )
            nReturnVal = msDrawLabelCacheSWF(image, map);
#endif
#ifdef USE_PDF
        else if( MS_RENDERER_PDF(image->format) )
            nReturnVal = msDrawLabelCachePDF(image, map);
#endif
        else if( MS_RENDERER_SVG(image->format) )
            nReturnVal = msDrawLabelCacheSVG(image, map);
    }

    return nReturnVal;
}

/**
 * Generic function to tell the underline device that layer 
 * drawing is stating
 */

void msImageStartLayer(mapObj *map, layerObj *layer, imageObj *image)
{
    if (image)
    {
        if( MS_RENDERER_IMAGEMAP(image->format) )
            msImageStartLayerIM(map, layer, image);
#ifdef USE_MING_FLASH
        if( MS_RENDERER_SWF(image->format) )
            msImageStartLayerSWF(map, layer, image);
#endif
#ifdef USE_PDF
        if( MS_RENDERER_PDF(image->format) )
            msImageStartLayerPDF(map, layer, image); 
#endif
        if( MS_RENDERER_SVG(image->format) )
            msImageStartLayerSVG(map, layer, image);
    }
}


/**
 * Generic function to tell the underline device that layer 
 * drawing is ending
 */

void msImageEndLayer(mapObj *map, layerObj *layer, imageObj *image)
{
}

/**
 * Generic function to tell the underline device that shape 
 * drawing is stating
 */

void msDrawStartShape(mapObj *map, layerObj *layer, imageObj *image,
                      shapeObj *shape)
{
    if (image)
    {

#ifdef USE_MING_FLASH
        if( MS_RENDERER_SWF(map->outputformat) )
            msDrawStartShapeSWF(map, layer, image, shape);
#endif
#ifdef USE_PDF
        if( MS_RENDERER_PDF(map->outputformat) )
            msDrawStartShapePDF(map, layer, image, shape);
#endif
               
    }
}


/**
 * Generic function to tell the underline device that shape 
 * drawing is ending
 */

void msDrawEndShape(mapObj *map, layerObj *layer, imageObj *image, 
                    shapeObj *shape)
{
}
/**
 * take the value from the shape and use it to change the 
 * color in the style to match the range map
 */
int msShapeToRange(styleObj *style, shapeObj *shape)
{
  double fieldVal;
  char* fieldStr;

  /*first, get the value of the rangeitem, which should*/
  /*evaluate to a double*/
  fieldStr = shape->values[style->rangeitemindex];
  if (fieldStr == NULL) /*if there's not value, bail*/
    {
      return MS_FAILURE;
    }
  fieldVal = 0.0;
  fieldVal = atof(fieldStr); /*faith that it's ok -- */
  /*should switch to strtod*/
  return msValueToRange(style, fieldVal);
}

/**
 * Allow direct mapping of a value so that mapscript can use the 
 * Ranges.  The styls passed in is updated to reflect the right color 
 * based on the fieldVal
 */
int msValueToRange(styleObj *style, double fieldVal)
{
  double range;
  double scaledVal;

  range = style->maxvalue - style->minvalue;
  scaledVal = (fieldVal - style->minvalue)/range;
  
  /*At this point, we know where on the range we need to be*/
  /*However, we don't know how to map it yet, since RGB(A) can */
  /*Go up or down*/
  style->color.red = (int)(MS_MAX(0,(MS_MIN(255, (style->mincolor.red + ((style->maxcolor.red - style->mincolor.red) * scaledVal))))));
  style->color.green = (int)(MS_MAX(0,(MS_MIN(255,(style->mincolor.green + ((style->maxcolor.green - style->mincolor.green) * scaledVal))))));
  style->color.blue = (int)(MS_MAX(0,(MS_MIN(255,(style->mincolor.blue + ((style->maxcolor.blue - style->mincolor.blue) * scaledVal))))));
  style->color.pen = MS_PEN_UNSET; /*so it will recalculate pen*/

  /*( "msMapRange(): %i %i %i", style->color.red , style->color.green, style->color.blue);*/

#if ALPHACOLOR_ENABLED
  /*NO ALPHA RANGE YET  style->color.alpha = style->mincolor.alpha + ((style->maxcolor.alpha - style->mincolor.alpha) * scaledVal);*/
#endif

  return MS_SUCCESS;
}
