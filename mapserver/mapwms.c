/******************************************************************************
 *
 * Project:  MapServer
 * Purpose:  OpenGIS Web Mapping Service support implementation.
 * Author:   Steve Lime and the MapServer team.
 *
 ******************************************************************************
 * Copyright (c) 1996-2004 Regents of the University of Minnesota.
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
 ******************************************************************************
 *
 * $Log$
 * Revision 1.159  2005/01/24 15:46:20  assefa
 * Error : missing index in the source.
 *
 * Revision 1.158  2005/01/14 05:03:01  frank
 * fixed style capabilities (use msIO_fprintf) generation per Bug 1152
 *
 * Revision 1.157  2004/11/29 21:31:56  dan
 * Fixed WMS GetCapabilities 1.1.0 crash when wms_style_<...>_legendurl_*
 * metadata were used (bug 1096)
 *
 * Revision 1.156  2004/11/26 17:24:55  assefa
 * Url encode Service online resource (Bug 1093).
 *
 * Revision 1.155  2004/11/24 00:00:13  assefa
 * SLD rasters was failing when there is Spatial Filter into it (Bug 1087).
 *
 * Revision 1.154  2004/11/17 23:53:07  assefa
 * Advertize only gd and gdal formats for wms capabilities (Bug 455).
 *
 * Revision 1.153  2004/11/17 17:29:18  dan
 * Fixed GetLegendGraphic in WMS Capabilities that were missing the '?'
 * or '&' separator if it was not included in wms_onlineresource (bug 1065)
 *
 * Revision 1.152  2004/11/16 21:57:49  dan
 * Final pass at updating WMS/WFS client/server interfaces to lookup "ows_*"
 * metadata in addition to default "wms_*"/"wfs_*" metadata (bug 568)
 *
 * Revision 1.151  2004/11/16 20:19:39  dan
 * First pass at supporting "ows_*" metadata names in WMS/WFS (bug 568)
 *
 * Revision 1.150  2004/11/16 18:49:44  dan
 * Added ows_service_onlineresource metadata for WMS/WFS to distinguish between
 * service onlineresource and GetMap/Capabilities onlineresource (bug 375)
 *
 * Revision 1.149  2004/11/11 14:41:27  assefa
 * Send a warning if the layer ststus is set to default (Bug 638).
 *
 * Revision 1.148  2004/11/11 01:03:33  assefa
 * You can now use wms_group_abstarct metedata for capabilities output (Bug 754)
 *
 * Revision 1.147  2004/11/10 22:49:23  assefa
 * Send warning for "invalid" layers in the capabilities document (Bug 646).
 *
 * Revision 1.146  2004/11/10 19:00:33  assefa
 * Output warning in capabilities document if layer,group,map names have
 * space in them. (Bug 486).
 *
 * Revision 1.145  2004/11/09 18:31:42  assefa
 * Use msOWSPrintURLType for GetLegendGraphic request in the capabilities.
 * (Bug 1011).
 *
 * Revision 1.144  2004/11/09 16:42:47  hobu
 * conditionally include <process.h> on the windows
 * platform for getpid
 *
 * Revision 1.143  2004/11/05 16:57:26  assefa
 * Add test for supported formats in getLegendGraphic (Bug 1030).
 *
 * Revision 1.142  2004/11/05 16:27:01  assefa
 * GetLenendGraphic only advertize GD formats.
 *
 * Revision 1.141  2004/11/04 19:26:42  assefa
 * MapServer now provids one default style named (default), title and LegendURL
 * when possible.
 * Added also the possibility to use the keword defulat for STYLES parameter when
 * doing a GetMap (..&STYLES=defuatlt,default,...). Bug 1011.
 *
 * Revision 1.140  2004/11/04 12:32:39  julien
 * Add xlink:type=... in WMS MetadataURL (bug 1027)
 *
 * Revision 1.139  2004/11/03 20:01:19  dan
 * Protect msDebug() call with a if(msp->debug)
 *
 * Revision 1.138  2004/11/02 13:16:39  dan
 * Fixed problem with msWMSIsSubGroup() when not all layers use
 * wms_layer_group (bug 1024)
 *
 * Revision 1.137  2004/11/01 22:05:16  dan
 * Get rid of WMS 1.0.8, it's not one of the 'official' WMS releases (bug 1022)
 *
 * Revision 1.136  2004/10/29 22:18:54  assefa
 * Use ows_schama_location metadata. The default value if metadata is not found
 * is http://schemas.opengeospatial.net
 *
 * Revision 1.135  2004/10/29 22:03:40  dan
 * Enable MS_NONSQUARE by default for WMS is width/height doesn't match the
 * extents' x/y ratio (bug 862).
 * When reprojecting layers in a GetMap request (or if NONSQUARE enabled), then
 * copy the original map projection to any layer that doesn't have a projection
 * explicitly set in the mapfile (bug 947)
 *
 * Revision 1.134  2004/10/29 00:13:17  assefa
 * Support RULE parameter for GetLegendGraphic (Bug 843)
 * Change link:href="...to "xlink:href="... (Bug 1001)
 *
 * Revision 1.133  2004/10/28 21:28:06  assefa
 * Auto generate GetLegndGraphic URL if wms_stle_<stylename>_legendurl_href
 * is not present (Bug 1001).
 *
 * Revision 1.132  2004/10/28 18:16:17  dan
 * Fixed WMS GetLegendGraphic which was returning an exception (GD error)
 * when requested layer was out of scale (bug 1006)
 *
 * Revision 1.131  2004/10/27 22:08:12  assefa
 * Add WCS tytpe in DescribeLayer (Bug 683).
 *
 * Revision 1.130  2004/10/27 20:41:07  julien
 * in MetadataURL printing write xlink:href instead of link:href.
 *
 * Revision 1.129  2004/10/27 19:51:24  assefa
 * Correct XML for DescribeLayer response (Bug 683)
 *
 * Revision 1.128  2004/10/27 14:58:34  assefa
 * Correct exception message for GetFeatureInfo (Bug 819)
 *
 * Revision 1.127  2004/10/27 10:20:04  assefa
 * Correct bug with format in GetLegendGraphic (Bug 991).
 *
 * Revision 1.126  2004/10/25 17:38:44  julien
 * Remove debug info tag.
 *
 * Revision 1.125  2004/10/25 17:30:38  julien
 * Print function for OGC URLs components. msOWSPrintURLType() (Bug 944)
 *
 * Revision 1.124  2004/10/25 14:46:41  assefa
 * Test on layer status before applying time (Bug 986).
 *
 * Revision 1.123  2004/10/21 19:20:48  assefa
 * Correct test in time functions on return value (Bug 976).
 *
 * Revision 1.122  2004/10/21 04:30:54  frank
 * Added standardized headers.  Added MS_CVSID().
 *
 */

#include "map.h"
#include "maperror.h"
#include "mapgml.h"
#include "gdfonts.h"

#include "maptemplate.h"

#include "mapogcsld.h"

#include "maptime.h"

#include <stdarg.h>
#include <time.h>
#include <string.h>

#ifdef WIN32
#include <process.h>
#endif

MS_CVSID("$Id$")

/* ==================================================================
 * WMS Server stuff.
 * ================================================================== */
#ifdef USE_WMS_SVR

/*
** msWMSException()
**
** Report current MapServer error in requested format.
*/
static char *wms_exception_format=NULL;

int msWMSException(mapObj *map, int nVersion, const char *exception_code)
{
    char *schemalocation = NULL;

    // Default to WMS 1.1.1 exceptions if version not set yet
    if (nVersion <= 0)
        nVersion = OWS_1_1_1;

    //get scheam location
    schemalocation = msEncodeHTMLEntities( msOWSGetSchemasLocation(map) );

  // Establish default exception format depending on VERSION
  if (wms_exception_format == NULL)
  {
      if (nVersion <= OWS_1_0_0)
        wms_exception_format = "INIMAGE";  // WMS 1.0.0
      else if (nVersion <= OWS_1_0_7)
        wms_exception_format = "SE_XML";   // WMS 1.0.1 to 1.0.7
      else
        wms_exception_format = "application/vnd.ogc.se_xml"; // WMS 1.1.0 and later
  }

  if (strcasecmp(wms_exception_format, "INIMAGE") == 0 ||
      strcasecmp(wms_exception_format, "BLANK") == 0 ||
      strcasecmp(wms_exception_format, "application/vnd.ogc.se_inimage")== 0 ||
      strcasecmp(wms_exception_format, "application/vnd.ogc.se_blank") == 0)
  {
    int blank = 0;

    if (strcasecmp(wms_exception_format, "BLANK") == 0 ||
        strcasecmp(wms_exception_format, "application/vnd.ogc.se_blank") == 0)
    {
        blank = 1;
    }

    msWriteErrorImage(map, NULL, blank);

  }
  else if (strcasecmp(wms_exception_format, "WMS_XML") == 0) // Only in V1.0.0
  {
    msIO_printf("Content-type: text/xml%c%c",10,10);
    msIO_printf("<WMTException version=\"1.0.0\">\n");
    msWriteErrorXML(stdout);
    msIO_printf("</WMTException>\n");
  }
  else // XML error, the default: SE_XML (1.0.1 to 1.0.7)
       // or application/vnd.ogc.se_xml (1.1.0 and later)
  {
    if (nVersion <= OWS_1_0_7)
    {
      // In V1.0.1 to 1.0.7, the MIME type was text/xml
      msIO_printf("Content-type: text/xml%c%c",10,10);

      msOWSPrintEncodeMetadata(stdout, &(map->web.metadata),
                               "MO", "encoding", OWS_NOERR,
                "<?xml version='1.0' encoding=\"%s\" standalone=\"no\" ?>\n",
                    "ISO-8859-1");
      msIO_printf("<!DOCTYPE ServiceExceptionReport SYSTEM \"http://www.digitalearth.gov/wmt/xml/exception_1_0_1.dtd\">\n");

      msIO_printf("<ServiceExceptionReport version=\"1.0.1\">\n");
    }
    else if (nVersion <= OWS_1_1_0)
    {
      // In V1.1.0 and later, we have OGC-specific MIME types
      // we cannot return anything else than application/vnd.ogc.se_xml here.
      msIO_printf("Content-type: application/vnd.ogc.se_xml%c%c",10,10);

      msOWSPrintEncodeMetadata(stdout, &(map->web.metadata),
                               "MO", "encoding", OWS_NOERR,
                "<?xml version='1.0' encoding=\"%s\" standalone=\"no\" ?>\n",
                         "ISO-8859-1");

      
      msIO_printf("<!DOCTYPE ServiceExceptionReport SYSTEM \"%s/wms/1.1.0/exception_1_1_0.dtd\">\n",schemalocation);

      msIO_printf("<ServiceExceptionReport version=\"1.1.0\">\n");
    }
    else //1.1.1
    {
        msIO_printf("Content-type: application/vnd.ogc.se_xml%c%c",10,10);

        msOWSPrintEncodeMetadata(stdout, &(map->web.metadata),
                                 "MO", "encoding", OWS_NOERR,
                  "<?xml version='1.0' encoding=\"%s\" standalone=\"no\" ?>\n",
                           "ISO-8859-1");
        msIO_printf("<!DOCTYPE ServiceExceptionReport SYSTEM \"%s/wms/1.1.1/exception_1_1_1.dtd\">\n", schemalocation);
        msIO_printf("<ServiceExceptionReport version=\"1.1.1\">\n");
    }


    if (exception_code)
      msIO_printf("<ServiceException code=\"%s\">\n", exception_code);
    else
      msIO_printf("<ServiceException>\n");
    msWriteErrorXML(stdout);
    msIO_printf("</ServiceException>\n");
    msIO_printf("</ServiceExceptionReport>\n");

    free(schemalocation);

  }

  return MS_FAILURE; // so that we can call 'return msWMSException();' anywhere
}

int msValidateTimeValue(char *timestring, const char *timeextent)
{
    char **atimeextent, **atimes, **tokens =  NULL;
    int numtimeextent, i, numtimes, ntmp = 0;
    struct tm tm, tmstart, tmend;


    //we need to validate the time passsed in the request
    //against the time extent defined


    if (!timestring || !timeextent)
      return MS_FALSE;

    //parse time extent. Only supports one range (2004-09-21/2004-09-25)
    atimeextent = split (timeextent, '/', &numtimeextent);
    if (atimeextent == NULL || numtimeextent != 2)
    {
        msFreeCharArray(atimeextent, numtimeextent);
        return MS_FALSE;
    }
    //build time structure for the extents
    msTimeInit(&tmstart);
    msTimeInit(&tmend);
    if (msParseTime(atimeextent[0], &tmstart) != MS_TRUE ||
        msParseTime(atimeextent[1], &tmend) != MS_TRUE)
    {
         msFreeCharArray(atimeextent, numtimeextent);
         return MS_FALSE;
    }

     msFreeCharArray(atimeextent, numtimeextent);
    //parse the time string. We support descrete times (eg 2004-09-21),
    //multiple times (2004-09-21, 2004-09-22, ...)
    //and range(s) (2004-09-21/2004-09-25, 2004-09-27/2004-09-29)
    if (strstr(timestring, ",") == NULL &&
        strstr(timestring, "/") == NULL) //discrete time
    {
        msTimeInit(&tm);
        if (msParseTime(timestring, &tm) == MS_TRUE)
        {
            if (msTimeCompare(&tmstart, &tm) <= 0 &&
                msTimeCompare(&tmend, &tm) >= 0)
                return MS_TRUE;
        }
    }
    else
    {
        atimes = split (timestring, ',', &numtimes);
        if (numtimes >=1)
        {
            tokens = split(atimes[0],  '/', &ntmp);
            if (ntmp == 2)//ranges
            {
                 for (i=0; i<numtimes; i++)
                 {
                     msFreeCharArray(tokens, ntmp);

                     tokens = split(atimes[i],  '/', &ntmp);
                     if (!tokens || ntmp != 2)
                     {
                        msFreeCharArray(tokens, ntmp);
                        return MS_FALSE;
                     }
                     msTimeInit(&tm);
                     if (msParseTime(tokens[0], &tm) != MS_TRUE ||
                         msTimeCompare(&tmstart, &tm) > 0 ||
                         msTimeCompare(&tmend, &tm) < 0)
                     {
                         msFreeCharArray(tokens, ntmp);
                         return MS_FALSE;
                     }
                     if (msParseTime(tokens[1], &tm) != MS_TRUE ||
                         msTimeCompare(&tmstart, &tm) > 0 ||
                         msTimeCompare(&tmend, &tm) < 0)
                     {
                         msFreeCharArray(tokens, ntmp);
                         return MS_FALSE;
                     }
                 }
                 msFreeCharArray(atimes, numtimes);
                 return MS_TRUE;
            }
            else if (ntmp == 1) //multiple times
            {
                msFreeCharArray(tokens, ntmp);
                for (i=0; i<numtimes; i++)
                {
                    msTimeInit(&tm);
                    if (msParseTime(atimes[i], &tm) != MS_TRUE ||
                        msTimeCompare(&tmstart, &tm) > 0 ||
                        msTimeCompare(&tmend, &tm) < 0)
                    {
                         msFreeCharArray(atimes, numtimes);
                        return MS_FALSE;
                    }
                }
                return MS_TRUE;
            }
        }

    }
    return MS_FALSE;

}

void msWMSSetTimePattern(const char *timepatternstring, char *timestring)
{
    char *time = NULL;
    char **atimes, **tokens = NULL;
    int numtimes, ntmp, i = 0;
    char *tmpstr = NULL;

    if (timepatternstring && timestring)
    {
        //parse the time parameter to extract a distinct time.
        //time value can be dicrete times (eg 2004-09-21),
        //multiple times (2004-09-21, 2004-09-22, ...)
        //and range(s) (2004-09-21/2004-09-25, 2004-09-27/2004-09-29)
        if (strstr(timestring, ",") == NULL &&
            strstr(timestring, "/") == NULL) //discrete time
        {
            time = strdup(timestring);
        }
        else
        {
            atimes = split (timestring, ',', &numtimes);
            if (numtimes >=1 && atimes)
            {
                tokens = split(atimes[0],  '/', &ntmp);
                if (ntmp == 2 && tokens) //range
                {
                    time = strdup(tokens[0]);
                }
                else //multiple times
                {
                    time = strdup(atimes[0]);
                }
                msFreeCharArray(tokens, ntmp);
                msFreeCharArray(atimes, numtimes);
            }
        }
        //get the pattern to use
        if (time)
        {
            tokens = split(timepatternstring, ',', &ntmp);
            if (tokens && ntmp >= 1)
            {
                for (i=0; i<ntmp; i++)
                {
                  if (tokens[i] && strlen(tokens[i]) > 0)
                  {
                      trimBlanks(tokens[i]);
                      tmpstr = trimLeft(tokens[i]);
                      if (msTimeMatchPattern(time, tmpstr) == MS_TRUE)
                      {
                          msSetLimitedPattersToUse(tmpstr);
                          break;
                      }
                  }
                }
                msFreeCharArray(tokens, ntmp);
            }
            free(time);
        }

    }
}

/*
** Apply the TIME parameter to layers that are time aware
*/
int msWMSApplyTime(mapObj *map, int version, char *time)
{
    int i=0;
    layerObj *lp = NULL;
    const char *timeextent, *timefield, *timedefault, *timpattern = NULL;

    if (map)
    {
        for (i=0; i<map->numlayers; i++)
        {
            lp = &(map->layers[i]);
            if (lp->status != MS_ON && lp->status != MS_DEFAULT)
              continue;
            //check if the layer is time aware
            timeextent = msOWSLookupMetadata(&(lp->metadata), "MO",
                                             "timeextent");
            timefield =  msOWSLookupMetadata(&(lp->metadata), "MO",
                                             "timeitem");
            timedefault =  msOWSLookupMetadata(&(lp->metadata), "MO",
                                             "timedefault");
            if (timeextent && timefield)
            {
                //check to see if the time value is given. If not
                //use default time. If default time is not available
                //send an exception
                if (time == NULL || strlen(time) <=0)
                {
                    if (timedefault == NULL)
                    {
                        msSetError(MS_WMSERR, "No Time value was given, and no default time value defined.", "msWMSApplyTime");
                        return msWMSException(map, version,
                                              "MissingDimensionValue");
                    }
                    else
                    {
                        if (msValidateTimeValue((char *)timedefault, timeextent) == MS_FALSE)
                        {
                            msSetError(MS_WMSERR, "No Time value was given, and the default time value %s is invalid or outside the time extent defined %s", "msWMSApplyTime", timedefault, timeextent);
                        //return MS_FALSE;
                            return msWMSException(map, version,
                                              "InvalidDimensionValue");
                        }
                        msLayerSetTimeFilter(lp, timedefault, timefield);
                    }
                }
                else
                {
                    //check if given time is in the range
                    if (msValidateTimeValue(time, timeextent) == MS_FALSE)
                    {
                        if (timedefault == NULL)
                        {
                            msSetError(MS_WMSERR, "Time value(s) %s given is invalid or outside the time extent defined (%s).", "msWMSApplyTime", time, timeextent);
                        //return MS_FALSE;
                            return msWMSException(map, version,
                                                  "InvalidDimensionValue");
                        }
                        else
                        {
                            if (msValidateTimeValue((char *)timedefault, timeextent) == MS_FALSE)
                            {
                                msSetError(MS_WMSERR, "Time value(s) %s given is invalid or outside the time extent defined (%s), and default time set is invalid (%s)", "msWMSApplyTime", time, timeextent, timedefault);
                        //return MS_FALSE;
                                return msWMSException(map, version,
                                                      "InvalidDimensionValue");
                            }
                            else
                              msLayerSetTimeFilter(lp, timedefault, timefield);
                        }
                            
                    }
                    else
                    {
                    //build the time string
                        msLayerSetTimeFilter(lp, time, timefield);
                        timeextent= NULL;
                    }
                }
            }
        }
        //check to see if there is a list of possible patterns defined
        //if it is the case, use it to set the time pattern to use
        //for the request

        timpattern = msOWSLookupMetadata(&(map->web.metadata), "MO",
                                         "timeformat");
        if (timpattern && time && strlen(time) > 0)
          msWMSSetTimePattern(timpattern, time);
    }

    return MS_SUCCESS;
}


/*
**
*/
int msWMSLoadGetMapParams(mapObj *map, int nVersion,
                          char **names, char **values, int numentries)
{
  int i, adjust_extent = MS_FALSE, nonsquare_enabled = MS_FALSE;
  int iUnits = -1;
  int nLayerOrder = 0;
  int transparent = MS_NOOVERRIDE;
  outputFormatObj *format = NULL;
  int validlayers = 0;
  char *styles = NULL;
  int numlayers = 0;
  char **layers = NULL;
  int layerfound =0;
  int invalidlayers = 0;
  char epsgbuf[32];
  char srsbuffer[32];
  int epsgvalid = MS_FALSE;
  const char *projstring;
   char **tokens;
   int n,j = 0;
   int timerequest = 0;
   char *stime = NULL;

   epsgbuf[0]='\0';
   srsbuffer[0]='\0';

  // Some of the getMap parameters are actually required depending on the
  // request, but for now we assume all are optional and the map file
  // defaults will apply.

  for(i=0; map && i<numentries; i++)
  {
    // getMap parameters
    if (strcasecmp(names[i], "LAYERS") == 0)
    {
      int  j, k, iLayer;

      layers = split(values[i], ',', &numlayers);
      if (layers==NULL || numlayers < 1) {
        msSetError(MS_WMSERR, "At least one layer name required in LAYERS.",
                   "msWMSLoadGetMapParams()");
        return msWMSException(map, nVersion, NULL);
      }


      for (iLayer=0; iLayer < map->numlayers; iLayer++)
          map->layerorder[iLayer] = iLayer;

      for(j=0; j<map->numlayers; j++)
      {
        // Keep only layers with status=DEFAULT by default
        // Layer with status DEFAULT is drawn first.
        if (map->layers[j].status != MS_DEFAULT)
           map->layers[j].status = MS_OFF;
        else
           map->layerorder[nLayerOrder++] = j;
      }

      for (k=0; k<numlayers; k++)
      {
          layerfound = 0;
          for (j=0; j<map->numlayers; j++)
          {
              // Turn on selected layers only.
              if ((map->layers[j].name &&
                   strcasecmp(map->layers[j].name, layers[k]) == 0) ||
                  (map->name && strcasecmp(map->name, layers[k]) == 0) ||
                  (map->layers[j].group && strcasecmp(map->layers[j].group, layers[k]) == 0))
              {
                  map->layers[j].status = MS_ON;
                  map->layerorder[nLayerOrder++] = j;
                  validlayers++;
                  layerfound = 1;
              }
          }
          if (layerfound == 0)
            invalidlayers++;

      }

      // set all layers with status off at end of array
      for (j=0; j<map->numlayers; j++)
      {
         if (map->layers[j].status == MS_OFF)
           map->layerorder[nLayerOrder++] = j;
      }

      msFreeCharArray(layers, numlayers);
    }
    else if (strcasecmp(names[i], "STYLES") == 0) {
        styles = values[i];

    }
    else if (strcasecmp(names[i], "SRS") == 0) {
      // SRS is in format "EPSG:epsg_id" or "AUTO:proj_id,unit_id,lon0,lat0"
      if (strncasecmp(values[i], "EPSG:", 5) == 0)
      {
        // SRS=EPSG:xxxx

          sprintf(srsbuffer, "init=epsg:%.20s", values[i]+5);
          sprintf(epsgbuf, "EPSG:%.20s",values[i]+5);

        //we need to wait until all params are read before
        //loding the projection into the map. This will help
        //insure that the passes srs is valid for all layers.
        /*
        if (msLoadProjectionString(&(map->projection), buffer) != 0)
          return msWMSException(map, nVersion, NULL);

        iUnits = GetMapserverUnitUsingProj(&(map->projection));
        if (iUnits != -1)
          map->units = iUnits;
        */
      }
      else if (strncasecmp(values[i], "AUTO:", 5) == 0)
      {
        sprintf(srsbuffer, "%s",  values[i]);
        // SRS=AUTO:proj_id,unit_id,lon0,lat0
        /*
        if (msLoadProjectionString(&(map->projection), values[i]) != 0)
          return msWMSException(map, nVersion, NULL);

        iUnits = GetMapserverUnitUsingProj(&(map->projection));
        if (iUnits != -1)
          map->units = iUnits;
        */
      }
      else
      {
        msSetError(MS_WMSERR,
                   "Unsupported SRS namespace (only EPSG and AUTO currently supported).",
                   "msWMSLoadGetMapParams()");
        return msWMSException(map, nVersion, "InvalidSRS");
      }
    }
    else if (strcasecmp(names[i], "BBOX") == 0) {
      char **tokens;
      int n;
      tokens = split(values[i], ',', &n);
      if (tokens==NULL || n != 4) {
        msSetError(MS_WMSERR, "Wrong number of arguments for BBOX.",
                   "msWMSLoadGetMapParams()");
        return msWMSException(map, nVersion, NULL);
      }
      map->extent.minx = atof(tokens[0]);
      map->extent.miny = atof(tokens[1]);
      map->extent.maxx = atof(tokens[2]);
      map->extent.maxy = atof(tokens[3]);

      msFreeCharArray(tokens, n);

      //validate bbox values
      if ( map->extent.minx >= map->extent.maxx ||
           map->extent.miny >=  map->extent.maxy)
      {
          msSetError(MS_WMSERR,
                   "Invalid values for BBOX.",
                   "msWMSLoadGetMapParams()");
          return msWMSException(map, nVersion, NULL);
      }
      adjust_extent = MS_TRUE;
    }
    else if (strcasecmp(names[i], "WIDTH") == 0) {
      map->width = atoi(values[i]);
    }
    else if (strcasecmp(names[i], "HEIGHT") == 0) {
      map->height = atoi(values[i]);
    }
    else if (strcasecmp(names[i], "FORMAT") == 0) {

      format = msSelectOutputFormat( map, values[i] );

      if( format == NULL || 
          (strncasecmp(format->driver, "GD/", 3) != 0 &&
           strncasecmp(format->driver, "GDAL/", 4) != 0))
        {
          msSetError(MS_IMGERR,
                   "Unsupported output format (%s).",
                   "msWMSLoadGetMapParams()",
                   values[i] );
        return msWMSException(map, nVersion, "InvalidFormat");
      }

      msFree( map->imagetype );
      map->imagetype = strdup(values[i]);
    }
    else if (strcasecmp(names[i], "TRANSPARENT") == 0) {
      transparent = (strcasecmp(values[i], "TRUE") == 0);
    }
    else if (strcasecmp(names[i], "BGCOLOR") == 0) {
      long c;
      c = strtol(values[i], NULL, 16);
      map->imagecolor.red = (c/0x10000)&0xff;
      map->imagecolor.green = (c/0x100)&0xff;
      map->imagecolor.blue = c&0xff;
    }
#ifdef USE_OGR
/* -------------------------------------------------------------------- */
/*      SLD support :                                                   */
/*        - check if the SLD parameter is there. it is supposed to      */
/*      refer a valid URL containing an SLD document.                   */
/*        - check the SLD_BODY parameter that should contain the SLD    */
/*      xml string.                                                     */
/* -------------------------------------------------------------------- */
    else if (strcasecmp(names[i], "SLD") == 0 &&
             values[i] && strlen(values[i]) > 0) {
          msSLDApplySLDURL(map, values[i], -1, NULL);
    }
    else if (strcasecmp(names[i], "SLD_BODY") == 0 &&
               values[i] && strlen(values[i]) > 0) {
          msSLDApplySLD(map, values[i], -1, NULL);
    }
#endif



    //value of time can be empty. We should look for a default value
    //see function msWMSApplyTime
    else if (strcasecmp(names[i], "TIME") == 0)// &&  values[i])
    {
        stime = values[i];
        timerequest = 1;
    }
  }
  /*
  ** Apply time filters if available in the request
  */
  if (timerequest)
  {
      if (msWMSApplyTime(map, nVersion, stime) == MS_FAILURE)
      {
          return MS_FAILURE;// msWMSException(map, nVersion, "InvalidTimeRequest");
      }
  } 
  /*
  ** Apply the selected output format (if one was selected), and override
  ** the transparency if needed.
  */

  if( format != NULL )
      msApplyOutputFormat( &(map->outputformat), format, transparent,
                           MS_NOOVERRIDE, MS_NOOVERRIDE );

  /* Validate all layers given. 
  ** If an invalid layer is sent, return an exception.
  */
  if (validlayers == 0 || invalidlayers > 0)
  {
      msSetError(MS_WMSERR, "Invalid layer(s) given in the LAYERS parameter.",
                 "msWMSLoadGetMapParams()");
      return msWMSException(map, nVersion, "LayerNotDefined");
  }

  /* validate srs value: When the SRS parameter in a GetMap request contains a
  ** SRS that is valid for some, but not all of the layers being requested, 
  ** then the server shall throw a Service Exception (code = "InvalidSRS").
  ** Validate first against epsg in the map and if no matching srs is found
  ** validate all layers requested.
  */
  if (epsgbuf && strlen(epsgbuf) > 1)
  {
      epsgvalid = MS_FALSE;
      projstring = msOWSGetEPSGProj(&(map->projection), &(map->web.metadata),
                                    "MO", MS_FALSE);
      if (projstring)
      {
          tokens = split(projstring, ' ', &n);
          if (tokens && n > 0)
          {
              for(i=0; i<n; i++)
              {
                  if (strcasecmp(tokens[i], epsgbuf) == 0)
                  {
                      epsgvalid = MS_TRUE;
                      break;
                  }
              }
              msFreeCharArray(tokens, n);
          }
      }
      if (epsgvalid == MS_FALSE)
      {
          for (i=0; i<map->numlayers; i++)
          {
              epsgvalid = MS_FALSE;
              if (map->layers[i].status == MS_ON)
              {
                  projstring = msOWSGetEPSGProj(&(map->layers[i].projection),
                                                &(map->layers[i].metadata),
                                                "MO", MS_FALSE);
                  if (projstring)
                  {
                      tokens = split(projstring, ' ', &n);
                      if (tokens && n > 0)
                      {
                          for(j=0; j<n; j++)
                          {
                              if (strcasecmp(tokens[j], epsgbuf) == 0)
                              {
                                  epsgvalid = MS_TRUE;
                                  break;
                              }
                          }
                          msFreeCharArray(tokens, n);
                      }
                  }
                  if (epsgvalid == MS_FALSE)
                  {
                      msSetError(MS_WMSERR, "Invalid SRS given : SRS must be valid for all requested layers.",
                                         "msWMSLoadGetMapParams()");
                      return msWMSException(map, nVersion, "InvalidSRS");
                  }
              }
          }
      }
  }

  /* Validate requested image size. 
   */
  if(map->width > map->maxsize || map->height > map->maxsize ||
     map->width < 1 || map->height < 1)
  {
      msSetError(MS_WMSERR, "Image size out of range, WIDTH and HEIGHT must be between 1 and %d pixels.", "msWMSLoadGetMapParams()", map->maxsize);

      // Restore valid default values in case errors INIMAGE are used
      map->width = 400;
      map->height= 300;
      return msWMSException(map, nVersion, NULL);
  }

  /* Check whether requested BBOX and width/height result in non-square pixels
   */
  nonsquare_enabled = msTestConfigOption( map, "MS_NONSQUARE", MS_FALSE );
  if (!nonsquare_enabled)
  {
      double dx, dy, reqy;
      dx = MS_ABS(map->extent.maxx - map->extent.minx);
      dy = MS_ABS(map->extent.maxy - map->extent.miny);

      reqy = ((double)map->width) * dy / dx;

      // Allow up to 1 pixel of error on the width/height ratios.
      // If more than 1 pixel then enable non-square pixels
      if ( MS_ABS((reqy - (double)map->height)) > 1.0 )
      {
          if (map->debug)
              msDebug("msWMSLoadGetMapParams(): enabling non-square pixels.");
          msSetConfigOption(map, "MS_NONSQUARE", "YES");
          nonsquare_enabled = MS_TRUE;
      }
  }

  /* If the requested SRS is different from the default mapfile projection, or
  ** if a BBOX resulting in non-square pixels is requested then
  ** copy the original mapfile's projection to any layer that doesn't already 
  ** have a projection. This will prevent problems when users forget to 
  ** explicitly set a projection on all layers in a WMS mapfile.
  */
  if ((srsbuffer && strlen(srsbuffer) > 1) || nonsquare_enabled)
  {
      projectionObj newProj;

      if (map->projection.numargs <= 0)
      {
          msSetError(MS_WMSERR, "Cannot set new SRS on a map that doesn't "
                     "have any projection set. Please make sure your mapfile "
                     "has a projection defined at the top level.", 
                     "msWMSLoadGetMapParams()");
          return msWMSException(map, nVersion, "InvalidSRS");
      }
      
      msInitProjection(&newProj);
      if (srsbuffer && strlen(srsbuffer) > 1 && 
          msLoadProjectionString(&newProj, srsbuffer) != 0)
      {
          msFreeProjection(&newProj);
          return msWMSException(map, nVersion, NULL);
      }

      if (nonsquare_enabled || 
          msProjectionsDiffer(&(map->projection), &newProj))
      {
          char *original_srs = NULL;

          for(i=0; i<map->numlayers; i++)
          {
              if (map->layers[i].projection.numargs <= 0 &&
                  map->layers[i].status != MS_OFF &&
                  map->layers[i].transform == MS_TRUE)
              {
                  // This layer is turned on and needs a projection

                  // Fetch main map projection string only now that we need it
                  if (original_srs == NULL)
                      original_srs = msGetProjectionString(&(map->projection));

                  if (msLoadProjectionString(&(map->layers[i].projection),
                                             original_srs) != 0)
                  {
                      msFreeProjection(&newProj);
                      return msWMSException(map, nVersion, NULL);
                  }
                  map->layers[i].project = MS_TRUE;
              }
          }

          msFree(original_srs);
      }

      msFreeProjection(&newProj);
  }

  //apply the srs to the map file. This is only done after validating
  //that the srs given as parameter is valid for all layers
  if (srsbuffer && strlen(srsbuffer) > 1)
  {
      if (msLoadProjectionString(&(map->projection), srsbuffer) != 0)
          return msWMSException(map, nVersion, NULL);

        iUnits = GetMapserverUnitUsingProj(&(map->projection));
        if (iUnits != -1)
          map->units = iUnits;
  }

  /* Validate Styles :
  ** mapserv does not advertize any styles (the default styles are the
  ** one that are used. So we are expecting here to have empty values
  ** for the styles parameter (...&STYLES=&...) Or for multiple Styles/Layers,
  ** we could have ...&STYLES=,,,. If that is not the
  ** case, we generate an exception.
  */
  if(styles && strlen(styles) > 0)
  {
      char **tokens;
      int n=0, i=0;
      
      tokens = split(styles, ',' ,&n);
      for (i=0; i<n; i++)
      {
          if (tokens[i] && strlen(tokens[i]) > 0 && 
              strcasecmp(tokens[i],"default") != 0)
          {
              msSetError(MS_WMSERR, "Invalid style (%s). Mapserver supports only default styles and is expecting an empty string for the STYLES : STYLES= or STYLES=,,, or using keyword default  STYLES=default,default, ...",
                         "msWMSLoadGetMapParams()", styles);
              return msWMSException(map, nVersion, "StyleNotDefined");
          }
      }
      if (tokens && n > 0)
        msFreeCharArray(tokens, n);
  }

  /*
  ** WMS extents are edge to edge while MapServer extents are center of
  ** pixel to center of pixel.  Here we try to adjust the WMS extents
  ** in by half a pixel.  We wait till here because we want to ensure we
  ** are doing this in terms of the correct WIDTH and HEIGHT.
  */
  if( adjust_extent )
  {
      double	dx, dy;

      dx = (map->extent.maxx - map->extent.minx) / map->width;
      map->extent.minx += dx*0.5;
      map->extent.maxx -= dx*0.5;

      dy = (map->extent.maxy - map->extent.miny) / map->height;
      map->extent.miny += dy*0.5;
      map->extent.maxy -= dy*0.5;
  }

  return MS_SUCCESS;
}



/*
**
*/
static void msWMSPrintRequestCap(int nVersion, const char *request,
                              const char *script_url, const char *formats, ...)
{
  va_list argp;
  const char *fmt;
  char *encoded;

  msIO_printf("    <%s>\n", request);

  // We expect to receive a NULL-terminated args list of formats
  va_start(argp, formats);
  fmt = formats;
  while(fmt != NULL)
  {
      /* Special case for early WMS with subelements in Format (bug 908) */
      if( nVersion <= OWS_1_0_7 )
      {
          encoded = strdup( fmt );
      }

      /* otherwise we HTML code special characters */
      else
      {
          encoded = msEncodeHTMLEntities(fmt);
      }

      msIO_printf("      <Format>%s</Format>\n", encoded);
      msFree(encoded);

      fmt = va_arg(argp, const char *);
  }
  va_end(argp);

  msIO_printf("      <DCPType>\n");
  msIO_printf("        <HTTP>\n");
  // The URL should already be HTML encoded.
  if (nVersion == OWS_1_0_0) {
    msIO_printf("          <Get onlineResource=\"%s\" />\n", script_url);
    msIO_printf("          <Post onlineResource=\"%s\" />\n", script_url);
  } else {
    msIO_printf("          <Get><OnlineResource xmlns:xlink=\"http://www.w3.org/1999/xlink\" xlink:href=\"%s\"/></Get>\n", script_url);
    msIO_printf("          <Post><OnlineResource xmlns:xlink=\"http://www.w3.org/1999/xlink\" xlink:href=\"%s\"/></Post>\n", script_url);
  }

  msIO_printf("        </HTTP>\n");
  msIO_printf("      </DCPType>\n");
  msIO_printf("    </%s>\n", request);
}



/*
** msWMSPrintScaleHint()
**
** Print a ScaleHint tag for this layer if applicable.
**
** (see WMS 1.1.0 sect. 7.1.5.4) The WMS defines the scalehint values as
** the ground distance in meters of the southwest to northeast diagonal of
** the central pixel of a map.  ScaleHint values are the min and max
** recommended values of that diagonal.
*/
void msWMSPrintScaleHint(const char *tabspace, double minscale,
                         double maxscale, double resolution)
{
  double scalehintmin=0.0, scalehintmax=0.0, diag;

  diag = sqrt(2.0);

  if (minscale > 0)
    scalehintmin = diag*(minscale/resolution)/msInchesPerUnit(MS_METERS,0);
  if (maxscale > 0)
    scalehintmax = diag*(maxscale/resolution)/msInchesPerUnit(MS_METERS,0);

  if (scalehintmin > 0.0 || scalehintmax > 0.0)
  {
      msIO_printf("%s<ScaleHint min=\"%g\" max=\"%g\" />\n",
             tabspace, scalehintmin, scalehintmax);
      if (scalehintmax == 0.0)
          msIO_printf("%s<!-- WARNING: Only MINSCALE and no MAXSCALE specified in "
                 "the mapfile. A default value of 0 has been returned for the "
                 "Max ScaleHint but this is probably not what you want. -->\n",
                 tabspace);
  }
}


/*
** msDumpLayer()
*/
int msDumpLayer(mapObj *map, layerObj *lp, int nVersion, const char *script_url_encoded, const char *indent)
{
   rectObj ext;
   const char *value;
   char **tokens;
   char *encoded;
   int n, i;
   const char *projstring;
   const char *pszWmsTimeExtent, *pszWmsTimeDefault= NULL, *pszStyle=NULL;
   const char *pszLegendURL=NULL;
   char *pszMetadataName=NULL, *mimetype=NULL;
   
   //if the layer status is set to MS_DEFAULT, output a warning
   if (lp->status == MS_DEFAULT)
     msIO_fprintf(stdout, "<!-- WARNING: This layer has its status set to DEFAULT and will always be displayed when doing a GetMap request even if it is not requested by the client. This is not in line with the expected behavior of a WMS server. Using status ON or OFF is recommended. -->\n");
 
   if (nVersion <= OWS_1_0_7)
   {
       msIO_printf("%s    <Layer queryable=\"%d\">\n",
              indent, msIsLayerQueryable(lp));
   }
   else
   {
       // 1.1.0 and later: opaque and cascaded are new.
       int cascaded=0, opaque=0;
       if ((value = msOWSLookupMetadata(&(lp->metadata), "MO", "opaque")) != NULL)
           opaque = atoi(value);
       if (lp->connectiontype == MS_WMS)
           cascaded = 1;

       msIO_printf("%s    <Layer queryable=\"%d\" opaque=\"%d\" cascaded=\"%d\">\n",
              indent, msIsLayerQueryable(lp), opaque, cascaded);
   }
   
   if (lp->name && strlen(lp->name) > 0 &&
       (msIsXMLTagValid(lp->name) == MS_FALSE || isdigit(lp->name[0])))
     msIO_fprintf(stdout, "<!-- WARNING: The layer name '%s' might contain spaces or "
                        "invalid characters or may start with a number. This could lead to potential problems. -->\n", 
                  lp->name);
   msOWSPrintEncodeParam(stdout, "LAYER.NAME", lp->name, OWS_WARN,
                         "        <Name>%s</Name>\n", NULL);

   // the majority of this section is dependent on appropriately named metadata in the LAYER object
   msOWSPrintEncodeMetadata(stdout, &(lp->metadata), "MO", "title",
                            OWS_WARN, "        <Title>%s</Title>\n", lp->name);

   msOWSPrintEncodeMetadata(stdout, &(lp->metadata), "MO", "abstract",
                         OWS_NOERR, "        <Abstract>%s</Abstract>\n", NULL);

   if (nVersion == OWS_1_0_0)
   {
       // <Keywords> in V 1.0.0
       // The 1.0.0 spec doesn't specify which delimiter to use so let's use spaces
       msOWSPrintEncodeMetadataList(stdout, &(lp->metadata), "MO",
                                    "keywordlist",
                                    "        <Keywords>",
                                    "        </Keywords>\n",
                                    "%s ", NULL);
   }
   else
   {
       // <KeywordList><Keyword> ... in V1.0.6+
       msOWSPrintEncodeMetadataList(stdout, &(lp->metadata), "MO",
                                    "keywordlist",
                                    "        <KeywordList>\n",
                                    "        </KeywordList>\n",
                                    "          <Keyword>%s</Keyword>\n", NULL);
   }

   if (msOWSGetEPSGProj(&(map->projection),&(map->web.metadata),
                        "MO", MS_FALSE) == NULL)
   {
       if (nVersion > OWS_1_1_0)
       {
           projstring = msOWSGetEPSGProj(&(lp->projection), &(lp->metadata),
                                         "MO", MS_FALSE);
           if (!projstring)
             msIO_fprintf(stdout, "<!-- WARNING: Mandatory mapfile parameter '%s' was missing in this context. -->\n", "(at least one of) MAP.PROJECTION, LAYER.PROJECTION or wms_srs metadata");
           else
           {
               tokens = split(projstring, ' ', &n);
               if (tokens && n > 0)
               {
                   for(i=0; i<n; i++)
                   {
                       encoded = msEncodeHTMLEntities(tokens[i]);
                       msIO_fprintf(stdout, "        <SRS>%s</SRS>\n", encoded);
                       msFree(encoded);
                   }

                    msFreeCharArray(tokens, n);
               }
           }
       }
       else
         // If map has no proj then every layer MUST have one or produce a warning
         msOWSPrintEncodeParam(stdout, "(at least one of) MAP.PROJECTION, "
                               "LAYER.PROJECTION or wms_srs metadata",
                               msOWSGetEPSGProj(&(lp->projection),
                                                &(lp->metadata), "MO", MS_FALSE),
                               OWS_WARN, "        <SRS>%s</SRS>\n", NULL);
   }
   else
   {
       //starting 1.1.1 SRS are given in individual tags
       if (nVersion > OWS_1_1_0)
       {
           projstring = msOWSGetEPSGProj(&(lp->projection), &(lp->metadata),
                                         "MO", MS_FALSE);
           if (projstring)
           {
               tokens = split(projstring, ' ', &n);
               if (tokens && n > 0)
               {
                   for(i=0; i<n; i++)
                   {
                       encoded = msEncodeHTMLEntities(tokens[i]);
                       msIO_fprintf(stdout, "        <SRS>%s</SRS>\n", encoded);
                       msFree(encoded);
                   }

                    msFreeCharArray(tokens, n);
               }
           }
       }
       else
       // No warning required in this case since there's at least a map proj.
         msOWSPrintEncodeParam(stdout,
                               " LAYER.PROJECTION (or wms_srs metadata)",
                               msOWSGetEPSGProj(&(lp->projection),
                                                &(lp->metadata),"MO",MS_FALSE),
                               OWS_NOERR, "        <SRS>%s</SRS>\n", NULL);
   }

   // If layer has no proj set then use map->proj for bounding box.
   if (msOWSGetLayerExtent(map, lp, "MO", &ext) == MS_SUCCESS)
   {
       if(lp->projection.numargs > 0)
       {
           msOWSPrintLatLonBoundingBox(stdout, "        ", &(ext),
                                       &(lp->projection), OWS_WMS);
           msOWSPrintBoundingBox( stdout,"        ", &(ext), &(lp->projection),
                                  &(lp->metadata), "MO" );
       }
       else
       {
           msOWSPrintLatLonBoundingBox(stdout, "        ", &(ext),
                                       &(map->projection), OWS_WMS);
           msOWSPrintBoundingBox(stdout,"        ", &(ext), &(map->projection),
                                  &(map->web.metadata), "MO" );
       }
   }

   //time support
   pszWmsTimeExtent = msOWSLookupMetadata(&(lp->metadata), "MO", "timeextent");
   if (pszWmsTimeExtent)
   {
       pszWmsTimeDefault = msOWSLookupMetadata(&(lp->metadata),  "MO",
                                               "timedefault");

       msIO_fprintf(stdout, "        <Dimension name=\"time\" units=\"ISO8601\"/>\n");
       if (pszWmsTimeDefault)
         msIO_fprintf(stdout, "        <Extent name=\"time\" default=\"%s\" nearestValue=\"0\">%s</Extent>\n",pszWmsTimeDefault, pszWmsTimeExtent);
       else
           msIO_fprintf(stdout, "        <Extent name=\"time\" nearestValue=\"0\">%s</Extent>\n",pszWmsTimeExtent);

   }

   if(nVersion >= OWS_1_1_0)
       msOWSPrintURLType(stdout, &(lp->metadata), "MO", "metadataurl", 
                         OWS_NOERR, NULL, "MetadataURL", " type=\"%s\"", 
                         NULL, NULL, ">\n          <Format>%s</Format", 
                         "\n          <OnlineResource xmlns:xlink=\""
                         "http://www.w3.org/1999/xlink\" "
                         "xlink:type=\"simple\" xlink:href=\"%s\"/>\n        ",
                         MS_TRUE, MS_FALSE, MS_FALSE, MS_TRUE, MS_TRUE, 
                         NULL, NULL, NULL, NULL, NULL, "        ");

   if(nVersion < OWS_1_1_0)
       msOWSPrintEncodeMetadata(stdout, &(lp->metadata), "MO", "dataurl_href",
                                OWS_NOERR, "        <DataURL>%s</DataURL>\n", 
                                NULL);
   else
       msOWSPrintURLType(stdout, &(lp->metadata), "MO", "dataurl", 
                         OWS_NOERR, NULL, "DataURL", NULL, NULL, NULL, 
                         ">\n          <Format>%s</Format", 
                         "\n          <OnlineResource xmlns:xlink=\""
                         "http://www.w3.org/1999/xlink\" "
                         "xlink:type=\"simple\" xlink:href=\"%s\"/>\n        ", 
                         MS_FALSE, MS_FALSE, MS_FALSE, MS_TRUE, MS_TRUE, 
                         NULL, NULL, NULL, NULL, NULL, "        ");

   // The LegendURL reside in a style. The Web Map Context spec already 
   // included the support on this in mapserver. However, it is not in the 
   // wms_legendurl_... metadatas it's in the styles metadata,
   // In wms_style_<style_name>_lengendurl_... metadata. So we have to detect
   // the current style before reading it. Also in the Style block, we need
   // a Title and a name. We can get those in wms_style.
   pszStyle = msOWSLookupMetadata(&(lp->metadata), "MO", "style");
   if (pszStyle)
   {
       pszMetadataName = (char*)malloc(strlen(pszStyle)+205);
       sprintf(pszMetadataName, "style_%s_legendurl_href", pszStyle);
       pszLegendURL = msOWSLookupMetadata(&(lp->metadata), "MO", pszMetadataName);
   }
   else
     pszStyle = "default";

       
   if(nVersion <= OWS_1_0_0 && pszLegendURL)
   {
       // First, print the style block
       msIO_fprintf(stdout, "        <Style>\n");
       msIO_fprintf(stdout, "          <Name>%s</Name>\n", pszStyle);
       msIO_fprintf(stdout, "          <Title>%s</Title>\n", pszStyle);

          
       // Inside, print the legend url block
       msOWSPrintEncodeMetadata(stdout, &(lp->metadata), "MO", 
                                pszMetadataName,
                                OWS_NOERR, 
                                "          <StyleURL>%s</StyleURL>\n", 
                                NULL);

       // close the style block
       msIO_fprintf(stdout, "        </Style>\n");

   }
   else if(nVersion >= OWS_1_1_0)
   {
       if (pszLegendURL)
       {
           // First, print the style block
           msIO_fprintf(stdout, "        <Style>\n");
           msIO_fprintf(stdout, "          <Name>%s</Name>\n", pszStyle);
           msIO_fprintf(stdout, "          <Title>%s</Title>\n", pszStyle);

           
           // Inside, print the legend url block
           sprintf(pszMetadataName, "style_%s_legendurl", pszStyle);
           msOWSPrintURLType(stdout, &(lp->metadata), "MO",pszMetadataName,
                             OWS_NOERR, NULL, "LegendURL", NULL, 
                             " width=\"%s\"", " height=\"%s\"", 
                             ">\n             <Format>%s</Format", 
                             "\n             <OnlineResource "
                             "xmlns:xlink=\"http://www.w3.org/1999/xlink\""
                             " xlink:type=\"simple\" xlink:href=\"%s\"/>\n"
                             "          ",
                             MS_FALSE, MS_TRUE, MS_TRUE, MS_TRUE, MS_TRUE, 
                             NULL, NULL, NULL, NULL, NULL, "          ");
           msIO_fprintf(stdout, "        </Style>\n");
               
       }
       else
       {
           if (script_url_encoded)
           {
               if (lp->connectiontype != MS_WMS && 
                   lp->connectiontype != MS_WFS &&
                   lp->connectiontype != MS_UNUSED_1 &&
                   lp->numclasses > 0)
               {
                   char width[10], height[10];
                   char *legendurl = NULL;
                   int classnameset = 0, i=0;
                   for (i=0; i<lp->numclasses; i++)
                   {
                       if (lp->class[i].name && 
                           strlen(lp->class[i].name) > 0)
                       {
                           classnameset = 1;
                           break;
                       }
                   }
                   if (classnameset)
                   {
                       if (map->legend.keysizex > 0)
                         sprintf(width, "%d", map->legend.keysizex);
                       else
                         sprintf(width, "%d", 20);//default;

                       if (map->legend.keysizey > 0)
                          sprintf(height, "%d", map->legend.keysizey);
                       else
                         sprintf(height, "%d", 20);//default;
                   
                       legendurl = (char*)malloc(strlen(script_url_encoded)+200);

#ifdef USE_GD_PNG
                       mimetype = strdup("image/png");
#endif
#ifdef USE_GD_GIF
                       if (!mimetype)
                         mimetype = strdup("image/gif");
#endif

#ifdef USE_GD_JPEG
                       if (!mimetype)
                         mimetype = strdup("image/jpeg");
#endif
#ifdef USE_GD_WBMP
                       if (!mimetype)
                         mimetype = strdup("image/wbmp");
#endif
                       if (!mimetype)
                         mimetype = MS_IMAGE_MIME_TYPE(map->outputformat);         
                       mimetype = msEncodeHTMLEntities(mimetype);

                       sprintf(legendurl, "%sversion=%s&amp;service=WMS&amp;request=GetLegendGraphic&amp;layer=%s&amp;format=%s",  
                               script_url_encoded,"1.1.1",msEncodeHTMLEntities(lp->name),
                               mimetype);
                           
                       msIO_fprintf(stdout, "        <Style>\n");
                       msIO_fprintf(stdout, "          <Name>%s</Name>\n", pszStyle);
                       msIO_fprintf(stdout, "          <Title>%s</Title>\n", pszStyle);
                      
                       msOWSPrintURLType(stdout, NULL, 
                                         "O", "ttt",
                                         OWS_NOERR, NULL, 
                                         "LegendURL", NULL, 
                                         " width=\"%s\"", " height=\"%s\"", 
                                         ">\n             <Format>%s</Format", 
                                         "\n             <OnlineResource "
                                         "xmlns:xlink=\"http://www.w3.org/1999/xlink\""
                                         " xlink:type=\"simple\" xlink:href=\"%s\"/>\n"
                                         "          ",
                                         MS_FALSE, MS_FALSE, MS_FALSE, MS_FALSE, MS_FALSE, 
                                         NULL, width, height, mimetype, legendurl, "          ");
                       

                       msIO_fprintf(stdout, "        </Style>\n");
                       msFree(legendurl);
                       msFree(mimetype);

                   }
               }       
           }
       }
   }
   
   msFree(pszMetadataName);

   msWMSPrintScaleHint("        ", lp->minscale, lp->maxscale, map->resolution);

   msIO_printf("%s    </Layer>\n", indent);

   return MS_SUCCESS;
}

/*
 * msWMSPrepareNestedGroups
 */
void msWMSPrepareNestedGroups(mapObj* map, int nVersion, char*** nestedGroups, int* numNestedGroups)
{
  int i;
  const char* groups;
  char* errorMsg;

  for (i = 0; i < map->numlayers; i++)
  {
    nestedGroups[i] = NULL; //default
    numNestedGroups[i] = 0; //default
    
    groups = msOWSLookupMetadata(&(map->layers[i].metadata), "MO", "layer_group");
    if ((groups != NULL) && (strlen(groups) != 0))
    {
      if (map->layers[i].group != NULL && strlen(map->layers[i].group) != 0)
      {
        errorMsg = "It is not allowed to set both the GROUP and WMS_LAYER_GROUP for a layer";
        msSetError(MS_WMSERR, errorMsg, "msWMSPrepareNestedGroups()", NULL);
        msIO_fprintf(stdout, "<!-- ERROR: %s -->\n", errorMsg);
        //cannot return exception at this point because we are already writing to stdout
      }
      else
      {
        if (groups[0] != '/')
        {      
          errorMsg = "The WMS_LAYER_GROUP metadata does not start with a '/'";
          msSetError(MS_WMSERR, errorMsg, "msWMSPrepareNestedGroups()", NULL);
          msIO_fprintf(stdout, "<!-- ERROR: %s -->\n", errorMsg);
          //cannot return exception at this point because we are already writing to stdout
        }
        else
        {
          //split into subgroups. Start at adres + 1 because the first '/' would cause an extra emtpy group
          nestedGroups[i] = split(groups + 1, '/', &numNestedGroups[i]); 
        }
      }
    }
  }
}

/*
 * msWMSIsSubGroup
 */
int msWMSIsSubGroup(char** currentGroups, int currentLevel, char** otherGroups, int numOtherGroups)
{
   int i;
   if (numOtherGroups == 0 || numOtherGroups < currentLevel) 
   {
      return MS_FALSE;
   }
   //compare all groups below the current level
   for (i = 0; i <= currentLevel; i++)
   {
      if (strncmp(currentGroups[i], otherGroups[i], strlen(currentGroups[i])) != 0)
      {
         return MS_FALSE; // if one of these is not equal it is not a sub group
      }
   }
   return MS_TRUE;
}

/***********************************************************************************
 * msWMSPrintNestedGroups()                                                        *
 *                                                                                 *
 * purpose: Writes the layers to the capabilities that have the                     *
 * "WMS_LAYER_GROUP" metadata set.                                                 *
 *                                                                                 *
 * params:                                                                         *
 * -map: The main map object                                                       *      
 * -nVersion: OGC WMS version                                                      *
 * -pabLayerProcessed: boolean array indicating which layers have been dealt with. *
 * -index: the index of the current layer.                                         *
 * -level: the level of depth in the group tree (root = 0)                         *
 * -nestedGroups: This array holds the arrays of groups that have                  *
 *   been set through the WMS_LAYER_GROUP metadata                                 *
 * -numNestedGroups: This array holds the number of nested groups for each layer   *
 ***********************************************************************************/
void msWMSPrintNestedGroups(mapObj* map, int nVersion, char* pabLayerProcessed, 
	int index, int level, char*** nestedGroups, int* numNestedGroups, const char *script_url_encoded)
{
   int j;

   if (numNestedGroups[index] <= level) //no more subgroups
   {
      //we are at the deepest level of the group branchings, so add layer now.
      msDumpLayer(map, &map->layers[index], nVersion, script_url_encoded, "");
      pabLayerProcessed[index] = 1; //done
   }
   else //not yet there, we have to deal with this group and possible subgroups and layers.
   {
      // Beginning of a new group... enclose the group in a layer block
      msIO_printf("    <Layer>\n");
      msIO_printf("    <Title>%s</Title>\n", nestedGroups[index][level]);      

      //Look for one group deeper in the current layer
      if (!pabLayerProcessed[index])
      {
         msWMSPrintNestedGroups(map, nVersion, pabLayerProcessed,
                                index, level + 1, nestedGroups, 
                                numNestedGroups, script_url_encoded);
      }

      //look for subgroups in other layers.
      for (j = index + 1; j < map->numlayers; j++) 
      {
         if (msWMSIsSubGroup(nestedGroups[index], level, nestedGroups[j], numNestedGroups[j]))
         {
            if (!pabLayerProcessed[j])
            {
               msWMSPrintNestedGroups(map, nVersion, pabLayerProcessed,
                                      j, level + 1, nestedGroups, 
                                      numNestedGroups, script_url_encoded);
            }
         }
         else
         {
            //TODO: if we would sort all layers on "WMS_LAYER_GROUP" beforehand
            //we could break out of this loop at this point, which would increase
            //performance. 
         }
      }
      // Close group layer block
      msIO_printf("    </Layer>\n");
   }
   
} // msWMSPrintNestedGroups

/*
** msWMSGetCapabilities()
*/
int msWMSGetCapabilities(mapObj *map, int nVersion, cgiRequestObj *req)
{
  char *dtd_url = NULL;
  char *script_url=NULL, *script_url_encoded=NULL;
  const char *pszMimeType=NULL;
  char szVersionBuf[OWS_VERSION_MAXLEN];
  char *schemalocation = NULL;


   schemalocation = msEncodeHTMLEntities( msOWSGetSchemasLocation(map) );

  if (nVersion < 0)
      nVersion = OWS_1_1_1;     // Default to 1.1.1

  // Decide which version we're going to return.
  if (nVersion < OWS_1_0_7) {
    nVersion = OWS_1_0_0;
    dtd_url = strdup(schemalocation);
    dtd_url = strcatalloc(dtd_url, "/wms/1.0.0/capabilities_1_0_0.dtd");
  }

  else if (nVersion < OWS_1_1_0) {
    nVersion = OWS_1_0_7;
    dtd_url = strdup(schemalocation);
    dtd_url = strcatalloc(dtd_url, "/wms/1.0.7/capabilities_1_0_7.dtd");
  }
  else if (nVersion == OWS_1_1_0) {
    nVersion = OWS_1_1_0;
    dtd_url = strdup(schemalocation);
    dtd_url = strcatalloc(dtd_url, "/wms/1.1.0/capabilities_1_1_0.dtd");
  }
  else {
    nVersion = OWS_1_1_1;
    dtd_url = strdup(schemalocation);
    dtd_url = strcatalloc(dtd_url, "/wms/1.1.1/capabilities_1_1_1.dtd");
  }

  // We need this server's onlineresource.
  // Default to use the value of the "onlineresource" metadata, and if not
  // set then build it: "http://$(SERVER_NAME):$(SERVER_PORT)$(SCRIPT_NAME)?"
  // the returned string should be freed once we're done with it.
  if ((script_url=msOWSGetOnlineResource(map, "MO", "onlineresource", req)) == NULL ||
      (script_url_encoded = msEncodeHTMLEntities(script_url)) == NULL)
  {
      return msWMSException(map, nVersion, NULL);
  }

  if (nVersion <= OWS_1_0_7)
      msIO_printf("Content-type: text/xml%c%c",10,10);  // 1.0.0 to 1.0.7
  else
      msIO_printf("Content-type: application/vnd.ogc.wms_xml%c%c",10,10);  // 1.1.0 and later

  msOWSPrintEncodeMetadata(stdout, &(map->web.metadata),
                           "MO", "encoding", OWS_NOERR,
                "<?xml version='1.0' encoding=\"%s\" standalone=\"no\" ?>\n",
                "ISO-8859-1");
  msIO_printf("<!DOCTYPE WMT_MS_Capabilities SYSTEM \"%s\"\n", dtd_url);
  msIO_printf(" [\n");

  // some mapserver specific declarations will go here
  msIO_printf(" <!ELEMENT VendorSpecificCapabilities EMPTY>\n");

  msIO_printf(" ]>  <!-- end of DOCTYPE declaration -->\n\n");

  msIO_printf("<WMT_MS_Capabilities version=\"%s\">\n",
         msOWSGetVersionString(nVersion, szVersionBuf));

  // Report MapServer Version Information
  msIO_printf("\n<!-- %s -->\n\n", msGetVersion());

  // WMS definition
  msIO_printf("<Service>\n");

  // Service name is defined by the spec and changed at v1.0.0
  if (nVersion <= OWS_1_0_7)
      msIO_printf("  <Name>GetMap</Name>\n");  // v 1.0.0 to 1.0.7
  else
      msIO_printf("  <Name>OGC:WMS</Name>\n"); // v 1.1.0+

  // the majority of this section is dependent on appropriately named metadata in the WEB object
  msOWSPrintEncodeMetadata(stdout, &(map->web.metadata), "MO", "title",
                           OWS_WARN, "  <Title>%s</Title>\n", map->name);
  msOWSPrintEncodeMetadata(stdout, &(map->web.metadata), "MO", "abstract",
                           OWS_NOERR, "  <Abstract>%s</Abstract>\n", NULL);

  if (nVersion == OWS_1_0_0)
  {
      // <Keywords> in V 1.0.0
      // The 1.0.0 spec doesn't specify which delimiter to use so let's use spaces
      msOWSPrintEncodeMetadataList(stdout, &(map->web.metadata),
                                   "MO", "keywordlist",
                                   "        <Keywords>",
                                   "        </Keywords>\n",
                                   "%s ", NULL);
  }
  else
  {
      // <KeywordList><Keyword> ... in V1.0.6+
      msOWSPrintEncodeMetadataList(stdout, &(map->web.metadata),
                                   "MO", "keywordlist",
                                   "        <KeywordList>\n",
                                   "        </KeywordList>\n",
                                   "          <Keyword>%s</Keyword>\n", NULL);
  }

  // Service/onlineresource
  // Defaults to same as request onlineresource if wms_service_onlineresource 
  // is not set.
  if (nVersion== OWS_1_0_0)
    msOWSPrintEncodeMetadata(stdout, &(map->web.metadata), 
                             "MO", "service_onlineresource", OWS_NOERR,
                             "  <OnlineResource>%s</OnlineResource>\n", 
                             script_url_encoded);
  else
    msOWSPrintEncodeMetadata(stdout, &(map->web.metadata), 
                             "MO", "service_onlineresource", OWS_NOERR,
                             "  <OnlineResource xmlns:xlink=\"http://www.w3.org/1999/xlink\" xlink:href=\"%s\"/>\n", 
                             script_url_encoded);

  // contact information is a required element in 1.0.7 but the
  // sub-elements such as ContactPersonPrimary, etc. are not!
  // In 1.1.0, ContactInformation becomes optional.
  msOWSPrintContactInfo(stdout, "  ", nVersion, &(map->web.metadata), "MO");

  msOWSPrintEncodeMetadata(stdout, &(map->web.metadata), "MO", "fees",
                           OWS_NOERR, "  <Fees>%s</Fees>\n", NULL);

  msOWSPrintEncodeMetadata(stdout, &(map->web.metadata), "MO",
                           "accessconstraints", OWS_NOERR,
                        "  <AccessConstraints>%s</AccessConstraints>\n", NULL);

  msIO_printf("</Service>\n\n");

  // WMS capabilities definitions
  msIO_printf("<Capability>\n");
  msIO_printf("  <Request>\n");

  if (nVersion <= OWS_1_0_7)
  {
    // WMS 1.0.0 to 1.0.7 - We don't try to use outputformats list here for now
    msWMSPrintRequestCap(nVersion, "Map", script_url_encoded, ""
#ifdef USE_GD_GIF
                      "<GIF />"
#endif
#ifdef USE_GD_PNG
                      "<PNG />"
#endif
#ifdef USE_GD_JPEG
                      "<JPEG />"
#endif
#ifdef USE_GD_WBMP
                      "<WBMP />"
#endif
                      , NULL);
    msWMSPrintRequestCap(nVersion, "Capabilities", script_url_encoded, "<WMS_XML />", NULL);
    msWMSPrintRequestCap(nVersion, "FeatureInfo", script_url_encoded, "<MIME /><GML.1 />", NULL);
  }
  else
  {
    char *mime_list[20];
    // WMS 1.1.0 and later
    // Note changes to the request names, their ordering, and to the formats

    msWMSPrintRequestCap(nVersion, "GetCapabilities", script_url_encoded,
                    "application/vnd.ogc.wms_xml",
                    NULL);

    msGetOutputFormatMimeListRaster(map,mime_list,sizeof(mime_list)/sizeof(char*));
    msWMSPrintRequestCap(nVersion, "GetMap", script_url_encoded,
                    mime_list[0], mime_list[1], mime_list[2], mime_list[3],
                    mime_list[4], mime_list[5], mime_list[6], mime_list[7],
                    mime_list[8], mime_list[9], mime_list[10], mime_list[11],
                    mime_list[12], mime_list[13], mime_list[14], mime_list[15],
                    mime_list[16], mime_list[17], mime_list[18], mime_list[19],
                    NULL );

    pszMimeType = msOWSLookupMetadata(&(map->web.metadata), "MO", 
                                      "feature_info_mime_type");

    if (pszMimeType)
      msWMSPrintRequestCap(nVersion, "GetFeatureInfo", script_url_encoded,
                           "text/plain",
                           pszMimeType,
                           "application/vnd.ogc.gml",
                           NULL);
    else
       msWMSPrintRequestCap(nVersion, "GetFeatureInfo", script_url_encoded,
                       "text/plain",
                       "application/vnd.ogc.gml",
                       NULL);

    msWMSPrintRequestCap(nVersion, "DescribeLayer", script_url_encoded,
                         "text/xml",
                         NULL);

    msGetOutputFormatMimeListGD(map,mime_list,sizeof(mime_list)/sizeof(char*));
    msWMSPrintRequestCap(nVersion, "GetLegendGraphic", script_url_encoded,
                    mime_list[0], mime_list[1], mime_list[2], mime_list[3],
                    mime_list[4], mime_list[5], mime_list[6], mime_list[7],
                    mime_list[8], mime_list[9], mime_list[10], mime_list[11],
                    mime_list[12], mime_list[13], mime_list[14], mime_list[15],
                    mime_list[16], mime_list[17], mime_list[18], mime_list[19],
                    NULL );
  }

  msIO_printf("  </Request>\n");

  msIO_printf("  <Exception>\n");
  if (nVersion <= OWS_1_0_7)
      msIO_printf("    <Format><BLANK /><INIMAGE /><WMS_XML /></Format>\n");
  else
  {
      // 1.1.0 and later
      msIO_printf("    <Format>application/vnd.ogc.se_xml</Format>\n");
      msIO_printf("    <Format>application/vnd.ogc.se_inimage</Format>\n");
      msIO_printf("    <Format>application/vnd.ogc.se_blank</Format>\n");
  }
  msIO_printf("  </Exception>\n");


  msIO_printf("  <VendorSpecificCapabilities />\n"); // nothing yet

  //SLD support
  msIO_printf("  <UserDefinedSymbolization SupportSLD=\"1\" UserLayer=\"0\" UserStyle=\"1\" RemoteWFS=\"0\"/>\n");

  // Top-level layer with map extents and SRS, encloses all map layers
  msIO_printf("  <Layer>\n");

  // Layer Name is optional but title is mandatory.
  if (map->name && strlen(map->name) > 0 &&
      (msIsXMLTagValid(map->name) == MS_FALSE || isdigit(map->name[0])))
    msIO_fprintf(stdout, "<!-- WARNING: The layer name '%s' might contain spaces or "
                 "invalid characters or may start with a number. This could lead to potential problems. -->\n", 
                 map->name);
  msOWSPrintEncodeParam(stdout, "MAP.NAME", map->name, OWS_NOERR,
                        "    <Name>%s</Name>\n", NULL);
  msOWSPrintEncodeMetadata(stdout, &(map->web.metadata), "MO", "title",
                           OWS_WARN, "    <Title>%s</Title>\n", map->name);

  // According to normative comments in the 1.0.7 DTD, the root layer's SRS tag
  // is REQUIRED.  It also suggests that we use an empty SRS element if there
  // is no common SRS.
  msOWSPrintEncodeParam(stdout, "MAP.PROJECTION (or wms_srs metadata)",
             msOWSGetEPSGProj(&(map->projection), &(map->web.metadata),
                              "MO", MS_FALSE),
                        OWS_WARN, "    <SRS>%s</SRS>\n", "");

  msOWSPrintLatLonBoundingBox(stdout, "    ", &(map->extent),
                              &(map->projection), OWS_WMS);
  msOWSPrintBoundingBox( stdout, "    ", &(map->extent), &(map->projection),
                         &(map->web.metadata), "MO" );
  msWMSPrintScaleHint("    ", map->web.minscale, map->web.maxscale,
                      map->resolution);


  //
  // Dump list of layers organized by groups.  Layers with no group are listed
  // individually, at the same level as the groups in the layer hierarchy
  //
  if (map->numlayers)
  {
     int i, j;
     char *pabLayerProcessed = NULL;
     char ***nestedGroups = NULL; 
     int *numNestedGroups = NULL; 

     // We'll use this array of booleans to track which layer/group have been
     // processed already
     pabLayerProcessed = (char *)calloc(map->numlayers, sizeof(char*));
     // This array holds the arrays of groups that have been set through the WMS_LAYER_GROUP metadata
     nestedGroups = (char***)calloc(map->numlayers, sizeof(char**));
     // This array holds the number of groups set in WMS_LAYER_GROUP for each layer
     numNestedGroups = (int*)calloc(map->numlayers, sizeof(int));

     msWMSPrepareNestedGroups(map, nVersion, nestedGroups, numNestedGroups);

     for(i=0; i<map->numlayers; i++)
     {
         layerObj *lp;
         lp = &(map->layers[i]);

         if (pabLayerProcessed[i])
             continue;  // Layer has already been handled


         if (numNestedGroups[i] > 0) 
         {
            // Has nested groups. 
             msWMSPrintNestedGroups(map, nVersion, pabLayerProcessed, i, 0, 
                                    nestedGroups, numNestedGroups, 
                                    script_url_encoded);
         }
         else if (lp->group == NULL || strlen(lp->group) == 0)
         {
             // This layer is not part of a group... dump it directly
             msDumpLayer(map, lp, nVersion, script_url_encoded, "");
             pabLayerProcessed[i] = 1;
         }
         else
         {
             // Beginning of a new group... enclose the group in a layer block
             msIO_printf("    <Layer>\n");

             // Layer Name is optional but title is mandatory.
             if (lp->group &&  strlen(lp->group) > 0 &&
                 (msIsXMLTagValid(lp->group) == MS_FALSE || isdigit(lp->group[0])))
               msIO_fprintf(stdout, "<!-- WARNING: The layer name '%s' might contain spaces or "
                        "invalid characters or may start with a number. This could lead to potential problems. -->\n", 
                            lp->group);
             msOWSPrintEncodeParam(stdout, "GROUP.NAME", lp->group,
                                   OWS_NOERR, "      <Name>%s</Name>\n", NULL);
             msOWSPrintGroupMetadata(stdout, map, lp->group,
                                     "MO", "GROUP_TITLE", OWS_WARN,
                                     "      <Title>%s</Title>\n", lp->group);
             msOWSPrintGroupMetadata(stdout, map, lp->group,
                                     "MO", "GROUP_ABSTRACT", OWS_NOERR,
                                     "      <Abstract>%s</Abstract>\n", lp->group);

             // Dump all layers for this group
             for(j=i; j<map->numlayers; j++)
             {
                 if (!pabLayerProcessed[j] &&
                     map->layers[j].group &&
                     strcmp(lp->group, map->layers[j].group) == 0 )
                 {
                     msDumpLayer(map, &(map->layers[j]), nVersion, script_url_encoded, "  ");
                     pabLayerProcessed[j] = 1;
                 }
             }

             // Close group layer block
             msIO_printf("    </Layer>\n");
         }
     }

     free(pabLayerProcessed);

     //free the stuff used for nested layers
     for (i = 0; i < map->numlayers; i++)
     {
       if (numNestedGroups[i] > 0)
       {
         msFreeCharArray(nestedGroups[i], numNestedGroups[i]);
       }
     }
     free(nestedGroups);
     free(numNestedGroups);


  }

  msIO_printf("  </Layer>\n");

  msIO_printf("</Capability>\n");
  msIO_printf("</WMT_MS_Capabilities>\n");

  free(script_url);
  free(script_url_encoded);

  free(dtd_url);
  free(schemalocation);

  return(MS_SUCCESS);
}

/*
 * This function look for params that can be used
 * by mapserv when generating template.
*/
int msTranslateWMS2Mapserv(char **names, char **values, int *numentries)
{
   int i=0;
   int tmpNumentries = *numentries;;

   for (i=0; i<*numentries; i++)
   {
      if (strcasecmp("X", names[i]) == 0)
      {
         values[tmpNumentries] = strdup(values[i]);
         names[tmpNumentries] = strdup("img.x");

         tmpNumentries++;
      }
      else
      if (strcasecmp("Y", names[i]) == 0)
      {
         values[tmpNumentries] = strdup(values[i]);
         names[tmpNumentries] = strdup("img.y");

         tmpNumentries++;
      }
      else
      if (strcasecmp("LAYERS", names[i]) == 0)
      {
         char **layers;
         int tok;
         int j;

         layers = split(values[i], ',', &tok);

         for (j=0; j<tok; j++)
         {
            values[tmpNumentries] = layers[j];
            layers[j] = NULL;
            names[tmpNumentries] = strdup("layer");

            tmpNumentries++;
         }

         free(layers);
      }
      else
      if (strcasecmp("QUERY_LAYERS", names[i]) == 0)
      {
         char **layers;
         int tok;
         int j;

         layers = split(values[i], ',', &tok);

         for (j=0; j<tok; j++)
         {
            values[tmpNumentries] = layers[j];
            layers[j] = NULL;
            names[tmpNumentries] = strdup("qlayer");

            tmpNumentries++;
         }

         free(layers);
      }
      else
      if (strcasecmp("BBOX", names[i]) == 0)
      {
         char *imgext;

         // Note gsub() works on the string itself, so we need to make a copy
         imgext = strdup(values[i]);
         imgext = gsub(imgext, ",", " ");

         values[tmpNumentries] = imgext;
         names[tmpNumentries] = strdup("imgext");

         tmpNumentries++;
      }
   }

   *numentries = tmpNumentries;

   return MS_SUCCESS;
}

/*
** msWMSGetMap()
*/
int msWMSGetMap(mapObj *map, int nVersion, char **names, char **values, int numentries)
{
  imageObj *img;
  int i = 0;
  int sldrequested = MS_FALSE,  sldspatialfilter = MS_FALSE;

  // __TODO__ msDrawMap() will try to adjust the extent of the map
  // to match the width/height image ratio.
  // The spec states that this should not happen so that we can deliver
  // maps to devices with non-square pixels.


//      If there was an SLD in the request, we need to treat it
//      diffrently : some SLD may contain spatial filters requiring
//      to do a query. While parsing the SLD and applying it to the
//      layer, we added a temporary metadata on the layer
//      (tmp_wms_sld_query) for layers with a spatial filter.

  for (i=0; i<numentries; i++)
  {
    if ((strcasecmp(names[i], "SLD") == 0 && values[i] && strlen(values[i]) > 0) ||
        (strcasecmp(names[i], "SLD_BODY") == 0 && values[i] && strlen(values[i]) > 0))
    {
        sldrequested = MS_TRUE;
        break;
    }
  }
  if (sldrequested)
  {
      for (i=0; i<map->numlayers; i++)
      {
          if (msLookupHashTable(&(map->layers[i].metadata), "tmp_wms_sld_query"))
          {
              sldspatialfilter = MS_TRUE;
              break;
          }
      }
  }

  if (sldrequested && sldspatialfilter)
  {
      //set the quermap style so that only selected features will be retruned
      map->querymap.status = MS_ON;
      map->querymap.style = MS_SELECTED;

      img = msImageCreate(map->width, map->height, map->outputformat,
                          map->web.imagepath, map->web.imageurl,
                          map);
      map->cellsize = msAdjustExtent(&(map->extent), map->width, map->height);
      msCalculateScale(map->extent, map->units, map->width,
                       map->height, map->resolution, &map->scale);
      // compute layer scale factors now
      for(i=0;i<map->numlayers; i++) {
          if(map->layers[i].sizeunits != MS_PIXELS)
            map->layers[i].scalefactor = (msInchesPerUnit(map->layers[i].sizeunits,0)/msInchesPerUnit(map->units,0)) / map->cellsize;
          else if(map->layers[i].symbolscale > 0 && map->scale > 0)
            map->layers[i].scalefactor = map->layers[i].symbolscale/map->scale;
          else
            map->layers[i].scalefactor = 1;
      }
      for (i=0; i<map->numlayers; i++)
      {
          if (msLookupHashTable(&(map->layers[i].metadata), "tmp_wms_sld_query") &&
              (map->layers[i].type == MS_LAYER_POINT || 
               map->layers[i].type == MS_LAYER_LINE ||
               map->layers[i].type == MS_LAYER_POLYGON ||
               map->layers[i].type == MS_LAYER_ANNOTATION ||
               map->layers[i].type == MS_LAYER_TILEINDEX))
               
          {
              //make sure that there is a resultcache. If not just ignore
              //the layer
              if (map->layers[i].resultcache)
                msDrawQueryLayer(map, &map->layers[i], img);
          }

          else
            msDrawLayer(map, &map->layers[i], img);
      }

  }
  else
    img = msDrawMap(map);
  if (img == NULL)
      return msWMSException(map, nVersion, NULL);

  
  msIO_printf("Content-type: %s%c%c",
              MS_IMAGE_MIME_TYPE(map->outputformat), 10,10);
  if (msSaveImage(map, img, NULL) != MS_SUCCESS)
      return msWMSException(map, nVersion, NULL);

  msFreeImage(img);

  return(MS_SUCCESS);
}

int msDumpResult(mapObj *map, int bFormatHtml, int nVersion, int feature_count)
{
   int numresults=0;
   int i;

   for(i=0; i<map->numlayers && numresults<feature_count; i++)
   {
      int j, k;
      layerObj *lp;
      lp = &(map->layers[i]);

      if(lp->status != MS_ON || lp->resultcache==NULL || lp->resultcache->numresults == 0)
        continue;

      if(msLayerOpen(lp) != MS_SUCCESS || msLayerGetItems(lp) != MS_SUCCESS)
        return msWMSException(map, nVersion, NULL);

      msIO_printf("\nLayer '%s'\n", lp->name);

      for(j=0; j<lp->resultcache->numresults && numresults<feature_count; j++) {
        shapeObj shape;

        msInitShape(&shape);
        if (msLayerGetShape(lp, &shape, lp->resultcache->results[j].tileindex, lp->resultcache->results[j].shapeindex) != MS_SUCCESS)
          return msWMSException(map, nVersion, NULL);

        msIO_printf("  Feature %ld: \n", lp->resultcache->results[j].shapeindex);

        for(k=0; k<lp->numitems; k++)
	  msIO_printf("    %s = '%s'\n", lp->items[k], shape.values[k]);

        msFreeShape(&shape);
        numresults++;
      }

      msLayerClose(lp);
    }

   return numresults;
}


/*
** msWMSFeatureInfo()
*/
int msWMSFeatureInfo(mapObj *map, int nVersion, char **names, char **values, int numentries)
{
  int i, feature_count=1, numlayers_found=0;
  pointObj point = {-1.0, -1.0};
  const char *info_format="MIME";
  double cellx, celly;
  errorObj *ms_error = msGetErrorObj();
  int status;
  const char *pszMimeType=NULL;
  int query_layer = 0;


  pszMimeType = msOWSLookupMetadata(&(map->web.metadata), "MO", "FEATURE_INFO_MIME_TYPE");

  for(i=0; map && i<numentries; i++) {
    if(strcasecmp(names[i], "QUERY_LAYERS") == 0) {
      char **layers;
      int numlayers, j, k;

      query_layer = 1; //flag set if QUERY_LAYERS is the request

      layers = split(values[i], ',', &numlayers);
      if(layers==NULL || numlayers < 1 || strlen(trimLeft(values[i])) < 1) {
        msSetError(MS_WMSERR, "At least one layer name required in QUERY_LAYERS.", "msWMSFeatureInfo()");
        return msWMSException(map, nVersion, "LayerNotDefined");
      }

      for(j=0; j<map->numlayers; j++) {
        // Force all layers OFF by default
	map->layers[j].status = MS_OFF;

        for(k=0; k<numlayers; k++) {
          if ((map->layers[j].name && strcasecmp(map->layers[j].name, layers[k]) == 0) ||
              (map->name && strcasecmp(map->name, layers[k]) == 0) ||
              (map->layers[j].group && strcasecmp(map->layers[j].group, layers[k]) == 0))
            {
              map->layers[j].status = MS_ON;
              numlayers_found++;
            }
        }
      }

      msFreeCharArray(layers, numlayers);
    } else if (strcasecmp(names[i], "INFO_FORMAT") == 0)
      info_format = values[i];
    else if (strcasecmp(names[i], "FEATURE_COUNT") == 0)
      feature_count = atoi(values[i]);
    else if(strcasecmp(names[i], "X") == 0)
      point.x = atof(values[i]);
    else if (strcasecmp(names[i], "Y") == 0)
      point.y = atof(values[i]);
    else if (strcasecmp(names[i], "RADIUS") == 0)
    {
        // RADIUS in pixels.
        // This is not part of the spec, but some servers such as cubeserv
        // support it as a vendor-specific feature.
        // It's easy for MapServer to handle this so let's do it!
        int j;
        for(j=0; j<map->numlayers; j++)
        {
            map->layers[j].tolerance = atoi(values[i]);
            map->layers[j].toleranceunits = MS_PIXELS;
        }
    }

  }

  if(numlayers_found == 0) 
  {
      if (query_layer)
      {
          msSetError(MS_WMSERR, "Layer(s) specified in QUERY_LAYERS parameter is not offered by the service instance.", "msWMSFeatureInfo()");
          return msWMSException(map, nVersion, "LayerNotDefined");
      }
      else
      {
          msSetError(MS_WMSERR, "Required QUERY_LAYERS parameter missing for getFeatureInfo.", "msWMSFeatureInfo()");
          return msWMSException(map, nVersion, "LayerNotDefined");
      }
  }

/* -------------------------------------------------------------------- */
/*      check if all layers selected are queryable. If not send an      */
/*      exception.                                                      */
/* -------------------------------------------------------------------- */
  for (i=0; i<map->numlayers; i++)
  {
      if (map->layers[i].status == MS_ON && !msIsLayerQueryable(&map->layers[i]))
      {
          msSetError(MS_WMSERR, "Requested layer(s) are not queryable.", "msWMSFeatureInfo()");
          return msWMSException(map, nVersion, "LayerNotQueryable");
      }
  }
  if(point.x == -1.0 || point.y == -1.0) {
    msSetError(MS_WMSERR, "Required X/Y parameters missing for getFeatureInfo.", "msWMSFeatureInfo()");
    return msWMSException(map, nVersion, NULL);
  }

  // Perform the actual query
  cellx = MS_CELLSIZE(map->extent.minx, map->extent.maxx, map->width); // note: don't adjust extent, WMS assumes incoming extent is correct
  celly = MS_CELLSIZE(map->extent.miny, map->extent.maxy, map->height);
  point.x = MS_IMAGE2MAP_X(point.x, map->extent.minx, cellx);
  point.y = MS_IMAGE2MAP_Y(point.y, map->extent.maxy, celly);

  if(msQueryByPoint(map, -1, (feature_count==1?MS_SINGLE:MS_MULTIPLE), point, 0) != MS_SUCCESS)
    if(ms_error->code != MS_NOTFOUND) return msWMSException(map, nVersion, NULL);

  // Generate response
  if (strcasecmp(info_format, "MIME") == 0 ||
      strcasecmp(info_format, "text/plain") == 0) {

    // MIME response... we're free to use any valid MIME type
    int numresults = 0;

    msIO_printf("Content-type: text/plain%c%c", 10,10);
    msIO_printf("GetFeatureInfo results:\n");

    numresults = msDumpResult(map, 0, nVersion, feature_count);

    if (numresults == 0) msIO_printf("\n  Search returned no results.\n");

  } else if (strncasecmp(info_format, "GML", 3) == 0 ||  // accept GML.1 or GML
             strcasecmp(info_format, "application/vnd.ogc.gml") == 0) {

    if (nVersion <= OWS_1_0_7)
        msIO_printf("Content-type: text/xml%c%c", 10,10);
    else
        msIO_printf("Content-type: application/vnd.ogc.gml%c%c", 10,10);

    msGMLWriteQuery(map, NULL, "GMO"); // default is stdout

  } else
  if (pszMimeType && (strcmp(pszMimeType, info_format) == 0))
  {
     mapservObj *msObj;

     msObj = msAllocMapServObj();

     // Translate some vars from WMS to mapserv
     msTranslateWMS2Mapserv(names, values, &numentries);

     msObj->Map = map;
     msObj->request->ParamNames = names;
     msObj->request->ParamValues = values;
     msObj->Mode = QUERY;
     sprintf(msObj->Id, "%ld%d",(long)time(NULL),(int)getpid()); // asign now so it can be overridden
     msObj->request->NumParams = numentries;
     msObj->MapPnt.x = point.x;
     msObj->MapPnt.y = point.y;

     if ((status = msReturnTemplateQuery(msObj, (char*)pszMimeType,NULL)) != MS_SUCCESS)
         return msWMSException(map, nVersion, NULL);

     // We don't want to free the map, and param names/values since they
     // belong to the caller, set them to NULL before freeing the mapservObj
     msObj->Map = NULL;
     msObj->request->ParamNames = NULL;
     msObj->request->ParamValues = NULL;
     msObj->request->NumParams = 0;

     msFreeMapServObj(msObj);
  }
  else
  {
     msSetError(MS_WMSERR, "Unsupported INFO_FORMAT value (%s).", "msWMSFeatureInfo()", info_format);
     return msWMSException(map, nVersion, NULL);
  }

  return(MS_SUCCESS);
}

/*
** msWMSDescribeLayer()
*/
int msWMSDescribeLayer(mapObj *map, int nVersion, char **names,
                       char **values, int numentries)
{
  int i = 0;
  char **layers = NULL;
  int numlayers = 0;
  int j, k;
  layerObj *lp = NULL;
  const char *pszOnlineResMapWFS = NULL, *pszOnlineResLyrWFS = NULL; 
  const char *pszOnlineResMapWCS = NULL, *pszOnlineResLyrWCS = NULL;
  char *pszOnlineResEncoded=NULL, *pszLayerName=NULL;
  char *schemalocation = NULL;

   for(i=0; map && i<numentries; i++) {
     if(strcasecmp(names[i], "LAYERS") == 0) {

      layers = split(values[i], ',', &numlayers);
     }
   }

   msOWSPrintEncodeMetadata(stdout, &(map->web.metadata),
                            "MO", "encoding", OWS_NOERR,
                            "<?xml version='1.0' encoding=\"%s\"?>\n",
                            "ISO-8859-1");
   schemalocation = msEncodeHTMLEntities(msOWSGetSchemasLocation(map));
   msIO_printf("<!DOCTYPE WMS_DescribeLayerResponse SYSTEM \"%s/wms/1.1.1/WMS_DescribeLayerResponse.dtd\">\n", schemalocation);
   free(schemalocation);

   msIO_printf("<WMS_DescribeLayerResponse version=\"1.1.0\" >\n");

   //check if map-level metadata wfs(wcs)_onlineresource is available
   pszOnlineResMapWFS = msOWSLookupMetadata(&(map->web.metadata), "FO", "onlineresource");
   if (pszOnlineResMapWFS && strlen(pszOnlineResMapWFS) == 0)
       pszOnlineResMapWFS = NULL;

   pszOnlineResMapWCS = msOWSLookupMetadata(&(map->web.metadata), "CO", "onlineresource");
   if (pszOnlineResMapWCS && strlen(pszOnlineResMapWCS) == 0)
     pszOnlineResMapWCS = NULL;

   for(j=0; j<numlayers; j++)
   {
       for(k=0; k<map->numlayers; k++)
       {
         lp = &map->layers[k];
         if (lp->name && strcasecmp(lp->name, layers[j]) == 0)
         {
             /* Look for a WFS onlineresouce at the layer level and then at
              * the map level.
              */
           pszOnlineResLyrWFS = msOWSLookupMetadata(&(lp->metadata), "FO",
                                                    "onlineresource");
           pszOnlineResLyrWCS = msOWSLookupMetadata(&(lp->metadata), "CO",
                                                    "onlineresource");
           if (pszOnlineResLyrWFS == NULL || strlen(pszOnlineResLyrWFS) == 0)
               pszOnlineResLyrWFS = pszOnlineResMapWFS;

           if (pszOnlineResLyrWCS == NULL || strlen(pszOnlineResLyrWCS) == 0)
               pszOnlineResLyrWCS = pszOnlineResMapWCS;

           if (pszOnlineResLyrWFS && (lp->type == MS_LAYER_POINT ||
                                      lp->type == MS_LAYER_LINE ||
                                      lp->type == MS_LAYER_POLYGON) )
           {
             pszOnlineResEncoded = msEncodeHTMLEntities(pszOnlineResLyrWFS);
             pszLayerName = msEncodeHTMLEntities(lp->name);

             msIO_printf("<LayerDescription name=\"%s\" wfs=\"%s\" owsType=\"WFS\" owsURL=\"%s\">\n",
                    pszLayerName, pszOnlineResEncoded, pszOnlineResEncoded);
             msIO_printf("<Query typeName=\"%s\" />\n", pszLayerName);
             msIO_printf("</LayerDescription>\n");

             msFree(pszOnlineResEncoded);
             msFree(pszLayerName);
           }
           else if (pszOnlineResLyrWCS && lp->type == MS_LAYER_RASTER)
           {
               pszOnlineResEncoded = msEncodeHTMLEntities(pszOnlineResLyrWCS);
               pszLayerName = msEncodeHTMLEntities(lp->name);

               msIO_printf("<LayerDescription name=\"%s\"  owsType=\"WCS\" owsURL=\"%s\">\n",
                    pszLayerName, pszOnlineResEncoded);
             msIO_printf("<Query typeName=\"%s\" />\n", pszLayerName);
             msIO_printf("</LayerDescription>\n");

             msFree(pszOnlineResEncoded);
             msFree(pszLayerName);
           }
           else
           {
             char *pszLayerName;
             pszLayerName = msEncodeHTMLEntities(lp->name);

             msIO_printf("<LayerDescription name=\"%s\"></LayerDescription>\n",
                    pszLayerName);

             msFree(pszLayerName);
           }
           break;
         }
       }
   }

   msIO_printf("</WMS_DescribeLayerResponse>\n");

   if (layers)
     msFreeCharArray(layers, numlayers);

   return(MS_SUCCESS);
}


/*
** msWMSGetLegendGraphic()
*/
int msWMSGetLegendGraphic(mapObj *map, int nVersion, char **names,
                       char **values, int numentries)
{
    char *pszLayer = NULL;
    char *pszFormat = NULL;
	  char *psRule = NULL;
    char *psScale = NULL;
    int iLayerIndex = -1;
    outputFormatObj *psFormat = NULL;
    imageObj *img=NULL;
    int i = 0;
    int nWidth = -1, nHeight =-1;

     for(i=0; map && i<numentries; i++)
     {
         if (strcasecmp(names[i], "LAYER") == 0)
         {
             pszLayer = values[i];
         }
         else if (strcasecmp(names[i], "WIDTH") == 0)
           nWidth = atoi(values[i]);
         else if (strcasecmp(names[i], "HEIGHT") == 0)
           nHeight = atoi(values[i]);
         else if (strcasecmp(names[i], "FORMAT") == 0)
           pszFormat = values[i];
#ifdef USE_OGR
/* -------------------------------------------------------------------- */
/*      SLD support :                                                   */
/*        - check if the SLD parameter is there. it is supposed to      */
/*      refer a valid URL containing an SLD document.                   */
/*        - check the SLD_BODY parameter that should contain the SLD    */
/*      xml string.                                                     */
/* -------------------------------------------------------------------- */
         else if (strcasecmp(names[i], "SLD") == 0 &&
                  values[i] && strlen(values[i]) > 0)
             msSLDApplySLDURL(map, values[i], -1, NULL);
         else if (strcasecmp(names[i], "SLD_BODY") == 0 &&
                  values[i] && strlen(values[i]) > 0)
             msSLDApplySLD(map, values[i], -1, NULL);
		     else if (strcasecmp(names[i], "RULE") == 0)
				 {
             psRule = values[i];
				 }
		     else if (strcasecmp(names[i], "SCALE") == 0)
				 {
             psScale = values[i];
				 }

#endif
     }

     if (!pszLayer)
     {
         msSetError(MS_WMSERR, "Mandatory LAYER parameter missing in GetLegendGraphic request.", "msWMSGetLegendGraphic()");
         return msWMSException(map, nVersion, "LayerNotDefined");
     }
     if (!pszFormat)
     {
         msSetError(MS_WMSERR, "Mandatory FORMAT parameter missing in GetLegendGraphic request.", "msWMSGetLegendGraphic()");
         return msWMSException(map, nVersion, "InvalidFormat");
     }

     //check if layer name is valid. We only test the layer name and not
     //the group name.
     for (i=0; i<map->numlayers; i++)
     {
         if (map->layers[i].name &&
             strcasecmp(map->layers[i].name, pszLayer) == 0)
         {
             iLayerIndex = i;
             break;
         }
     }

     if (iLayerIndex == -1)
     {
         msSetError(MS_WMSERR, "Invalid layer given in the LAYER parameter.",
                 "msWMSGetLegendGraphic()");
         return msWMSException(map, nVersion, "LayerNotDefined");
     }

     //validate format
     psFormat = msSelectOutputFormat( map, pszFormat);
     if( psFormat == NULL || 
         psFormat->renderer != MS_RENDER_WITH_GD)
     {
         msSetError(MS_IMGERR,
                    "Unsupported output format (%s).",
                    "msWMSGetLegendGraphic()",
                    pszFormat);
         return msWMSException(map, nVersion, "InvalidFormat");
     }
     msApplyOutputFormat(&(map->outputformat), psFormat, 0,
                          MS_NOOVERRIDE, MS_NOOVERRIDE );

     if ( psRule == NULL )
     {
         // turn off all other layers
         for (i=0; i<map->numlayers; i++)
         {
             if (map->layers[i].name &&
                 strcasecmp(map->layers[i].name, pszLayer) != 0)
             {
                 map->layers[i].status = MS_OFF;
             }
         }

         // if SCALE was provided in request, calculate an extent and use a default width and height
         if ( psScale != NULL )
         {
             double center_y, scale, cellsize;

             scale = atof(psScale);
             map->width = 600;
             map->height = 600;
             center_y = 0.0;

             cellsize = (scale/map->resolution)/msInchesPerUnit(map->units, center_y);

             map->extent.minx = 0.0 - cellsize*map->width/2.0;
             map->extent.miny = 0.0 - cellsize*map->height/2.0;
             map->extent.maxx = 0.0 + cellsize*map->width/2.0;
             map->extent.maxy = 0.0 + cellsize*map->height/2.0;

             img = msDrawLegend(map, MS_FALSE);
         }
         else
         {
             // Scale-independent legend
             img = msDrawLegend(map, MS_TRUE);
         }
     }
     else
     {
         // RULE was specified. Get the class corresponding to the RULE
         //(RULE = class->name)
         
         for (i=0; i<map->layers[iLayerIndex].numclasses; i++)
         {
             if (map->layers[iLayerIndex].class[i].name && 
                 strlen(map->layers[iLayerIndex].class[i].name) > 0 &&
                 strcasecmp(map->layers[iLayerIndex].class[i].name,psRule) == 0)
               break;
             
         }
         if (i < map->layers[iLayerIndex].numclasses)
         {
         //set the map legend parameters
             if (nWidth < 0)
             {
                 if (map->legend.keysizex > 0)
                   nWidth = map->legend.keysizex;
                 else
                   nWidth = 20; //default values : this in not defined in the specs
             }
             if (nHeight < 0)
             {
                 if (map->legend.keysizey > 0)
                   nHeight = map->legend.keysizey;
                 else
                   nHeight = 20;
             }
             
             img = msCreateLegendIcon(map, &map->layers[iLayerIndex], 
                                      &map->layers[iLayerIndex].class[i],
                                      nWidth, nHeight);
         }
         if (img == NULL)
         {
             msSetError(MS_IMGERR,
                        "Unavailable RULE (%s).",
                        "msWMSGetLegendGraphic()",
                        psRule);
              return msWMSException(map, nVersion, "InvalidRule");
         }
     }

     if (img == NULL)
      return msWMSException(map, nVersion, NULL);

     msIO_printf("Content-type: %s%c%c", MS_IMAGE_MIME_TYPE(map->outputformat), 10,10);
     if (msSaveImage(map, img, NULL) != MS_SUCCESS)
       return msWMSException(map, nVersion, NULL);

     msFreeImage(img);

     return(MS_SUCCESS);
}


/*
** msWMSGetStyles() : return an SLD document for all layers that
** have a status set to on or default.
*/
int msWMSGetStyles(mapObj *map, int nVersion, char **names,
                       char **values, int numentries)

{
    int i,j,k;
    int validlayer = 0;
    int numlayers = 0;
    char **layers = NULL;
    char  *sld = NULL;

    for(i=0; map && i<numentries; i++)
    {
        // getMap parameters
        if (strcasecmp(names[i], "LAYERS") == 0)
        {
            layers = split(values[i], ',', &numlayers);
            if (layers==NULL || numlayers < 1) {
                msSetError(MS_WMSERR, "At least one layer name required in LAYERS.",
                   "msWMSGetStyles()");
                return msWMSException(map, nVersion, NULL);
            }
            for(j=0; j<map->numlayers; j++)
               map->layers[j].status = MS_OFF;

            for (k=0; k<numlayers; k++)
            {
                for (j=0; j<map->numlayers; j++)
                {
                    if (map->layers[j].name &&
                        strcasecmp(map->layers[j].name, layers[k]) == 0)
                    {
                        map->layers[j].status = MS_ON;
                        validlayer =1;
                    }
                }
            }

            msFreeCharArray(layers, numlayers);
        }

    }

    //validate all layers given. If an invalid layer is sent, return an exception.
    if (validlayer == 0)
    {
        msSetError(MS_WMSERR, "Invalid layer(s) given in the LAYERS parameter.",
                   "msWMSGetStyles()");
        return msWMSException(map, nVersion, "LayerNotDefined");
    }

    msIO_printf("Content-type: application/vnd.ogc.sld+xml%c%c",10,10);
    sld = msSLDGenerateSLD(map, -1);
    if (sld)
    {
        msIO_printf("%s\n", sld);
        free(sld);
    }

    return(MS_SUCCESS);
}


#endif /* USE_WMS_SVR */


/*
** msWMSDispatch() is the entry point for WMS requests.
** - If this is a valid request then it is processed and MS_SUCCESS is returned
**   on success, or MS_FAILURE on failure.
** - If this does not appear to be a valid WMS request then MS_DONE
**   is returned and MapServer is expected to process this as a regular
**   MapServer request.
*/
int msWMSDispatch(mapObj *map, cgiRequestObj *req)
{
#ifdef USE_WMS_SVR
  int i, status, nVersion=-1;
  static char *request=NULL, *service=NULL, *format=NULL;

  /*
  ** Process Params common to all requests
  */
  // VERSION (WMTVER in 1.0.0) and REQUEST must be present in a valid request
  for(i=0; i<req->NumParams; i++) {
      if(strcasecmp(req->ParamNames[i], "VERSION") == 0)
      {
        nVersion = msOWSParseVersionString(req->ParamValues[i]);
        if (nVersion == -1)
            return msWMSException(map, OWS_1_1_1, NULL); // Invalid format
      }
      else if (strcasecmp(req->ParamNames[i], "WMTVER") == 0 && nVersion == -1)
      {
        nVersion = msOWSParseVersionString(req->ParamValues[i]);
        if (nVersion == -1)
            return msWMSException(map, OWS_1_1_1, NULL); // Invalid format
      }
      else if (strcasecmp(req->ParamNames[i], "REQUEST") == 0)
        request = req->ParamValues[i];
      else if (strcasecmp(req->ParamNames[i], "EXCEPTIONS") == 0)
        wms_exception_format = req->ParamValues[i];
      else if (strcasecmp(req->ParamNames[i], "SERVICE") == 0)
        service = req->ParamValues[i];
      else if (strcasecmp(req->ParamNames[i], "FORMAT") == 0)
        format = req->ParamValues[i];
  }

  /* If SERVICE is specified then it MUST be "WMS" */
  if (service != NULL && strcasecmp(service, "WMS") != 0)
      return MS_DONE;  /* Not a WMS request */

  /*
  ** Dispatch request... we should probably do some validation on VERSION here
  ** vs the versions we actually support.
  */
  if (request && (strcasecmp(request, "capabilities") == 0 ||
                  strcasecmp(request, "GetCapabilities") == 0) )
  {
      if (nVersion == -1)
          nVersion = OWS_1_1_1;// VERSION is optional with getCapabilities only
      if ((status = msOWSMakeAllLayersUnique(map)) != MS_SUCCESS)
          return msWMSException(map, nVersion, NULL);
      return msWMSGetCapabilities(map, nVersion, req);
  }
  else if (request && (strcasecmp(request, "context") == 0 ||
                       strcasecmp(request, "GetContext") == 0) )
  {
      /* Return a context document with all layers in this mapfile
       * This is not a standard WMS request.
       * __TODO__ The real implementation should actually return only context
       * info for selected layers in the LAYERS parameter.
       */
      const char *getcontext_enabled;
      getcontext_enabled = msOWSLookupMetadata(&(map->web.metadata),
                                               "MO", "getcontext_enabled");

      if (nVersion != -1)
      {
          // VERSION, if specified, is Map Context version, not WMS version
          // Pass it via wms_context_version metadata
          char szVersion[OWS_VERSION_MAXLEN];
          msInsertHashTable(&(map->web.metadata), "wms_context_version",
                            msOWSGetVersionString(nVersion, szVersion));
      }
      // Now set version to 1.1.1 for error handling purposes
      nVersion = OWS_1_1_1;

      if (getcontext_enabled==NULL || atoi(getcontext_enabled) == 0)
      {
        msSetError(MS_WMSERR, "GetContext not enabled on this server.",
                   "msWMSDispatch()");
        return msWMSException(map, nVersion, NULL);
      }

      if ((status = msOWSMakeAllLayersUnique(map)) != MS_SUCCESS)
          return msWMSException(map, nVersion, NULL);
      msIO_printf("Content-type: text/xml\n\n");
      if ( msWriteMapContext(map, stdout) != MS_SUCCESS )
          return msWMSException(map, nVersion, NULL);
      // Request completed
      return MS_SUCCESS;
  }
  else if (request && strcasecmp(request, "GetMap") == 0 &&
           format && strcasecmp(format,  "image/txt") == 0)
  {
      // Until someone adds full support for ASCII graphics this should do. ;)
      msIO_printf("Content-type: text/plain\n\n");
      msIO_printf(".\n               ,,ggddY\"\"\"Ybbgg,,\n          ,agd888b,_ "
             "\"Y8, ___'\"\"Ybga,\n       ,gdP\"\"88888888baa,.\"\"8b    \""
             "888g,\n     ,dP\"     ]888888888P'  \"Y     '888Yb,\n   ,dP\""
             "      ,88888888P\"  db,       \"8P\"\"Yb,\n  ,8\"       ,8888"
             "88888b, d8888a           \"8,\n ,8'        d88888888888,88P\""
             "' a,          '8,\n,8'         88888888888888PP\"  \"\"      "
             "     '8,\nd'          I88888888888P\"                   'b\n8"
             "           '8\"88P\"\"Y8P'                      8\n8         "
             "   Y 8[  _ \"                        8\n8              \"Y8d8"
             "b  \"Y a                   8\n8                 '\"\"8d,   __"
             "                 8\nY,                    '\"8bd888b,        "
             "     ,P\n'8,                     ,d8888888baaa       ,8'\n '8"
             ",                    888888888888'      ,8'\n  '8a           "
             "        \"8888888888I      a8'\n   'Yba                  'Y88"
             "88888P'    adP'\n     \"Yba                 '888888P'   adY\""
             "\n       '\"Yba,             d8888P\" ,adP\"' \n          '\""
             "Y8baa,      ,d888P,ad8P\"' \n               ''\"\"YYba8888P\""
             "\"''\n");
      return MS_SUCCESS;
  }

  /* If SERVICE, VERSION and REQUEST not included than this isn't a WMS req*/
  if (service == NULL && nVersion == -1 && request==NULL)
      return MS_DONE;  /* Not a WMS request */

  // VERSION *and* REQUEST required by both getMap and getFeatureInfo
  if (nVersion == -1)
  {
      msSetError(MS_WMSERR,
                 "Incomplete WMS request: VERSION parameter missing",
                 "msWMSDispatch()");
      return msWMSException(map, nVersion, NULL);
  }

  if (request==NULL)
  {
      msSetError(MS_WMSERR,
                 "Incomplete WMS request: REQUEST parameter missing",
                 "msWMSDispatch()");
      return msWMSException(map, nVersion, NULL);
  }

  if ((status = msOWSMakeAllLayersUnique(map)) != MS_SUCCESS)
      return msWMSException(map, nVersion, NULL);

  if (strcasecmp(request, "GetLegendGraphic") == 0)
    return msWMSGetLegendGraphic(map, nVersion, req->ParamNames, req->ParamValues, req->NumParams);

  if (strcasecmp(request, "GetStyles") == 0)
    return msWMSGetStyles(map, nVersion, req->ParamNames, req->ParamValues, req->NumParams);

  // getMap parameters are used by both getMap and getFeatureInfo
  status = msWMSLoadGetMapParams(map, nVersion, req->ParamNames, req->ParamValues, req->NumParams);
  if (status != MS_SUCCESS) return status;

  if (strcasecmp(request, "map") == 0 || strcasecmp(request, "GetMap") == 0)
    return msWMSGetMap(map, nVersion, req->ParamNames, req->ParamValues, req->NumParams);
  else if (strcasecmp(request, "feature_info") == 0 || strcasecmp(request, "GetFeatureInfo") == 0)
    return msWMSFeatureInfo(map, nVersion, req->ParamNames, req->ParamValues, req->NumParams);
  else if (strcasecmp(request, "DescribeLayer") == 0)
  {
      msIO_printf("Content-type: text/xml\n\n");
      return msWMSDescribeLayer(map, nVersion, req->ParamNames, req->ParamValues, req->NumParams);
  }

  // Hummmm... incomplete or unsupported WMS request
  msSetError(MS_WMSERR, "Incomplete or unsupported WMS request", "msWMSDispatch()");
  return msWMSException(map, nVersion, NULL);
#else
  msSetError(MS_WMSERR, "WMS server support is not available.", "msWMSDispatch()");
  return(MS_FAILURE);
#endif
}

