/**********************************************************************
 * $Id$
 *
 * Project:  MapServer
 * Purpose:  Implementation of WFS CONNECTIONTYPE - client to WFS servers
 * Author:   Daniel Morissette, DM Solutions Group (morissette@dmsolutions.ca)
 *
 **********************************************************************
 * Copyright (c) 2002, Daniel Morissette, DM Solutions Group Inc
 *
 * Permission is hereby granted, free of charge, to any person obtaining a
 * copy of this software and associated documentation files (the "Software"),
 * to deal in the Software without restriction, including without limitation
 * the rights to use, copy, modify, merge, publish, distribute, sublicense,
 * and/or sell copies of the Software, and to permit persons to whom the
 * Software is furnished to do so, subject to the following conditions:
 * 
 * The above copyright notice and this permission notice shall be included
 * in all copies or substantial portions of the Software.
 * 
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.  IN NO EVENT SHALL
 * THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER 
 * DEALINGS IN THE SOFTWARE.
 **********************************************************************
 * $Log$
 * Revision 1.19  2004/03/11 22:45:39  dan
 * Added pszPostContentType in httpRequestObj instead of using hardcoded
 * text/html mime type for all post requests.
 *
 * Revision 1.18  2003/10/30 22:37:01  assefa
 * Add function msWFSExecuteGetFeature on a wfs layer.
 *
 * Revision 1.17  2003/10/22 20:20:09  assefa
 * Test if wfs_filter metada is empty.
 *
 * Revision 1.16  2003/09/19 21:54:19  assefa
 * Add support fot the Post request.
 *
 * Revision 1.15  2003/09/10 19:53:19  assefa
 * Use local hash function instead of md5.
 *
 * Revision 1.14  2003/09/10 03:52:53  assefa
 * The <Filter ...> and </Filter> is now generated here intstead of
 * comming from the wfs_filter metadata parameter.
 *
 * Revision 1.13  2003/09/04 17:47:15  assefa
 * Add filterencoding tests.
 *
 * Revision 1.12  2003/03/26 20:24:38  dan
 * Do not call msDebug() unless debug flag is turned on
 *
 * Revision 1.11  2003/02/19 14:19:02  frank
 * cleanup warnings
 *
 * Revision 1.10  2002/12/19 07:35:53  dan
 * Call msWFSLayerWhichShapes() inside open() to force downloading layer and
 * enable msOGRLayerGetItems() to work for queries.  i.e.WFS queries work now.
 *
 * Revision 1.9  2002/12/19 06:30:59  dan
 * Enable caching WMS/WFS request using tmp filename built from URL
 *
 * Revision 1.8  2002/12/19 05:17:09  dan
 * Report WFS exceptions, and do not fail on WFS requests returning 0 features
 *
 * Revision 1.7  2002/12/17 21:33:54  dan
 * Enable following redirections with libcurl (requires libcurl 7.10.1+)
 *
 * Revision 1.6  2002/12/17 05:30:17  dan
 * Fixed HTTP timeout value (in secs, not msecs) for WMS/WFS requests
 *
 * Revision 1.5  2002/12/17 04:48:25  dan
 * Accept version 0.0.14 in addition to 1.0.0
 *
 * Revision 1.4  2002/12/16 20:35:00  dan
 * Flush libwww and use libcurl instead for HTTP requests in WMS/WFS client
 *
 * Revision 1.3  2002/12/13 01:32:53  dan
 * OOOpps.. lp->wfslayerinfo was not set in msWFSLayerOpen()
 *
 * Revision 1.2  2002/12/13 00:57:31  dan
 * Modified WFS implementation to behave more as a real vector data source
 *
 * Revision 1.1  2002/10/09 02:29:03  dan
 * Initial implementation of WFS client support.
 *
 **********************************************************************/

#include "map.h"
#include "maperror.h"
#include "mapows.h"

#include <time.h>

#if defined(_WIN32) && !defined(__CYGWIN__)
#include <process.h>
#endif

#define WFS_V_0_0_14  14
#define WFS_V_1_0_0  100


/************************************************************************/
/*                           msBuildRequestParms                        */
/*                                                                      */
/*      Build the params object based on the metadata                   */
/*      information. This object will be used when building the Get     */
/*      and Post requsests.                                             */
/*      Note : Verify the connection string to extract some values      */
/*      for backward compatiblity. (It is though depricated).           */
/*      This will also set layer projection and compute BBOX in that    */
/*      projection.                                                     */
/*                                                                      */
/************************************************************************/
wfsParamsObj *msBuildRequestParams(mapObj *map, layerObj *lp, 
                                   rectObj *bbox_ret)
{
    wfsParamsObj *psParams = NULL;
    rectObj bbox;
    const char *pszTmp; 
    int nLength, i = 0;
    char *pszVersion, *pszService, *pszTypeName = NULL;

    if (!map || !lp || !bbox_ret)
      return NULL;

    if (lp->connection == NULL)
      return NULL;
    
    psParams = msWFSCreateParamsObj();
    pszTmp = msLookupHashTable(lp->metadata, "wfs_version");
    if (pszTmp)
      psParams->pszVersion = strdup(pszTmp);
    else
    {
        pszTmp = strstr(lp->connection, "VERSION=");
        if (!pszTmp)
           pszTmp = strstr(lp->connection, "version=");
        if (pszTmp)
        {
            pszVersion = strchr(pszTmp, '=')+1;
            if (strncmp(pszVersion, "0.0.14", 6) == 0)
              psParams->pszVersion = strdup("0.0.14");
            else if (strncmp(pszVersion, "1.0.0", 5) == 0)
              psParams->pszVersion = strdup("1.0.0");
        }
    }


    pszTmp = msLookupHashTable(lp->metadata, "wfs_service");
    if (pszTmp)
      psParams->pszService = strdup(pszTmp);
    else
    {
        pszTmp = strstr(lp->connection, "SERVICE=");
        if (!pszTmp)
          pszTmp = strstr(lp->connection, "service=");
        if (pszTmp)
        {
            pszService = strchr(pszTmp, '=')+1;
            if (strncmp(pszService, "WFS", 3) == 0)
              psParams->pszService = strdup("WFS");
        }
    }


    pszTmp = msLookupHashTable(lp->metadata, "wfs_typename");
    if (pszTmp)
      psParams->pszTypeName = strdup(pszTmp);
    else
    {
        pszTmp = strstr(lp->connection, "TYPENAME=");
        if (!pszTmp)
          pszTmp = strstr(lp->connection, "typename=");
        if (pszTmp)
        {
            pszTypeName = strchr(pszTmp, '=')+1;
            if (pszTypeName)
            {
                nLength = strlen(pszTypeName);
                if (nLength > 0)
                {
                    for (i=0; i<nLength; i++)
                    {
                        if (pszTypeName[i] == '&')
                          break;
                    }

                    if (i<nLength)
                    {
                        char *pszTypeNameTmp = NULL;
                        pszTypeNameTmp = strdup(pszTypeName);
                        pszTypeNameTmp[i] = '\0';
                        psParams->pszTypeName = strdup(pszTypeNameTmp);
                        free(pszTypeNameTmp);
                    }
                    else
                      psParams->pszTypeName = strdup(pszTypeName);
                }
            }
        }
    }

    pszTmp = msLookupHashTable(lp->metadata, "wfs_filter");
    if (pszTmp && strlen(pszTmp) > 0)
    {
        psParams->pszFilter = malloc(sizeof(char)*(strlen(pszTmp)+17+1));
        sprintf(psParams->pszFilter, "<Filter>%s</Filter>", pszTmp);
        //<Filter xmlns=\"http://www.opengis.net/ogc\" xmlns:gml=\"http://www.opengis.net/gml\" xmlns:xsi=\"http://www.w3.org/2001/XMLSchema-instance\" xsi:schemaLocation=\"http://www.opengis.net/ogc ../filter/1.0.0/filter.xsd http://www.opengis.net/gml../gml/2.1/geometry.xsd\">
    }

     pszTmp = msLookupHashTable(lp->metadata, "wfs_maxfeatures");
     if (pszTmp)
       psParams->nMaxFeatures = atoi(pszTmp);

    //Request is always GetFeature;
    psParams->pszRequest = strdup("GetFeature");

               
/* ------------------------------------------------------------------
 * Figure the SRS we'll use for the request.
 * - Fetch the map SRS (if it's EPSG)
 * - Check if map SRS is listed in layer wfs_srs metadata
 * - If map SRS is valid for this layer then use it
 * - Otherwise request layer in its default SRS and we'll reproject later
 * ------------------------------------------------------------------ */

// __TODO__ WFS servers support only one SRS... need to decide how we'll
// handle this and document it well.
// It's likely that we'll simply reproject the BBOX to teh layer's projection.

/* ------------------------------------------------------------------
 * Set layer SRS and reproject map extents to the layer's SRS
 * ------------------------------------------------------------------ */
#ifdef __TODO__
    // No need to set lp->proj if it's already set to the right EPSG code
    if ((pszTmp = msGetEPSGProj(&(lp->projection), NULL, MS_TRUE)) == NULL ||
        strcasecmp(pszEPSG, pszTmp) != 0)
    {
        char szProj[20];
        sprintf(szProj, "init=epsg:%s", pszEPSG+5);
        if (msLoadProjectionString(&(lp->projection), szProj) != 0)
            return NULL;
    }
#endif

    bbox = map->extent;
    if (msProjectionsDiffer(&(map->projection), &(lp->projection)))
    {
        msProjectRect(&(map->projection), &(lp->projection), &bbox);
    }

    if (bbox_ret != NULL)
      *bbox_ret = bbox;

    return psParams;
}

/**********************************************************************
 *                          msBuildWFSLayerPostRequest()
 *
 * Build a WFS GetFeature xml document for a Post Request.  
 *
 * Returns a reference to a newly allocated string that should be freed 
 * by the caller.
 **********************************************************************/
char *msBuildWFSLayerPostRequest(mapObj *map, layerObj *lp, 
                                 rectObj *bbox, wfsParamsObj *psParams) 
{
    char *pszPostReq = NULL;
    char *pszFilter = NULL;

#ifdef USE_WFS_LYR

    if (psParams->pszVersion == NULL || 
        (strncmp(psParams->pszVersion, "0.0.14", 6) != 0 &&
        strncmp(psParams->pszVersion, "1.0.0", 5)) != 0)
    {
        msSetError(MS_WFSCONNERR, "MapServer supports only WFS 1.0.0 or 0.0.14 (please verify the version metadata wfs_version).", "msBuildWFSLayerPostRequest()");
        return NULL;
    }

    if (psParams->pszService == NULL ||
        strncmp(psParams->pszService, "WFS", 3) != 0)
    {
        msSetError(MS_WFSCONNERR, "Metadata wfs_service must be set in the layare", "msBuildWFSLayerPostRequest()");
        return NULL;
    }

    if (psParams->pszTypeName == NULL)
    {
        msSetError(MS_WFSCONNERR, "Metadata wfs_typename must be set in the layare", "msBuildWFSLayerPostRequest()");
        return NULL;
    } 
    
    pszPostReq = (char *)malloc(sizeof(char)*1000);

    if (psParams->pszFilter)
      pszFilter = psParams->pszFilter;
    else
    {
        pszFilter = (char *)malloc(sizeof(char)*250);
        sprintf(pszFilter, "<Filter>\n"
"<BBOX>\n"
"<PropertyName>Geometry</PropertyName>\n"
"<Box>\n"
"<coordinates>%f,%f %f,%f</coordinates>\n"
"</Box>\n"
"</BBOX>\n"
"</Filter>",bbox->minx, bbox->miny, bbox->maxx, bbox->maxy);
    }

    if (psParams->nMaxFeatures > 0)
      sprintf(pszPostReq, "<?xml version=\"1.0\" ?>\n"
"<GetFeature\n"
"service=\"WFS\"\n"
"version=\"1.0.0\"\n"
"maxFeatures=\"%d\"\n"
"outputFormat=\"GML2\">\n"
"<Query typeName=\"%s\">\n"
"%s"
"</Query>\n"
"</GetFeature>\n", psParams->nMaxFeatures, psParams->pszTypeName, pszFilter);
    else
      sprintf(pszPostReq, "<?xml version=\"1.0\" ?>\n"
"<GetFeature\n"
"service=\"WFS\"\n"
"version=\"1.0.0\"\n"
"outputFormat=\"GML2\">\n"
"<Query typeName=\"%s\">\n"
"%s"
"</Query>\n"
"</GetFeature>\n", psParams->pszTypeName, pszFilter);
    if (psParams->pszFilter == NULL)
      free(pszFilter);


    return pszPostReq; 
#else
/* ------------------------------------------------------------------
 * WFS CONNECTION Support not included...
 * ------------------------------------------------------------------ */
  msSetError(MS_WFSCONNERR, "WFS CLIENT CONNECTION support is not available.", 
             "msBuildWFSLayerPostURL()");
  return NULL;

#endif
}

/**********************************************************************
 *                          msBuildWFSLayerGetURL()
 *
 * Build a WFS GetFeature URL for a Get Request.  
 *
 * Returns a reference to a newly allocated string that should be freed 
 * by the caller.
 **********************************************************************/
char *msBuildWFSLayerGetURL(mapObj *map, layerObj *lp, rectObj *bbox,
                            wfsParamsObj *psParams) 
{
#ifdef USE_WFS_LYR
    char *pszURL = NULL;
    const char *pszTmp; 
    char *pszVersion, *pszService, *pszTypename = NULL;
    int bVersionInConnection = 0, bServiceInConnection = 0;
    int bTypenameInConnection = 0;
    

    if (lp->connectiontype != MS_WFS || lp->connection == NULL)
    {
        msSetError(MS_WFSCONNERR, "Call supported only for CONNECTIONTYPE WFS",
                   "msBuildWFSLayerGetURL()");
        return NULL;
    }

/* -------------------------------------------------------------------- */
/*      Find out request version. Look first for the wfs_version        */
/*      metedata. If not available try to find out if the CONNECTION    */
/*      string contains the version. This last test is done for         */
/*      backward compatiblity but is depericated.                       */
/* -------------------------------------------------------------------- */
    pszVersion = psParams->pszVersion;
    if (!pszVersion)
    {
      if ((pszTmp = strstr(lp->connection, "VERSION=")) == NULL &&
          (pszTmp = strstr(lp->connection, "version=")) == NULL )
      {
        msSetError(MS_WFSCONNERR, "Metadata wfs_version must be set in the layer", "msBuildWFSLayerGetURL()");
        return NULL;
      }
      pszVersion = strchr(pszTmp, '=')+1;
      bVersionInConnection = 1;
    }
    
   
    if (strncmp(pszVersion, "0.0.14", 6) != 0 &&
        strncmp(pszVersion, "1.0.0", 5) != 0 )
    {
        msSetError(MS_WFSCONNERR, "MapServer supports only WFS 1.0.0 or 0.0.14 (please verify the version metadata wfs_version).", "msBuildWFSLayerGetURL()");
        return NULL;
    }

/* -------------------------------------------------------------------- */
/*      Find out the service. Look first for the wfs_service            */
/*      metadata. If not available try to find out if the CONNECTION    */
/*      string contains it. This last test is done for                  */
/*      backward compatiblity but is depericated.                       */
/* -------------------------------------------------------------------- */
    pszService = psParams->pszService;
    if (!pszService)
    {
      if ((pszTmp = strstr(lp->connection, "SERVICE=")) == NULL &&
          (pszTmp = strstr(lp->connection, "service=")) == NULL )
      {
        msSetError(MS_WFSCONNERR, "Metadata wfs_service must be set in the layare", "msBuildWFSLayerGetURL()");
        return NULL;
      }
      pszService = strchr(pszTmp, '=')+1;
      bServiceInConnection = 1;
    }
    
   
    if (strncmp(pszService, "WFS", 3))
    {
        msSetError(MS_WFSCONNERR, "MapServer supports only WFS as a SERVICE (pease verify the service metadata wfs_service).", "msBuildWFSLayerGetURL()");
        return NULL;
    }
    pszService = strdup("WFS");

/* -------------------------------------------------------------------- */
/*      Find out the typename. Look first for the wfs_tyename           */
/*      metadata. If not available try to find out if the CONNECTION    */
/*      string contains it. This last test is done for                  */
/*      backward compatiblity but is depericated.                       */
/* -------------------------------------------------------------------- */
    pszTypename = psParams->pszTypeName;
    if (!pszTypename)
    {
      if ((pszTmp = strstr(lp->connection, "TYPENAME=")) == NULL &&
          (pszTmp = strstr(lp->connection, "typename=")) == NULL )
      {
        msSetError(MS_WFSCONNERR, "Metadata wfs_typename must be set in the layare", "msBuildWFSLayerGetURL()");
        return NULL;
      }
      bTypenameInConnection = 1;
    }
    

/* -------------------------------------------------------------------- 
 * Build the request URL.
 * At this point we set only the following parameters for GetFeature:
 *   REQUEST
 *   BBOX
 *   VERSION
 *   SERVICE
 *   TYPENAME
 *   FILTER
 *   MAXFEATURES
 *
 * For backward compatiblity the user could also have in the connection
 * string the following parameters (but it is depricated):
 *   VERSION
 *   SERVICE
 *   TYPENAME
 * -------------------------------------------------------------------- */
    // Make sure we have a big enough buffer for the URL
    if(!(pszURL = (char *)malloc((strlen(lp->connection)+1024)*sizeof(char)))) 
    {
        msSetError(MS_MEMERR, NULL, "msBuildWFSLayerGetURL()");
        return NULL;
    }

    // __TODO__ We have to urlencode each value... especially the BBOX values
    // because if they end up in exponent format (123e+06) the + will be seen
    // as a space by the remote server.

/* -------------------------------------------------------------------- */
/*      build the URL,                                                  */
/* -------------------------------------------------------------------- */
    sprintf(pszURL, "%s", lp->connection);

    //REQUEST
    sprintf(pszURL + strlen(pszURL),  "&REQUEST=GetFeature");

    //VERSION
    if (!bVersionInConnection)
      sprintf(pszURL + strlen(pszURL),  "&VERSION=%s", pszVersion);
    
    //SERVICE
    if (!bServiceInConnection)
        sprintf(pszURL + strlen(pszURL),  "&SERVICE=%s", pszService);

    //TYPENAME
    if (!bTypenameInConnection)
      sprintf(pszURL + strlen(pszURL),  "&TYPENAME=%s", pszTypename);

/* -------------------------------------------------------------------- */
/*      If the filter parameter is given in the wfs_filter metadata,    */
/*      we use it and do not send the BBOX paramter as they are         */
/*      mutually exclusive.                                             */
/* -------------------------------------------------------------------- */
    if (psParams->pszFilter)
    {   
        sprintf(pszURL + strlen(pszURL), "&FILTER=%s",
                msEncodeUrl(psParams->pszFilter));
    }
    else
      sprintf(pszURL + strlen(pszURL), 
              "&BBOX=%f,%f,%f,%f",
              bbox->minx, bbox->miny, bbox->maxx, bbox->maxy);
    
    if (psParams->nMaxFeatures > 0)
      sprintf(pszURL + strlen(pszURL),  "&MAXFEATURES=%d", psParams->nMaxFeatures);

    return pszURL;

#else
/* ------------------------------------------------------------------
 * WFS CONNECTION Support not included...
 * ------------------------------------------------------------------ */
  msSetError(MS_WFSCONNERR, "WFS CLIENT CONNECTION support is not available.", 
             "msBuildWFSLayerGetURL()");
  return NULL;

#endif /* USE_WFS_LYR */

}


typedef struct ms_wfs_layer_info_t
{
    char        *pszGMLFilename;
    rectObj     rect;                     /* set by WhichShapes */
    char        *pszGetUrl;
    int         nStatus;           /* HTTP status */
    int         bLayerOpened;      /* False until msWFSLayerOpen() is called*/
} msWFSLayerInfo;

#ifdef USE_WFS_LYR

/**********************************************************************
 *                          msAllocWFSLayerInfo()
 *
 **********************************************************************/
static msWFSLayerInfo *msAllocWFSLayerInfo()
{
    msWFSLayerInfo *psInfo;

    psInfo = (msWFSLayerInfo*)calloc(1,sizeof(msWFSLayerInfo));
    if (psInfo)
    {
        psInfo->pszGMLFilename = NULL;
        psInfo->rect.minx = psInfo->rect.maxx = 0;
        psInfo->rect.miny = psInfo->rect.maxy = 0;
        psInfo->pszGetUrl = NULL;
        psInfo->nStatus = 0;
        psInfo->bLayerOpened = MS_FALSE;
    }
    else
    {
        msSetError(MS_MEMERR, NULL, "msAllocWFSLayerInfo()");
    }

    return psInfo;
}

/**********************************************************************
 *                          msFreeWFSLayerInfo()
 *
 **********************************************************************/
static void msFreeWFSLayerInfo(msWFSLayerInfo *psInfo)
{
    if (psInfo)
    {
        if (psInfo->pszGMLFilename)
            free(psInfo->pszGMLFilename);
        if (psInfo->pszGetUrl)
            free(psInfo->pszGetUrl);

        free(psInfo);
    }
}

#endif /* USE_WFS_LYR */

/**********************************************************************
 *                          msPrepareWFSLayerRequest()
 *
 **********************************************************************/

int msPrepareWFSLayerRequest(int nLayerId, mapObj *map, layerObj *lp,
                             httpRequestObj *pasReqInfo, int *numRequests) 
{
#ifdef USE_WFS_LYR
    char *pszURL = NULL;
    const char *pszTmp;
    rectObj bbox;
    int nTimeout;
    int nStatus = MS_SUCCESS;
    msWFSLayerInfo *psInfo = NULL;
    char *pszHashFileName = NULL;
    int bPostRequest = 0;
    wfsParamsObj *psParams = NULL;
    

    if (lp->connectiontype != MS_WFS || lp->connection == NULL)
        return MS_FAILURE;

/* ------------------------------------------------------------------
 * Build a params object that will be used by to build the request, 
  this will also set layer projection and compute BBOX in that projection.
 * ------------------------------------------------------------------ */
    psParams = msBuildRequestParams(map, lp, &bbox);
    if (!psParams)
      return MS_FAILURE;

/* -------------------------------------------------------------------- */
/*      Depending on the metadata wms_request_method, build a Get or    */
/*      a Post URL.                                                     */
/*    If it is a Get request the URL would contain all the parameters in*/
/*      the string;                                                     */
/*      If it is a Post request, the URL will only contain the          */
/*      connection string comming from the layer.                       */
/* -------------------------------------------------------------------- */
    if ((pszTmp = msLookupHashTable(lp->metadata, 
                                    "wms_request_method")) != NULL)
    {
        if (strncmp(pszTmp, "GET", 3) ==0)
        {
            pszURL = msBuildWFSLayerGetURL(map, lp, &bbox, psParams);
            if (!pszURL)
            {
              /* an error was already reported. */
                return MS_FAILURE;
            }
        }
    }
    //else it is a post request and just get the connection string
    if (!pszURL)
    {
        bPostRequest = 1;
        pszURL = strdup(lp->connection);
    }

    
/* ------------------------------------------------------------------
 * check to see if a the metadata wfs_connectiontimeout is set. If it is 
 * the case we will use it, else we use the default which is 30 seconds.
 * First check the metadata in the layer object and then in the map object.
 * ------------------------------------------------------------------ */
    nTimeout = 30;  // Default is 30 seconds 
    if ((pszTmp = msLookupHashTable(lp->metadata, 
                                    "wfs_connectiontimeout")) != NULL)
    {
        nTimeout = atoi(pszTmp);
    }
    else if ((pszTmp = msLookupHashTable(map->web.metadata, 
                                         "wfs_connectiontimeout")) != NULL)
    {
        nTimeout = atoi(pszTmp);
    }

/* ------------------------------------------------------------------
 * If nLayerId == -1 then we need to figure it
 * ------------------------------------------------------------------ */
    if (nLayerId == -1)
    {
        int iLayer;
        for(iLayer=0; iLayer < map->numlayers; iLayer++)
        {
            if (&(map->layers[iLayer]) == lp)
            {
                nLayerId = iLayer;
                break;
            }
        }
    }

/* ------------------------------------------------------------------
 * Add a request to the array (already preallocated)
 * ------------------------------------------------------------------ */
    pasReqInfo[(*numRequests)].nLayerId = nLayerId;
    pasReqInfo[(*numRequests)].pszGetUrl = pszURL;

    if (bPostRequest)
    {
        pasReqInfo[(*numRequests)].pszPostRequest = 
            msBuildWFSLayerPostRequest(map, lp, &bbox, psParams);
        pasReqInfo[(*numRequests)].pszPostContentType =
            strdup("text/xml");
    }

    // We'll store the remote server's response to a tmp file.
    if (bPostRequest)
    {
        char *pszPostTmpName = NULL;
        pszPostTmpName = (char *)malloc(sizeof(char)*(strlen(pszURL)+128));
        sprintf(pszPostTmpName,"%s%ld%d",
                pszURL, (long)time(NULL), (int)getpid());
        pszHashFileName = msHashString(pszPostTmpName);
        free(pszPostTmpName);
    }
    else
      pszHashFileName = msHashString(pszURL);
    pszURL = NULL;
    
    pasReqInfo[(*numRequests)].pszOutputFile =  
        msOWSBuildURLFilename(map->web.imagepath, 
                              pszHashFileName,".tmp.gml");
    free(pszHashFileName);
    pasReqInfo[(*numRequests)].nStatus = 0;
    pasReqInfo[(*numRequests)].nTimeout = nTimeout;
    pasReqInfo[(*numRequests)].bbox = bbox;
    pasReqInfo[(*numRequests)].debug = lp->debug;

/* ------------------------------------------------------------------
 * Pre-Open the layer now, (i.e. alloc and fill msWFSLayerInfo inside 
 * layer obj).  Layer will be ready for use when the main mapserver 
 * code calls msLayerOpen().
 * ------------------------------------------------------------------ */
    if (lp->wfslayerinfo != NULL)
    {
        psInfo =(msWFSLayerInfo*)(lp->wfslayerinfo);
    }
    else
    {
        lp->wfslayerinfo = psInfo = msAllocWFSLayerInfo();
    }

    if (psInfo->pszGMLFilename) 
        free(psInfo->pszGMLFilename);
    psInfo->pszGMLFilename=strdup(pasReqInfo[(*numRequests)].pszOutputFile);
 
    psInfo->rect = pasReqInfo[(*numRequests)].bbox;

    if (psInfo->pszGetUrl) 
        free(psInfo->pszGetUrl);
    psInfo->pszGetUrl = strdup(pasReqInfo[(*numRequests)].pszGetUrl);

    psInfo->nStatus = 0;

    (*numRequests)++;

    if (psParams)
    {
        msWFSFreeParamsObj(psParams);
        psParams = NULL;
    }
    return nStatus;

#else
/* ------------------------------------------------------------------
 * WFS CONNECTION Support not included...
 * ------------------------------------------------------------------ */
  msSetError(MS_WFSCONNERR, "WFS CLIENT CONNECTION support is not available.", 
             "msPrepareWFSLayerRequest");
  return(MS_FAILURE);

#endif /* USE_WFS_LYR */

}

/**********************************************************************
 *                          msWFSUpdateRequestInfo()
 *
 * This function is called after a WFS request has been completed so that
 * we can copy request result information from the httpRequestObj to the
 * msWFSLayerInfo struct.  Things to copy here are the HTTP status, exceptions
 * information, mime type, etc.
 **********************************************************************/
void msWFSUpdateRequestInfo(layerObj *lp, httpRequestObj *pasReqInfo)
{
    if (lp->wfslayerinfo)
    {
        msWFSLayerInfo *psInfo = NULL;

        psInfo =(msWFSLayerInfo*)(lp->wfslayerinfo);

        // Copy request results infos to msWFSLayerInfo struct
        // For now there is only nStatus, but we should eventually add
        // mime type and WFS exceptions information.
        psInfo->nStatus = pasReqInfo->nStatus;
    }
}

/**********************************************************************
 *                          msWFSLayerOpen()
 *
 * WFS layers are just a special case of OGR connection.  Only the open/close
 * methods differ since they have to download and maintain GML files in cache
 * but the rest is mapped directly to OGR function calls in maplayer.c
 *
 **********************************************************************/

int msWFSLayerOpen(layerObj *lp, 
                   const char *pszGMLFilename, rectObj *defaultBBOX) 
{
#ifdef USE_WFS_LYR
    int status = MS_SUCCESS;
    msWFSLayerInfo *psInfo = NULL;

    if (lp->wfslayerinfo != NULL)
    {
        psInfo =(msWFSLayerInfo*)lp->wfslayerinfo;

        // Layer already opened.  If explicit filename requested then check
        // that file was already opened with the same filename.
        // If no explicit filename requested then we'll try to reuse the
        // previously opened layer... this will happen in a msDrawMap() call.
        if (pszGMLFilename == NULL ||
            (psInfo->pszGMLFilename && pszGMLFilename && 
             strcmp(psInfo->pszGMLFilename, pszGMLFilename) == 0) )
        {
            return MS_SUCCESS;  // Nothing to do... layer is already opened
        }
        else
        {
            // Hmmm... should we produce a fatal error?
            // For now we'll just close the layer and reopen it.
            if (lp->debug)
                msDebug("msWFSLayerOpen(): Layer already opened (%s)\n",
                        lp->name?lp->name:"(null)" );
            msWFSLayerClose(lp);
        }
    }

/* ------------------------------------------------------------------
 * Alloc and fill msWFSLayerInfo inside layer obj
 * ------------------------------------------------------------------ */
    lp->wfslayerinfo = psInfo = msAllocWFSLayerInfo();

    if (pszGMLFilename)
        psInfo->pszGMLFilename = strdup(pszGMLFilename);
    else
        psInfo->pszGMLFilename = msTmpFile(lp->map->web.imagepath, 
                                           "tmp.gml");

    if (defaultBBOX)
    {
        // __TODO__ If new bbox differs from current one then we should
        // invalidate current GML file in cache
        psInfo->rect = *defaultBBOX;
    }
    else
    {
        // Use map bbox by default
        psInfo->rect = lp->map->extent;
    }

    // We will call whichshapes() now and force downloading layer right
    // away.  This saves from having to call DescribeFeatureType and
    // parsing the response (being lazy I guess) and anyway given the
    // way we work with layers right now the bbox is unlikely to change
    // between now and the time whichshapes() would have been called by
    // the MapServer core.
    if (msWFSLayerWhichShapes(lp, psInfo->rect) == MS_FAILURE)
        status = MS_FAILURE;
    
    psInfo->bLayerOpened = MS_TRUE;

    return status;
#else
/* ------------------------------------------------------------------
 * WFS CONNECTION Support not included...
 * ------------------------------------------------------------------ */
  msSetError(MS_WFSCONNERR, "WFS CLIENT CONNECTION support is not available.", 
             "msWFSLayerOpen()");
  return(MS_FAILURE);

#endif /* USE_WFS_LYR */
}

/**********************************************************************
 *                          msWFSLayerInitItemInfo()
 *
 **********************************************************************/

int msWFSLayerInitItemInfo(layerObj *layer)
{
    // Nothing to do here.  OGR will do its own initialization when it
    // opens the actual file.
    // Note that we didn't implement our own msWFSLayerFreeItemInfo()
    // so that the OGR one gets called.
    return MS_SUCCESS;
}

/**********************************************************************
 *                          msWFSLayerGetItems()
 *
 **********************************************************************/

int msWFSLayerGetItems(layerObj *layer)
{
    // For now this method simply lets OGR parse the GML and figure the 
    // schema itself.
    // It could also be implemented to call DescribeFeatureType for
    // this layer, but we don't need to do it so why waste resources?

    return msOGRLayerGetItems(layer);
}

/**********************************************************************
 *                          msWFSLayerWhichShapes()
 *
 **********************************************************************/

int msWFSLayerWhichShapes(layerObj *lp, rectObj rect)
{
#ifdef USE_WFS_LYR
    msWFSLayerInfo *psInfo;
    int status = MS_SUCCESS;
    const char *pszTmp;
    FILE *fp;

    psInfo =(msWFSLayerInfo*)lp->wfslayerinfo;

    if (psInfo == NULL)
    {
        msSetError(MS_WFSCONNERR, "Assertion failed: WFS layer not opened!!!", 
                   "msWFSLayerWhichShapes()");
        return(MS_FAILURE);
    }

/* ------------------------------------------------------------------
 * Check if layer overlaps current view window (using wfs_latlonboundingbox)
 * ------------------------------------------------------------------ */
    if ((pszTmp = msLookupHashTable(lp->metadata, 
                                    "wfs_latlonboundingbox")) != NULL)
    {
        char **tokens;
        int n;
        rectObj ext;

        tokens = split(pszTmp, ' ', &n);
        if (tokens==NULL || n != 4) {
            msSetError(MS_WFSCONNERR, "Wrong number of values in 'wfs_latlonboundingbox' metadata.",
                       "msWFSLayerWhichShapes()");
            return MS_FAILURE;
        }

        ext.minx = atof(tokens[0]);
        ext.miny = atof(tokens[1]);
        ext.maxx = atof(tokens[2]);
        ext.maxy = atof(tokens[3]);

        msFreeCharArray(tokens, n);

        // Reproject latlonboundingbox to the selected SRS for the layer and
        // check if it overlaps the bbox that we calculated for the request

        msProjectRect(&(lp->map->latlon), &(lp->projection), &ext);
        if (!msRectOverlap(&rect, &ext))
        {
            // No overlap... nothing to do
            return MS_DONE;  // No overlap.
        }
    }


 /* ------------------------------------------------------------------
  * __TODO__ If new bbox differs from current one then we should
  * invalidate current GML file in cache
  * ------------------------------------------------------------------ */
    psInfo->rect = rect;


/* ------------------------------------------------------------------
 * If file not downloaded yet then do it now.
 * ------------------------------------------------------------------ */
    if (psInfo->nStatus == 0)
    {
        httpRequestObj asReqInfo[2];
        int numReq = 0;

        msHTTPInitRequestObj(asReqInfo, 2);

        if ( msPrepareWFSLayerRequest(-1, lp->map, lp,
                                      asReqInfo, &numReq) == MS_FAILURE  ||
             msOWSExecuteRequests(asReqInfo, numReq, 
                                  lp->map, MS_TRUE) == MS_FAILURE )
        {
            // Delete tmp file... we don't want it to stick around.
            unlink(asReqInfo[0].pszOutputFile);
            return MS_FAILURE;
        }

        // Cleanup
        msHTTPFreeRequestObj(asReqInfo, numReq);

    }

    if ( !MS_HTTP_SUCCESS( psInfo->nStatus ) )
    {
        // Delete tmp file... we don't want it to stick around.
        unlink(psInfo->pszGMLFilename);

        msSetError(MS_WFSCONNERR, 
                   "Got HTTP status %d downloading WFS layer %s", 
                   "msWFSLayerWhichShapes()",
                   psInfo->nStatus, lp->name?lp->name:"(null)");
        return(MS_FAILURE);
    }

/* ------------------------------------------------------------------
 * Check that file is really GML... it could be an exception, or just junk.
 * ------------------------------------------------------------------ */
    if ((fp = fopen(psInfo->pszGMLFilename, "r")) != NULL)
    {
        char szHeader[2000];
        int  nBytes = 0;

        nBytes = fread( szHeader, 1, sizeof(szHeader)-1, fp );
        fclose(fp);

        if (nBytes < 0)
            nBytes = 0;
        szHeader[nBytes] = '\0';

        if ( nBytes == 0 )
        {
            msSetError(MS_WFSCONNERR, 
                       "WFS request produced no oputput for layer %s.",
                       "msWFSLayerWhichShapes()",
                       lp->name?lp->name:"(null)");
            return(MS_FAILURE);

        }
        if ( strstr(szHeader, "<WFS_Exception>") ||
             strstr(szHeader, "<ServiceExceptionReport>") )
        {
            msOWSProcessException(lp, psInfo->pszGMLFilename,
                                  MS_WFSCONNERR, "msWFSLayerWhichShapes()" );
            return MS_FAILURE;
        }
        else if ( strstr(szHeader,"opengis.net/gml") &&
                  strstr(szHeader,"featureMember>") == NULL )
        {
            // This looks like valid GML, but contains 0 features.
            return MS_DONE;
        }
        else if ( strstr(szHeader,"opengis.net/gml") == NULL ||
                  strstr(szHeader,"featureMember>") == NULL )
        {
            // This is probably just junk.
            msSetError(MS_WFSCONNERR, 
                       "WFS request produced unexpected output (junk?) for layer %s.",
                       "msWFSLayerWhichShapes()",
                       lp->name?lp->name:"(null)");
            return(MS_FAILURE);
        }
        
        // If we got this far, it must be a valid GML dataset... keep going
    }


/* ------------------------------------------------------------------
 * Open GML file using OGR.
 * ------------------------------------------------------------------ */
    if ((status = msOGRLayerOpen(lp, psInfo->pszGMLFilename)) != MS_SUCCESS)
        return status;
    
    status = msOGRLayerWhichShapes(lp, rect);

    return status;
#else
/* ------------------------------------------------------------------
 * WFS CONNECTION Support not included...
 * ------------------------------------------------------------------ */
  msSetError(MS_WFSCONNERR, "WFS CLIENT CONNECTION support is not available.", 
             "msWFSLayerWhichShapes()");
  return(MS_FAILURE);

#endif /* USE_WFS_LYR */
}



/**********************************************************************
 *                          msWFSLayerClose()
 *
 **********************************************************************/

int msWFSLayerClose(layerObj *lp)
{
#ifdef USE_WFS_LYR

/* ------------------------------------------------------------------
 * Cleanup OGR connection
 * ------------------------------------------------------------------ */
    if (lp->ogrlayerinfo)
        msOGRLayerClose(lp);

/* ------------------------------------------------------------------
 * Cleanup WFS connection info.
 * __TODO__ For now we flush everything, but we should try to cache some stuff
 * ------------------------------------------------------------------ */
    // __TODO__ unlink()  .gml file and OGR's schema file if they exist
    // unlink(

    msFreeWFSLayerInfo(lp->wfslayerinfo);
    lp->wfslayerinfo = NULL;

    return MS_SUCCESS;

#else
/* ------------------------------------------------------------------
 * WFS CONNECTION Support not included...
 * ------------------------------------------------------------------ */
  msSetError(MS_WFSCONNERR, "WFS CLIENT CONNECTION support is not available.", 
             "msWFSLayerClose()");
  return(MS_FAILURE);

#endif /* USE_WFS_LYR */

}

/**********************************************************************
 *                          msWFSExecuteGetFeature()
 * Returns the temporary gml file name. User shpuld free the return string.
 **********************************************************************/
char *msWFSExecuteGetFeature(layerObj *lp)
{
  char *gmltmpfile = NULL;
  msWFSLayerInfo *psInfo = NULL;

#ifdef USE_WFS_LYR
  if (lp == NULL || lp->connectiontype != MS_WFS)
    return NULL;

  msWFSLayerOpen(lp, NULL, NULL);
  psInfo =(msWFSLayerInfo*)lp->wfslayerinfo;
  if (psInfo &&  psInfo->pszGMLFilename)
    gmltmpfile = strdup(psInfo->pszGMLFilename);
  msWFSLayerClose(lp);

  return gmltmpfile;

#else
/* ------------------------------------------------------------------
 * WFS CONNECTION Support not included...
 * ------------------------------------------------------------------ */
  msSetError(MS_WFSCONNERR, "WFS CLIENT CONNECTION support is not available.", 
             "msExecuteWFSGetFeature()");
  return NULL;

#endif /* USE_WFS_LYR */

}

