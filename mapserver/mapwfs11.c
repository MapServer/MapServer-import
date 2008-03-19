/**********************************************************************
 * $Id: $
 *
 * Project:  MapServer
 * Purpose:  OGC WFS 1.1.0 implementation. This file holds some WFS 1.1.0 
 *           specific functions but other parts are still implemented in mapwfs.c.
 * Author:   Y. Assefa, DM Solutions Group (assefa@dmsolutions.ca)
 *
 **********************************************************************
 * Copyright (c) 2008, Y. Assefa, DM Solutions Group Inc
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

#include "mapogcfilter.h"
#include "mapowscommon.h"
#include "mapows.h"
#include "maplibxml2.h"

MS_CVSID("$Id: $")

#if defined(USE_WFS_SVR) && defined(USE_LIBXML2)


int msWFSException11(mapObj *map, const char *locator, 
                     const char *exceptionCode, const char *version)
{
    int size = 0;
    char *errorString     = NULL;
    char *errorMessage    = NULL;
    char *schemasLocation = NULL;

    xmlDocPtr  psDoc      = NULL;   
    xmlNodePtr psRootNode = NULL;
    xmlNsPtr   psNsOws    = NULL;
    xmlChar *buffer       = NULL;

    psNsOws = xmlNewNs(NULL, BAD_CAST "http://www.opengis.net/ows/1.1", BAD_CAST "ows");

    errorString = msGetErrorString("\n");
    errorMessage = msEncodeHTMLEntities(errorString);
    schemasLocation = msEncodeHTMLEntities(msOWSGetSchemasLocation(map));

    psDoc = xmlNewDoc(BAD_CAST "1.0");

    psRootNode = msOWSCommonExceptionReport(psNsOws, OWS_1_1_0, schemasLocation, version, msOWSGetLanguage(map, "exception"), exceptionCode, locator, errorMessage);

    xmlDocSetRootElement(psDoc, psRootNode);

    psNsOws = xmlNewNs(psRootNode, BAD_CAST "http://www.opengis.net/ows/1.1", BAD_CAST "ows");

    msIO_printf("Content-type: text/xml%c%c",10,10);
    xmlDocDumpFormatMemoryEnc(psDoc, &buffer, &size, "ISO-8859-1", 1);
    
    msIO_printf("%s", buffer);

    /*free buffer and the document */
    free(errorString);
    free(errorMessage);
    free(schemasLocation);
    xmlFree(buffer);
    xmlFreeDoc(psDoc);

    /* clear error since we have already reported it */
    msResetErrorList();

    return MS_FAILURE;
}
    

/************************************************************************/
/*                             msWFSDumpLayer11                         */
/************************************************************************/
static xmlNodePtr msWFSDumpLayer11(mapObj *map, layerObj *lp, xmlNsPtr psOwsNs)
{
    rectObj ext;
   
    xmlNodePtr   psRootNode, psNode, psSubNode;
    const char *value    = NULL;

    psRootNode = xmlNewNode(NULL, BAD_CAST "FeatureType");

    psNode = xmlNewChild(psRootNode, NULL, BAD_CAST "Name", BAD_CAST lp->name);

    if (lp->name && strlen(lp->name) > 0 &&
        (msIsXMLTagValid(lp->name) == MS_FALSE || isdigit(lp->name[0])))
      xmlAddSibling(psNode,
                    xmlNewComment(BAD_CAST "WARNING: The layer name '%s' might contain spaces or "
                                  "invalid characters or may start with a number. This could lead to potential problems"));
   
    value = msOWSLookupMetadata(&(lp->metadata), "FO", "title");
    if (value)
      psNode = xmlNewChild(psRootNode, NULL, BAD_CAST "Title", BAD_CAST value);
    else
      psNode = xmlNewChild(psRootNode, NULL, BAD_CAST "Title", BAD_CAST lp->name);


    value = msOWSLookupMetadata(&(lp->metadata), "FO", "abstract");
    if (value)
      psNode = xmlNewChild(psRootNode, NULL, BAD_CAST "Abstract", BAD_CAST value);


    value = msOWSLookupMetadata(&(lp->metadata), "O", "keywordlist");

    if (value) 
    {
        char **tokens = NULL;
        int n = 0;
        int i = 0;

        psNode = xmlNewChild(psRootNode, NULL, BAD_CAST "Keywords", NULL);

        tokens = msStringSplit(value, ',', &n);
        if (tokens && n > 0) 
        {
            for (i=0; i<n; i++) 
              psSubNode = xmlNewChild(psNode, NULL, BAD_CAST "Keyword", BAD_CAST tokens[i]);
          
            msFreeCharArray(tokens, n);
        }
    }

    /*srs only supposrt DefaultSRS with the same logic as for wfs1.0
      TODO support OtherSRS*/
    value = msOWSGetEPSGProj(&(map->projection),&(map->web.metadata),"FO",MS_TRUE);
    if (!value)
      value =  msOWSGetEPSGProj(&(lp->projection), &(lp->metadata), "FO", MS_TRUE);
  
    psNode = xmlNewChild(psRootNode, NULL, BAD_CAST "DefaultSRS", BAD_CAST value);
    if (!value)
      xmlAddSibling(psNode,
                    xmlNewComment(BAD_CAST "WARNING: Mandatory mapfile parameter: (at least one of) MAP.PROJECTION, LAYER.PROJECTION or wfs/ows_srs metadata was missing in this context."));

    /*TODO: adevertize only gml3?*/
    psNode = xmlNewNode(NULL, BAD_CAST "OutputFormats");
    xmlAddChild(psRootNode, psNode);
    xmlNewChild(psNode, NULL, BAD_CAST "Format", BAD_CAST "text/xml; subtype=gml/3.1.1");
  
    /*bbox*/
    if (msOWSGetLayerExtent(map, lp, "FO", &ext) == MS_SUCCESS)
    {   
        /*convert to latlong*/
        if (lp->projection.numargs > 0)
        {
            if (!pj_is_latlong(&lp->projection.proj))
              msProjectRect(&lp->projection, NULL, &ext);
        }
        else if (map->projection.numargs > 0 && !pj_is_latlong(&map->projection.proj))
          msProjectRect(&map->projection, NULL, &ext);

        xmlAddChild(psRootNode,
                    msOWSCommonWGS84BoundingBox( psOwsNs, 2,
                                                 ext.minx, ext.miny,
                                                 ext.maxx, ext.maxy));
    }
    else
    {
        xmlNewChild(psRootNode, psOwsNs, BAD_CAST "WGS84BoundingBox", NULL);
        xmlAddSibling(psNode,
                      xmlNewComment(BAD_CAST "WARNING: Mandatory WGS84BoundingBox could not be established for this layer.  Consider setting LAYER.EXTENT or wfs_extent metadata."));

        
    }

    return psRootNode;


}

/************************************************************************/
/*                          msWFSGetCapabilities11                      */
/*                                                                      */
/*      Return the capabilities document for wfs 1.1.0                  */
/************************************************************************/
int msWFSGetCapabilities11(mapObj *map, wfsParamsObj *params, 
                         cgiRequestObj *req) 
{
    xmlDocPtr psDoc = NULL;       /* document pointer */
    xmlNodePtr psRootNode, psMainNode, psNode, psFtNode;
    xmlNodePtr psTmpNode;
    const char *updatesequence=NULL;
    xmlNsPtr psOwsNs, psXLinkNs, psNsOgc, psWfsNs;
    char *schemalocation = NULL;
    char *xsi_schemaLocation = NULL;

    char *script_url=NULL, *script_url_encoded=NULL;

    xmlChar *buffer = NULL;
    int size = 0, i;
    msIOContext *context = NULL;

    int ows_version = OWS_1_0_0;

/* -------------------------------------------------------------------- */
/*      Handle updatesequence                                           */
/* -------------------------------------------------------------------- */

    updatesequence = msOWSLookupMetadata(&(map->web.metadata), "FO", "updatesequence");

    if (params->pszUpdateSequence != NULL) {
      i = msOWSNegotiateUpdateSequence(params->pszUpdateSequence, updatesequence);
      if (i == 0) { // current
          msSetError(MS_WFSERR, "UPDATESEQUENCE parameter (%s) is equal to server (%s)", "msWFSGetCapabilities11()", params->pszUpdateSequence, updatesequence);
          return msWFSException11(map, "updatesequence", "CurrentUpdateSequence", params->pszVersion);
      }
      if (i > 0) { // invalid
          msSetError(MS_WFSERR, "UPDATESEQUENCE parameter (%s) is higher than server (%s)", "msWFSGetCapabilities11()", params->pszUpdateSequence, updatesequence);
          return msWFSException11(map, "updatesequence", "InvalidUpdateSequence", params->pszVersion);
      }
    }


/* -------------------------------------------------------------------- */
/*      Create document.                                                */
/* -------------------------------------------------------------------- */
    psDoc = xmlNewDoc(BAD_CAST "1.0");

    psRootNode = xmlNewNode(NULL, BAD_CAST "WFS_Capabilities");

    xmlDocSetRootElement(psDoc, psRootNode);

/* -------------------------------------------------------------------- */
/*      Name spaces                                                     */
/* -------------------------------------------------------------------- */
    psWfsNs = xmlNewNs(NULL, BAD_CAST "http://www.opengis.net/wfs", BAD_CAST "wfs");

    /*default name space*/      
    xmlNewProp(psRootNode, BAD_CAST "xmlns", BAD_CAST "http://www.opengis.net/wfs");
    
    xmlSetNs(psRootNode, xmlNewNs(psRootNode, BAD_CAST "http://www.opengis.net/gml", BAD_CAST "gml"));
    xmlSetNs(psRootNode, xmlNewNs(psRootNode, BAD_CAST "http://www.opengis.net/wfs", BAD_CAST "wfs"));
    
    psOwsNs = xmlNewNs(psRootNode, BAD_CAST MS_OWSCOMMON_OWS_NAMESPACE_URI, BAD_CAST MS_OWSCOMMON_OWS_NAMESPACE_PREFIX);
    psXLinkNs = xmlNewNs(psRootNode, BAD_CAST MS_OWSCOMMON_W3C_XLINK_NAMESPACE_URI, BAD_CAST MS_OWSCOMMON_W3C_XLINK_NAMESPACE_PREFIX);
    xmlNewNs(psRootNode, BAD_CAST MS_OWSCOMMON_W3C_XSI_NAMESPACE_URI, BAD_CAST MS_OWSCOMMON_W3C_XSI_NAMESPACE_PREFIX);
    xmlNewNs(psRootNode, BAD_CAST MS_OWSCOMMON_OGC_NAMESPACE_URI, BAD_CAST MS_OWSCOMMON_OGC_NAMESPACE_PREFIX );

    xmlNewProp(psRootNode, BAD_CAST "version", BAD_CAST params->pszVersion );

    updatesequence = msOWSLookupMetadata(&(map->web.metadata), "FO", "updatesequence");

    if (updatesequence)
      xmlNewProp(psRootNode, BAD_CAST "updateSequence", BAD_CAST updatesequence);

    /*schema*/
    schemalocation = msEncodeHTMLEntities( msOWSGetSchemasLocation(map) );
    xsi_schemaLocation = strdup("http://www.opengis.net/wfs");
    xsi_schemaLocation = msStringConcatenate(xsi_schemaLocation, " ");
    xsi_schemaLocation = msStringConcatenate(xsi_schemaLocation, schemalocation);
    xsi_schemaLocation = msStringConcatenate(xsi_schemaLocation, "/wfs/1.1.0/");
    xsi_schemaLocation = msStringConcatenate(xsi_schemaLocation, "wfs.xsd");
    xmlNewNsProp(psRootNode, NULL, BAD_CAST "xsi:schemaLocation", BAD_CAST xsi_schemaLocation);

/* -------------------------------------------------------------------- */
/*      Service metadata.                                               */
/* -------------------------------------------------------------------- */

    psTmpNode = xmlAddChild(psRootNode, 
                            msOWSCommonServiceIdentification(psOwsNs, map, "OGC WFS", params->pszVersion));

    /*service provider*/
    psTmpNode = xmlAddChild(psRootNode, msOWSCommonServiceProvider(
                                psOwsNs, psXLinkNs, map));

    /*operation metadata */
    if ((script_url=msOWSGetOnlineResource(map, "FO", "onlineresource", req)) == NULL 
        || (script_url_encoded = msEncodeHTMLEntities(script_url)) == NULL)
    {
        msSetError(MS_WFSERR, "Server URL not found", "msWFSGetCapabilities11()");
        return msWFSException11(map, "mapserv", "NoApplicableCode", params->pszVersion);
    }
    free( script_url );

/* -------------------------------------------------------------------- */
/*      Operations metadata.                                            */
/* -------------------------------------------------------------------- */
    psMainNode= xmlAddChild(psRootNode,msOWSCommonOperationsMetadata(psOwsNs));

/* -------------------------------------------------------------------- */
/*      GetCapabilities                                                 */
/* -------------------------------------------------------------------- */
    psNode = xmlAddChild(psMainNode, 
                         msOWSCommonOperationsMetadataOperation(psOwsNs,psXLinkNs,"GetCapabilities", 
                                                                OWS_METHOD_GETPOST, script_url_encoded));
    
    xmlAddChild(psMainNode, psNode);
    xmlAddChild(psNode, msOWSCommonOperationsMetadataDomainType(
                    ows_version, psOwsNs, "Parameter", "service", "WFS"));
    /*accept version*/
    xmlAddChild(psNode, msOWSCommonOperationsMetadataDomainType(ows_version, psOwsNs, 
                                                                "Parameter", "AcceptVersions", 
                                                                "1.0.0, 1.1.0"));
    /*format*/
    xmlAddChild(psNode, msOWSCommonOperationsMetadataDomainType(ows_version, psOwsNs, 
                                                                "Parameter", "AcceptFormats", 
                                                                "text/xml"));


/* -------------------------------------------------------------------- */
/*      DescribeFeatureType                                             */
/* -------------------------------------------------------------------- */
     psNode = xmlAddChild(psMainNode, 
                          msOWSCommonOperationsMetadataOperation(psOwsNs,psXLinkNs,"DescribeFeatureType", 
                                                                 OWS_METHOD_GETPOST, script_url_encoded));
     xmlAddChild(psMainNode, psNode);

     /*output format*/
      xmlAddChild(psNode, msOWSCommonOperationsMetadataDomainType(ows_version, psOwsNs, 
                                                                  "Parameter", "outputFormat", 
                                                                  "text/gml; subtype=gml/3.1.1"));

/* -------------------------------------------------------------------- */
/*      GetFeatureType                                                  */
/* -------------------------------------------------------------------- */
      psNode = xmlAddChild(psMainNode, 
                          msOWSCommonOperationsMetadataOperation(psOwsNs,psXLinkNs,"GetFeature", 
                                                                 OWS_METHOD_GETPOST, script_url_encoded));
     xmlAddChild(psMainNode, psNode);

     /*resultType: TODO support hits*/
     xmlAddChild(psNode, msOWSCommonOperationsMetadataDomainType(ows_version, psOwsNs, 
                                                                "Parameter", "resultType", 
                                                                "results"));
     /*
     xmlAddChild(psNode, msOWSCommonOperationsMetadataDomainType(ows_version, psOwsNs, 
                                                                 "Parameter", "resultType", 
                                                                 "results, hits"));
     */
     xmlAddChild(psNode, msOWSCommonOperationsMetadataDomainType(ows_version, psOwsNs, 
                                                                  "Parameter", "outputFormat", 
                                                                  "text/gml; subtype=gml/3.1.1"));

/* -------------------------------------------------------------------- */
/*      FeatureTypeList                                                 */
/* -------------------------------------------------------------------- */
     
     psFtNode = xmlNewNode(NULL, BAD_CAST "FeatureTypeList");
     xmlAddChild(psRootNode, psFtNode);
     psNode = xmlNewChild(psFtNode, NULL, BAD_CAST "Operations", NULL);
     xmlNewChild(psNode, NULL, BAD_CAST "Operation", BAD_CAST "Query");
     
     for(i=0; i<map->numlayers; i++)
     {
         layerObj *lp;
         lp = GET_LAYER(map, i);

         /* List only vector layers in which DUMP=TRUE */
         if (msWFSIsLayerSupported(lp))
           xmlAddChild(psFtNode, msWFSDumpLayer11(map, lp, psOwsNs));
     }
     
     
     
     
     
/* -------------------------------------------------------------------- */
/*      Filter capabilities.                                            */
/* -------------------------------------------------------------------- */

     psNsOgc = xmlNewNs(NULL, BAD_CAST MS_OWSCOMMON_OGC_NAMESPACE_URI, BAD_CAST MS_OWSCOMMON_OGC_NAMESPACE_PREFIX);
     xmlAddChild(psRootNode, FLTGetCapabilities(psNsOgc, psNsOgc, MS_FALSE));
/* -------------------------------------------------------------------- */
/*      Write out the document.                                         */
/* -------------------------------------------------------------------- */

    if( msIO_needBinaryStdout() == MS_FAILURE )
        return MS_FAILURE;
     
    msIO_printf("Content-type: text/xml%c%c",10,10);
    
    context = msIO_getHandler(stdout);

    xmlDocDumpFormatMemoryEnc(psDoc, &buffer, &size, "ISO-8859-1", 1);
    msIO_contextWrite(context, buffer, size);
    xmlFree(buffer);

    /*free buffer and the document */
    /*xmlFree(buffer);*/
    xmlFreeDoc(psDoc);

    free(script_url);
     free(script_url_encoded);
    free(xsi_schemaLocation);
    free(schemalocation);

    xmlCleanupParser();

    /* clean up */
    msWFSFreeParamsObj(params);
    free(params);

    return(MS_SUCCESS);
}
    

#endif /*defined(USE_WFS_SVR) && defined(USE_LIBXML2)*/

#if defined(USE_WFS_SVR) && !defined(USE_LIBXML2)



int msWFSGetCapabilities11(mapObj *map, wfsParamsObj *params, 
                           cgiRequestObj *req)

{
    msSetError( MS_WFSERR,
                "WFS 1.1 request made, but mapserver requires libxml2 for WFS 1.1 services and this is not configured.",
                "msWFSGetCapabilities11()", "NoApplicableCode" );

    return msWFSException11(map, "mapserv", "NoApplicableCode", params->pszVersion);
}

int msWFSException11(mapObj *map, const char *locator, const char *exceptionCode, const char *version) {
    /* fallback to reporting using 1.0 style exceptions. */
    return msWFSException( map, locator, exceptionCode, "1.0.0" );
}

#endif /* defined(USE_WFS_SVR) && !defined(USE_LIBXML2) */
