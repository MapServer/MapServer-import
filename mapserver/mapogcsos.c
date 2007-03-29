/**********************************************************************

 *
 * Name:     mapogsos.c
 * Project:  MapServer
 * Language: C
 * Purpose:  OGC SOS implementation
 * Author:   Y. Assefa, DM Solutions Group (assefa@dmsolutions.ca)
 *
 **********************************************************************
 * Copyright (c) 2006, Y. Assefa, DM Solutions Group Inc
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
 * Revision 1.30  2007/03/29 15:55:55  tkralidi
 * - Cleaned up operation optional/required definitions in GetCapabilities
 * - Added functionality to check for mandatory VERSION param for msSOSDescribeSensor and msSOSGetObservation as per spec
 *
 * Revision 1.29  2007/03/27 23:10:24  assefa
 * sos_procedure takes priority on sos_precedure_item (bug 2050).
 *
 * Revision 1.28  2007/03/27 02:40:49  tkralidi
 * abstracted version string
 *
 * Revision 1.27  2007/03/27 02:20:04  tkralidi
 * - msSOSDescribeSensor(): Added functionality to test for required parameter outputFormat.  Also checks that the correct outputFormat is passed, and matches what is advertised in Capabilities XML.
 * - msSOSGetObservation(): Added functionality to test for required parameter responseFormat.  Also checks that the correct responseFormat is passed, and matches what is advertised in Capabilities XML.
 *
 * Revision 1.26  2007/03/27 01:40:33  tkralidi
 * - updated version to 0.1.2b
 * - updated GetCapabilities OperationsMetadata to leverage abstract functions from mapowscommon.c
 * - updated om.xsd to 0.14.7/om.xsd
 *
 * Revision 1.25  2007/03/27 00:30:33  tkralidi
 * typo in a few exception messages fixed
 *
 * Revision 1.24  2007/03/26 03:22:12  assefa
 * Support procedure_item for GetObservation (bug 2050)
 *
 * Revision 1.23  2007/03/25 13:46:48  tkralidi
 * updated resultFormat to specify o&m subtype
 *
 * Revision 1.22  2007/03/23 16:23:20  tkralidi
 * changed = to == in else if statement
 *
 * Revision 1.21  2007/03/23 15:26:29  assefa
 * Add possiblity to do variable substitution on describesensor_url (bug 2051)
 *
 * Revision 1.20  2007/03/22 20:18:09  assefa
 * Ignore procedures that are repeated (bug 2050).
 *
 * Revision 1.19  2007/03/22 15:12:38  assefa
 * Add support for procedure_item (Bug 2050)
 *
 * Revision 1.18  2007/02/13 04:39:07  frank
 * ensure that error stack is cleared after issing exceptions (bug 2025)
 *
 * Revision 1.17  2006/11/10 01:44:49  tkralidi
 * Integration of mapowscommon.c/h (bug 1954) to derive all OWS Common
 * constructs from mapowscommon functions.
 *
 * - msSOSException now is a wrapper to msOWSCommonExceptionReport
 * - GetCapabilities: ServiceIdentification now uses msOWSCommonServiceIdentification
 * - GetCapabilities: ServiceProvider now uses msOWSCommonServiceProvider
 *
 * Revision 1.16  2006/10/16 14:50:32  assefa
 * Fixed bugs realted to metadata and xml output
 * (1731, 1739, 1740, 1741).  Fixed bug with large xml output (1938)
 *
 * Revision 1.15  2006/06/05 19:45:04  assefa
 * Split buffer into small pieces before outputting it.
 *
 * Revision 1.14  2006/04/06 00:51:54  assefa
 * change url location the exception's schema.
 *
 * Revision 1.13  2006/03/30 00:57:14  assefa
 * Correct misspling.
 * Encode itme names.
 *
 * Revision 1.12  2006/03/29 01:11:07  assefa
 * Corrected misspelled keywordlist.
 *
 * Revision 1.11  2006/03/28 17:36:11  assefa
 * Correct use of the wrong variaable.
 *
 * Revision 1.10  2006/03/27 13:59:07  assefa
 * Initilaize variabale properly.
 *
 * Revision 1.9  2006/03/27 13:50:58  assefa
 * Add support for more than 1 observed property and procedure.
 *
 * Revision 1.8  2006/03/22 20:39:39  assefa
 * Suport parameters FEATUREOFINTEREST and EVENTTIME  for GetObservation.
 *
 * Revision 1.7  2006/03/22 04:13:56  assefa
 * Look for the attribute name alias when outputing members in getobservation.
 *
 * Revision 1.6  2006/03/22 03:51:12  assefa
 * cleaup unused varaibles.
 *
 * Revision 1.5  2006/03/22 03:45:55  assefa
 * Clean up exception output.
 * Add describelayer.
 * Add filter using procedure.
 *
 * Revision 1.4  2006/03/20 02:00:36  assefa
 * Add bbox support for getobservation.
 *
 * Revision 1.3  2006/03/16 01:42:39  assefa
 * Verfify layer indix before closing it.
 *
 * Revision 1.2  2006/03/15 18:07:33  assefa
 * Add time output support
 * Use USE_SOS_SVR flag instead of US_OGC_SOS.
 *
 * Revision 1.1  2006/03/14 03:46:20  assefa
 * Sensor Observation support.
 *
 *
 *
 **********************************************************************/


#include "map.h"

MS_CVSID("$Id$")

#ifdef USE_SOS_SVR

#include "maperror.h"
#include "mapthread.h"
#include "mapows.h"
#include "maptime.h"
#include "mapogcfilter.h"

#include "mapowscommon.h"

#include "libxml/parser.h"
#include "libxml/tree.h"

const char *pszSOSVersion                = "0.1.2b";
const char *pszSOSDescribeSensorMimeType = "text/xml;subtype=\"sensorML/1.0.0\"";
const char *pszSOSGetObservationMimeType = "text/xml;subtype=\"om/0.14.7\"";

/*
** msSOSException()
**
** Report current MapServer error in XML exception format.
** Wrapper function around msOWSCommonExceptionReport. Merely
** passes SOS specific info.
** 
*/

static int msSOSException(mapObj *map, char *locator, char *exceptionCode) 
{
    xmlDocPtr  psDoc      = NULL;   
    xmlNodePtr psRootNode = NULL;
    xmlChar *buffer       = NULL;
    int size = 0;

    psDoc = xmlNewDoc(BAD_CAST "1.0");

    psRootNode = msOWSCommonExceptionReport(msEncodeHTMLEntities(msOWSGetSchemasLocation(map)), pszSOSVersion, msOWSGetLanguage(map, "exception"), exceptionCode, locator, msEncodeHTMLEntities(msGetErrorString("\n")));

    xmlDocSetRootElement(psDoc, psRootNode);
    xmlSetNs(psRootNode,  xmlNewNs(psRootNode, BAD_CAST "http://www.opengis.net/ows",  BAD_CAST "ows"));

    msIO_printf("Content-type: text/xml%c%c",10,10);
    xmlDocDumpFormatMemoryEnc(psDoc, &buffer, &size, "ISO-8859-1", 1);
    
    msIO_printf("%s", buffer);

    /*free buffer and the document */
    xmlFree(buffer);
    xmlFreeDoc(psDoc);

    /* clear error since we have already reported it */
    msResetErrorList();

    return MS_FAILURE;
}

static int _IsInList(char **papsProcedures, int nDistinctProcedures, char *pszProcedure)
{
    int i = 0;
    if (papsProcedures && nDistinctProcedures > 0 && pszProcedure)
    {
        for (i=0; i<nDistinctProcedures; i++)
        {
            if (papsProcedures[i] && strcmp(papsProcedures[i], pszProcedure) == 0)
              return 1;
        }
    }

    return 0;
}

/************************************************************************/
/*                        msSOSAddMetadataChildNode                     */
/*                                                                      */
/*      Utility function to add a metadata node.                        */
/************************************************************************/
void msSOSAddMetadataChildNode(xmlNodePtr psParent, const char *psNodeName,
                              xmlNsPtr psNs, hashTableObj *metadata,
                              const char *psNamespaces, 
                              const char *psMetadataName, 
                              const char *psDefaultValue)
{
    xmlNodePtr psNode = NULL;
    char *psValue = NULL;

    if (psParent && psNodeName)
    {   
        psValue = msOWSGetEncodeMetadata(metadata, psNamespaces, psMetadataName, 
                                         psDefaultValue);
        if (psValue)
        {
            psNode = xmlNewChild(psParent, NULL, BAD_CAST psNodeName, BAD_CAST psValue);
            if (psNs)
              xmlSetNs(psNode,  psNs);
            free(psValue);
        }
    }
}


/************************************************************************/
/*                      msSOSGetFirstLayerForOffering                   */
/*                                                                      */
/*      return the first layer for the offering.                        */
/************************************************************************/
layerObj *msSOSGetFirstLayerForOffering(mapObj *map, const char *pszOffering,
                                        const char *pszProperty)
{
    layerObj *lp = NULL;
    const char *pszTmp = NULL;
    int i = 0;

    if (pszOffering && map)
    {
        for (i=0; i<map->numlayers; i++)
        {
            pszTmp = 
              msOWSLookupMetadata(&(map->layers[i].metadata), "S", "offering_id");
            if (pszTmp && (strcasecmp(pszTmp, pszOffering) == 0))
            {
                if (pszProperty)
                {
                    pszTmp = 
                      msOWSLookupMetadata(&(map->layers[i].metadata), "S", 
                                          "observedProperty_id");
                    if (pszTmp && (strcasecmp(pszTmp, pszProperty) == 0))
                    {
                        lp = &(map->layers[i]);
                        break;
                    }
                }
                else
                {
                    lp = &(map->layers[i]);
                    break;
                }
            }
        }
    }
    return lp;
}

void msSOSAddTimeNode(xmlNodePtr psParent, char *pszStart, char *pszEnd,  xmlNsPtr psNsGml)
{
    xmlNodePtr psNode, psTimeNode;

    if (psParent && pszStart)
    {
        psNode = xmlNewChild(psParent, NULL, BAD_CAST "eventTime", NULL);
        psTimeNode = xmlNewChild(psNode, psNsGml, BAD_CAST "TimePeriod", NULL);

        psNode = xmlNewChild(psTimeNode, NULL, BAD_CAST "beginPosition", BAD_CAST pszStart);
        
        
        if (pszEnd)
           psNode = xmlNewChild(psTimeNode, NULL, BAD_CAST "endPosition", BAD_CAST pszEnd);
        else
        {
            psNode = xmlNewChild(psTimeNode, NULL, BAD_CAST "endPosition", NULL);
            xmlNewProp(psNode, BAD_CAST "indeterminatePosition", BAD_CAST "now");
        }
        
        
    }
}



/************************************************************************/
/*                            Add a bbox node.                          */
/*      <gml:boundedBy>                                                 */
/*      -<gml:Envelope>                                                 */
/*      <gml:lowerCorner srsName="epsg:4326">-66 43</gml:lowerCorner>   */
/*      <upperCorner srsName="epsg:4326">-62 45</upperCorner>           */
/*      </gml:Envelope>                                                 */
/*      </gml:boundedBy>                                                */
/************************************************************************/
void msSOSAddBBNode(xmlNodePtr psParent, double minx, double miny, double maxx, 
                    double maxy, const char *psEpsg, xmlNsPtr psNsGml)
{               
    xmlNodePtr psNode, psEnvNode;
    char *pszTmp = NULL;

    if (psParent)
    {
      psNode = xmlNewChild(psParent, psNsGml,
                             BAD_CAST "boundedBy", NULL);
        
        psEnvNode = xmlNewChild(psNode, NULL, BAD_CAST "Envelope", NULL);

        pszTmp = double2string(minx);
        pszTmp = strcatalloc(pszTmp, " ");
        pszTmp = strcatalloc(pszTmp, double2string(miny));
        psNode = xmlNewChild(psEnvNode, NULL, BAD_CAST "lowerCorner", BAD_CAST pszTmp);
        if (psEpsg)
        {
            
            xmlNewProp(psNode, BAD_CAST "srsName", BAD_CAST psEpsg);
        }
        free(pszTmp);

        pszTmp = double2string(maxx);
        pszTmp = strcatalloc(pszTmp, " ");
        pszTmp = strcatalloc(pszTmp, double2string(maxy));
        psNode = xmlNewChild(psEnvNode, NULL,
                             BAD_CAST "upperCorner", BAD_CAST pszTmp);
        
        if (psEpsg)
        {
            
            xmlNewProp(psNode, BAD_CAST "srsName", BAD_CAST psEpsg);
        }
        free(pszTmp);
                             
    }
}

void msSOSAddPropertyNode(xmlNodePtr psParent, layerObj *lp,  xmlNsPtr  psNsGml)
{
    const char *pszValue = NULL, *pszFullName = NULL;
    xmlNodePtr psCompNode, psNode;
    int i;
    char szTmp[256];
    xmlNsPtr psNsSwe = xmlNewNs(NULL, BAD_CAST "http://www.opengis.net/swe", BAD_CAST "swe");

    if (psParent && lp)
    {
        psNode = xmlNewChild(psParent, NULL, BAD_CAST "observedProperty", NULL);
        psCompNode = xmlNewChild(psNode, NULL, BAD_CAST "CompositePhenomenon", NULL);
        pszValue = msOWSLookupMetadata(&(lp->metadata), "S", 
                                       "observedProperty_id");
        if (pszValue)/*should always be true */
          xmlNewNsProp(psNode, psNsGml,
                       BAD_CAST "id", BAD_CAST pszValue);

          pszValue = msOWSLookupMetadata(&(lp->metadata), "S", 
                                         "observedProperty_name");
          if (pszValue)
            psNode = xmlNewChild(psCompNode, psNsGml, 
                                 BAD_CAST "name", BAD_CAST pszValue);

          /* add componenets */
          /*  Componenets are exposed 
              using the metadata sos_%s_componenturl "url value" where 
              the %s is the name of the  attribute. */
        
          if (msLayerOpen(lp) == MS_SUCCESS && msLayerGetItems(lp) == MS_SUCCESS)
          {
              for(i=0; i<lp->numitems; i++) 
              {
                  sprintf(szTmp, "%s_componenturl", lp->items[i]);
                  pszValue = msOWSLookupMetadata(&(lp->metadata), "S", szTmp);
                  if (pszValue)
                  {
                      psNode = xmlNewChild(psCompNode, psNsSwe,
                                           BAD_CAST "component", NULL);

                      //check if there is an alias/full name used
                      sprintf(szTmp, "%s_alias", lp->items[i]);
                      pszFullName = msOWSLookupMetadata(&(lp->metadata), "S", szTmp);
                      if (pszFullName)
                        xmlNewNsProp(psNode, NULL, BAD_CAST "name", BAD_CAST pszFullName);
                      else
                        xmlNewNsProp(psNode, NULL, BAD_CAST "name", BAD_CAST lp->items[i]);

                      xmlNewNsProp(psNode, 
                                   xmlNewNs(NULL, BAD_CAST "http://www.w3.org/1999/xlink", 
                                            BAD_CAST "xlink"),
                                   BAD_CAST "href", BAD_CAST pszValue);
                  }
              }
              msLayerClose(lp);
          }
    }	
}
        
/************************************************************************/
/*                           msSOSAddGeometryNode                       */
/*                                                                      */
/*      Outout gml 2 gemptry nodes based on a shape. All logic comes    */
/*      from gmlWriteGeometry_GML2. Should be merged at one point if    */
/*      possible.                                                       */
/************************************************************************/
void  msSOSAddGeometryNode(xmlNodePtr psParent, layerObj *lp, shapeObj *psShape, 
                           const char *pszEpsg)
{
    char *pszTmp = NULL;
    int i,j = 0;
    xmlNodePtr psPointNode, psNode, psLineNode, psPolygonNode;
    int *panOuterList = NULL, *panInnerList = NULL;

    if (psParent && psShape)
    {
        switch(psShape->type) 
        {
            case(MS_SHAPE_POINT):
              psNode = xmlNewChild(psParent, NULL, BAD_CAST "msGeometry", NULL);
              xmlSetNs(psNode,xmlNewNs(psNode, NULL,  NULL));
              if (psShape->line[0].numpoints > 1)
              {
                  psPointNode = xmlNewChild(psNode, NULL, BAD_CAST "MultiPoint", NULL);
                  xmlSetNs(psPointNode,xmlNewNs(psPointNode, BAD_CAST "http://www.opengis.net/gml",  
                                                BAD_CAST "gml"));
                   
                  if (pszEpsg)
                    xmlNewProp(psPointNode, BAD_CAST "srsName", BAD_CAST pszEpsg);
              }
              else
                psPointNode= psNode;

              /*add all points */
              for(i=0; i<psShape->line[0].numpoints; i++)
              {
                  psNode = xmlNewChild(psPointNode, NULL, BAD_CAST "Point", NULL);
                  xmlSetNs(psNode,xmlNewNs(psNode, 
                                           BAD_CAST "http://www.opengis.net/gml",  
                                           BAD_CAST "gml"));
                  if (pszEpsg)
                    xmlNewProp(psNode, BAD_CAST "srsName", BAD_CAST pszEpsg);

                  pszTmp = double2string(psShape->line[0].point[0].x);
                  pszTmp = strcatalloc(pszTmp, ",");
                  pszTmp = strcatalloc(pszTmp, 
                                       double2string(psShape->line[0].point[0].y));
                  psNode = xmlNewChild(psNode, NULL, BAD_CAST "coordinates", BAD_CAST pszTmp);
                  xmlSetNs(psNode,xmlNewNs(psNode, BAD_CAST "http://www.opengis.net/gml", BAD_CAST "gml"));
                  free(pszTmp);
                  
              }
              break;
              
            case(MS_SHAPE_LINE):
              psNode = xmlNewChild(psParent, NULL, BAD_CAST "msGeometry", NULL);
              xmlSetNs(psNode,xmlNewNs(psNode, NULL,  NULL));
              if (psShape->numlines > 1)
              {
                  psLineNode = xmlNewChild(psNode, NULL, BAD_CAST "MultiLineString", NULL);
                  xmlSetNs(psLineNode,xmlNewNs(psLineNode, 
                                               BAD_CAST "http://www.opengis.net/gml",  
                                               BAD_CAST "gml"));
                   
                  if (pszEpsg)
                    xmlNewProp(psLineNode, BAD_CAST "srsName", BAD_CAST pszEpsg);
              }
              else
                psLineNode= psNode;

              for(i=0; i<psShape->numlines; i++)
              {
                  if (psShape->numlines > 1)
                  {
                      psNode = xmlNewChild(psLineNode, NULL, BAD_CAST "lineStringMember", NULL);
                      xmlSetNs(psNode,xmlNewNs(psNode, 
                                               BAD_CAST "http://www.opengis.net/gml",  
                                               BAD_CAST "gml"));
                      psNode = xmlNewChild(psNode, NULL, BAD_CAST "LineString", NULL);
                      xmlSetNs(psNode,xmlNewNs(psNode, 
                                               BAD_CAST "http://www.opengis.net/gml",  
                                               BAD_CAST "gml"));
                  }
                  else
                  {
                      psNode = xmlNewChild(psLineNode, NULL, BAD_CAST "LineString", NULL);
                      xmlSetNs(psNode,xmlNewNs(psNode, 
                                               BAD_CAST "http://www.opengis.net/gml",  
                                               BAD_CAST "gml"));
                  }
                  if (pszEpsg)
                    xmlNewProp(psNode, BAD_CAST "srsName", BAD_CAST pszEpsg);

                  pszTmp = NULL;
                  for(j=0; j<psShape->line[i].numpoints; j++)
                  {
                      pszTmp = strcatalloc(pszTmp, 
                                           double2string(psShape->line[i].point[j].x));
                      pszTmp = strcatalloc(pszTmp, ",");
                      pszTmp = strcatalloc(pszTmp, 
                                           double2string(psShape->line[i].point[j].y));
                      pszTmp = strcatalloc(pszTmp, " ");
                  }
                  psNode = xmlNewChild(psNode, NULL, BAD_CAST "coordinates", BAD_CAST pszTmp);
                  xmlSetNs(psNode,xmlNewNs(psNode, BAD_CAST "http://www.opengis.net/gml", BAD_CAST "gml"));
                  free(pszTmp);
              }

              break;

            case(MS_SHAPE_POLYGON):
              psNode = xmlNewChild(psParent, NULL, BAD_CAST "msGeometry", NULL);
              xmlSetNs(psNode,xmlNewNs(psNode, NULL,  NULL));
              if (psShape->numlines > 1)
              {
                  psPolygonNode = xmlNewChild(psNode, NULL, BAD_CAST "MultiPolygon", NULL);
                  xmlSetNs(psPolygonNode,
                           xmlNewNs(psPolygonNode, BAD_CAST "http://www.opengis.net/gml",
                                    BAD_CAST "gml"));
                   
                  if (pszEpsg)
                    xmlNewProp(psPolygonNode, BAD_CAST "srsName", BAD_CAST pszEpsg);
              }
              else
                psPolygonNode= psNode;

              panOuterList = msGetOuterList(psShape);
               
              for(i=0; i<psShape->numlines; i++)
              {        
                  if(panOuterList[i] != MS_TRUE)
                    continue;

                  panInnerList = msGetInnerList(psShape, i, panOuterList);

                  if (psShape->numlines > 1)
                  {
                      psNode = xmlNewChild(psPolygonNode, NULL, BAD_CAST "polygonMember", NULL);
                      xmlSetNs(psNode,xmlNewNs(psNode, BAD_CAST "http://www.opengis.net/gml",  
                                               BAD_CAST "gml"));
                      psNode = xmlNewChild(psNode, NULL, BAD_CAST "Polygon", NULL);
                      xmlSetNs(psNode,xmlNewNs(psNode, BAD_CAST "http://www.opengis.net/gml",  
                                               BAD_CAST "gml"));
                  }
                  else
                  {
                      psNode = xmlNewChild(psPolygonNode, NULL, BAD_CAST "Polygon", NULL);
                      xmlSetNs(psNode,xmlNewNs(psNode, BAD_CAST "http://www.opengis.net/gml",  
                                               BAD_CAST "gml"));
                  }
                  if (pszEpsg)
                    xmlNewProp(psNode, BAD_CAST "srsName", BAD_CAST pszEpsg);

                  psNode = xmlNewChild(psNode, NULL, BAD_CAST "outerBoundaryIs", NULL);
                  xmlSetNs(psNode,xmlNewNs(psNode, BAD_CAST "http://www.opengis.net/gml",  
                                           BAD_CAST "gml"));
                  psNode = xmlNewChild(psNode, NULL, BAD_CAST "LinearRing", NULL);
                  xmlSetNs(psNode,xmlNewNs(psNode, BAD_CAST "http://www.opengis.net/gml",  
                                           BAD_CAST "gml"));
                   
                  pszTmp = NULL;
                  for(j=0; j<psShape->line[i].numpoints; j++)
                  {
  
                      pszTmp = 
                        strcatalloc(pszTmp, 
                                    double2string(psShape->line[i].point[j].x));
                      pszTmp = strcatalloc(pszTmp, ",");
                      pszTmp = 
                        strcatalloc(pszTmp, 
                                    double2string(psShape->line[i].point[j].y));
                      pszTmp = strcatalloc(pszTmp, " ");
                  }
                  psNode = xmlNewChild(psNode, NULL, BAD_CAST "coordinates", BAD_CAST pszTmp);
                  xmlSetNs(psNode,xmlNewNs(psNode, 
                                           BAD_CAST "http://www.opengis.net/gml", 
                                           BAD_CAST "gml"));
                  free(pszTmp);

                  if (panInnerList)
                    free(panInnerList);
              }

              if (panOuterList)
                free(panOuterList);

              break;

            default:
              break;
        }
                   
    }   
      
}


/************************************************************************/
/*                            msSOSAddMemberNode                        */
/*                                                                      */
/*      Add a memeber node corresponding to a feature.                  */
/*      Assuming that the layer is opened and msLayerGetItems is        */
/*      called on it.                                                   */
/************************************************************************/
void msSOSAddMemberNode(xmlNodePtr psParent, mapObj *map, layerObj *lp, 
                        int iFeatureId)
{
    xmlNodePtr psObsNode, psNode, psLayerNode;
    const char *pszEpsg = NULL, *pszValue = NULL;
    int status,i,j;
    shapeObj sShape;
    char szTmp[256];
    layerObj *lpfirst = NULL;
    const char *pszTimeField = NULL;
    char *pszTmp = NULL;
    char *pszTime = NULL;

    xmlNsPtr psNsGml =xmlNewNs(NULL, BAD_CAST "http://www.opengis.net/gml", BAD_CAST "gml");

    if (psParent)
    {
        msInitShape(&sShape);
    
        status = msLayerGetShape(lp, &sShape, 
                                 lp->resultcache->results[iFeatureId].tileindex, 
                                 lp->resultcache->results[iFeatureId].shapeindex);
        if(status != MS_SUCCESS) 
          return;

        psNode = xmlNewChild(psParent, NULL, BAD_CAST "member", NULL);
        
        psObsNode = xmlNewChild(psNode, NULL, BAD_CAST BAD_CAST "Observation", BAD_CAST pszValue);
        

        /* order of elements is time, location, procedure, observedproperty
         featureofinterest, result */

        /* time*/
        pszTimeField =  msOWSLookupMetadata(&(lp->metadata), "SO",
                                            "timeitem");
        if (pszTimeField && sShape.values)
        {
            for(i=0; i<lp->numitems; i++) 
            {
                if (strcasecmp(lp->items[i], pszTimeField) == 0)
                {
                    if (sShape.values[i] && strlen(sShape.values[i]) > 0)
                    {
                        pszTime = strcatalloc(pszTime, sShape.values[i]);
                        psNode = xmlNewChild(psObsNode, NULL, BAD_CAST "time", BAD_CAST pszTime);

                        xmlSetNs(psNode,xmlNewNs(psNode, NULL,  NULL));
                    }
                    break;
                
                }
            }
        }
        /*TODO add location,*/

        /*precedure*/
        pszValue = msOWSLookupMetadata(&(lp->metadata), "S", "procedure");
        if (pszValue)
        {
            sprintf(szTmp, "%s", "urn:ogc:def:procedure:");
            pszTmp = strcatalloc(pszTmp, szTmp);
            pszTmp = strcatalloc(pszTmp, (char *)pszValue);
            
            psNode =  xmlNewChild(psObsNode, NULL, BAD_CAST "procedure", NULL);
            xmlNewNsProp(psNode,
                         xmlNewNs(NULL, BAD_CAST "http://www.w3.org/1999/xlink", 
                                  BAD_CAST "xlink"), BAD_CAST "href", BAD_CAST pszTmp);
            msFree(pszTmp);
            pszTmp = NULL;
        }

        /*observed propery*/
        pszValue = msOWSLookupMetadata(&(lp->metadata), "S", 
                                       "observedProperty_id");
        if (pszValue)
        {
            psNode= xmlNewChild(psObsNode, NULL, BAD_CAST "observedProperty", BAD_CAST pszValue);
             xmlSetNs(psNode,xmlNewNs(psNode, NULL,  NULL));
        }

        /*TODO add featureofinterest*/

        /* add result : gml:featureMember of all selected elements */
        psNode = xmlNewChild(psObsNode, NULL, BAD_CAST "result", NULL);

        /*TODO should we add soemwhere the units of the value :
          <om:result uom="units.xml#cm">29.00</om:result> */
        
        
#ifdef USE_PROJ
        if(msProjectionsDiffer(&(lp->projection), &(map->projection)))
          msProjectShape(&lp->projection, &lp->projection, &sShape);
#endif
        psNode = xmlNewChild(psNode, NULL, BAD_CAST "featureMember", NULL);
        xmlSetNs(psNode,xmlNewNs(psNode, BAD_CAST "http://www.opengis.net/gml", BAD_CAST "gml"));

        /*TODO : add namespaces like wfs " ms and a url to mapserve ? */
        psLayerNode = xmlNewChild(psNode, NULL, BAD_CAST lp->name, NULL);
        xmlSetNs(psLayerNode,xmlNewNs(psLayerNode, NULL,  NULL));
        
        /*bbox*/
        pszEpsg = NULL;
#ifdef USE_PROJ
        pszEpsg = msOWSGetEPSGProj(&(map->projection), &(map->web.metadata), "SO", MS_TRUE);
        if (!pszEpsg)
          pszEpsg = msOWSGetEPSGProj(&(lp->projection), &(lp->metadata), "SO", MS_TRUE);
#endif        
        msSOSAddBBNode(psLayerNode, sShape.bounds.minx, sShape.bounds.miny, sShape.bounds.maxx, 
                       sShape.bounds.maxy, pszEpsg, psNsGml);

        /*geometry*/
        msSOSAddGeometryNode(psLayerNode, lp, &sShape, pszEpsg);

        /*attributes */
        /* TODO only output attributes where there is a sos_%s_componenturl (to be discussed)*/
        /* the first layer is the one that has to have all the metadata defined */
        lpfirst = msSOSGetFirstLayerForOffering(map, 
                                                msOWSLookupMetadata(&(lp->metadata), "S", 
                                                                    "offering_id"), 
                                                msOWSLookupMetadata(&(lp->metadata), "S", 
                                                                    "observedProperty_id"));

        if (lpfirst && msLayerOpen(lpfirst) == MS_SUCCESS && 
            msLayerGetItems(lpfirst) == MS_SUCCESS)
        {
            for(i=0; i<lpfirst->numitems; i++) 
            {
                sprintf(szTmp, "%s_componenturl", lpfirst->items[i]);
                pszValue = msOWSLookupMetadata(&(lpfirst->metadata), "S", szTmp);
                if (pszValue)
                {
                    for (j=0; j<lp->numitems; j++)
                    {
                        if (strcasecmp(lpfirst->items[i],  lpfirst->items[j]) == 0)
                        {
                            /*if there is an alias used, use it to ooutput the
                              parameter name : eg "sos_AMMON_DIS_alias" "Amonia"  */
                            sprintf(szTmp, "%s_alias", lpfirst->items[i]);
                            pszValue = msOWSLookupMetadata(&(lpfirst->metadata), "S", szTmp);
                            if (pszValue)
                            {
                              pszTmp = msEncodeHTMLEntities(pszValue);
                              psNode = xmlNewChild(psLayerNode, NULL, BAD_CAST pszTmp, 
                                                   BAD_CAST sShape.values[j]);
                              free(pszTmp);
                            } 
                            else
                            {
                              pszTmp = msEncodeHTMLEntities(lpfirst->items[i]);
                              psNode = xmlNewChild(psLayerNode, NULL, BAD_CAST lpfirst->items[i], 
                                                   BAD_CAST sShape.values[j]);
                              free(pszTmp);
                            } 

                            xmlSetNs(psNode,xmlNewNs(psNode, NULL,  NULL));
                            break;
                        }
                    }
                }
            }
            if (lp->index != lpfirst->index)
              msLayerClose(lpfirst);

            /*add also the time field */
            if (pszTime)
            {
                psNode = xmlNewChild(psLayerNode, NULL, BAD_CAST "time", BAD_CAST pszTime);
                xmlSetNs(psNode,xmlNewNs(psNode, NULL,  NULL));

                msFree(pszTime);
            }
                
        }
    }        
}
        


/************************************************************************/
/*                            msSOSParseTimeGML                         */
/*                                                                      */
/*      Utility function to convert a gml time value to a               */
/*      string. Supported gml times are :                               */
/*                                                                      */
/*       -  <gml:TimePeriod>                                            */
/*           <gml:beginPosition>2005-09-01T11:54:32</gml:beginPosition> */
/*            <gml:endPosition>2005-09-02T14:54:32</gml:endPosition>    */
/*          </gml:TimePeriod>                                           */
/*        This will be converted to startime/endtime                    */
/*                                                                      */
/*       - <gml:TimeInstant>                                            */
/*           <gml:timePosition>2003-02-13T12:28-08:00</gml:timePosition>*/
/*           </gml:TimeInstant>                                         */
/*       This will retunr the timevalue as a string.                    */
/*                                                                      */
/*       The caller of the function should free the return value.       */
/************************************************************************/
char *msSOSParseTimeGML(char *pszGmlTime)
{
    char *pszReturn = NULL, *pszBegin = NULL, *pszEnd = NULL;
    CPLXMLNode *psRoot=NULL, *psChild=NULL;
    CPLXMLNode *psTime=NULL, *psBegin=NULL, *psEnd=NULL;

    if (pszGmlTime)
    {
        psRoot = CPLParseXMLString(pszGmlTime);
        if(!psRoot)
          return NULL;
        CPLStripXMLNamespace(psRoot, "gml", 1);
        
        if (psRoot->eType == CXT_Element && 
            (EQUAL(psRoot->pszValue,"TimePeriod") || 
             EQUAL(psRoot->pszValue,"TimeInstant")))
        {
            if (EQUAL(psRoot->pszValue,"TimeInstant"))
            {
                psChild = psRoot->psChild;
                if (psChild && EQUAL(psChild->pszValue,"timePosition"))
                {
                    psTime = psChild->psNext;
                    if (psTime && psTime->pszValue && psTime->eType == CXT_Text)
                      pszReturn = strdup(psTime->pszValue);
                }
            }
            else
            {
                psBegin = psRoot->psChild;
                if (psBegin)
                  psEnd = psBegin->psNext;

                if (psBegin && EQUAL(psBegin->pszValue, "beginPosition") &&
                    psEnd && EQUAL(psEnd->pszValue, "endPosition"))
                {
                    if (psBegin->psChild && psBegin->psChild->pszValue &&
                        psBegin->psChild->eType == CXT_Text)
                      pszBegin = strdup( psBegin->psChild->pszValue);

                    if (psEnd->psChild && psEnd->psChild->pszValue &&
                        psEnd->psChild->eType == CXT_Text)
                      pszEnd = strdup(psEnd->psChild->pszValue);

                    if (pszBegin && pszEnd)
                    {
                        pszReturn = strdup(pszBegin);
                        pszReturn = strcatalloc(pszReturn, "/");
                        pszReturn = strcatalloc(pszReturn, pszEnd);
                    }
                }
            }
        }
    }
        
    return pszReturn;
}


/************************************************************************/
/*                           msSOSGetCapabilities                       */
/*                                                                      */
/*      getCapabilities request handler.                                */
/************************************************************************/
int msSOSGetCapabilities(mapObj *map, int nVersion, cgiRequestObj *req)
{
    xmlDocPtr psDoc = NULL;       /* document pointer */
    xmlNodePtr psRootNode, psMainNode, psNode;
    xmlNodePtr psOfferingNode;
    xmlNodePtr psTmpNode;


    char *schemalocation = NULL;
    char *dtd_url = NULL;
    char *script_url=NULL, *script_url_encoded=NULL;

    int i,j,k;
    layerObj *lp = NULL, *lpTmp = NULL;
    const char *value = NULL;
    char *pszTmp = NULL;
    char *pszProcedure = NULL;
    char szTmp[256]; 

     /* array of offering */
    char **papsOfferings = NULL; 
    int nOfferings  =0, nCurrentOff = -1;
    int nProperties = 0;
    char **papszProperties = NULL;

    /*
      char workbuffer[5000];
      int nSize = 0;
    int iIndice = 0;
    xmlChar *buffer = NULL;
    int size = 0;
    */

    int iItemPosition = -1;
    shapeObj sShape;
    int status;

     /* for each layer it indicates the indice to be used in papsOfferings
        (to associate it with the offering) */
    int *panOfferingLayers = NULL;
   
    char **papsProcedures = NULL;
    int nDistinctProcedures =0;

    FILE *stream=NULL;

    xmlNsPtr     psNsGml       = NULL;


    psDoc = xmlNewDoc(BAD_CAST "1.0");

    psRootNode = xmlNewNode(NULL, BAD_CAST "Capabilities");

    xmlDocSetRootElement(psDoc, psRootNode);

    psNsGml =xmlNewNs(NULL, BAD_CAST "http://www.opengis.net/gml", BAD_CAST "gml");

    /* name spaces */
    //psNameSpace = xmlNewNsProp(psRootNode, "url",  "sos");
    //psNameSpace = xmlNewNs(psRootNode, "http://www.opengis.net/sos",  "sos");
    xmlSetNs(psRootNode,  xmlNewNs(psRootNode, BAD_CAST "http://www.opengis.net/gml", BAD_CAST "gml"));
    xmlSetNs(psRootNode,  xmlNewNs(psRootNode, BAD_CAST "http://www.opengis.net/om", BAD_CAST "om"));
    xmlSetNs(psRootNode,  xmlNewNs(psRootNode, BAD_CAST "http://www.opengis.net/ows", BAD_CAST "ows"));
    xmlSetNs(psRootNode,  xmlNewNs(psRootNode, BAD_CAST "http://www.opengis.net/swe", BAD_CAST "swe"));
    xmlSetNs(psRootNode,  xmlNewNs(psRootNode, BAD_CAST "http://www.w3.org/1999/xlink", BAD_CAST "xlink"));
    xmlSetNs(psRootNode,  xmlNewNs(psRootNode, BAD_CAST "http://www.w3.org/2001/XMLSchema-instance", BAD_CAST "xsi"));
    xmlSetNs(psRootNode,   xmlNewNs(psRootNode, BAD_CAST "http://www.opengis.net/sos", BAD_CAST "sos"));
    

    /*version fixed for now*/
    xmlNewProp(psRootNode, BAD_CAST "version", BAD_CAST pszSOSVersion);

    /*schema fixed*/
    schemalocation = msEncodeHTMLEntities( msOWSGetSchemasLocation(map) );
    /*TODO : review this*/
    dtd_url = strdup("http://www.opengis.net/sos ");
    dtd_url = strcatalloc(dtd_url, schemalocation);
    dtd_url = strcatalloc(dtd_url, "/sos/");
    dtd_url = strcatalloc(dtd_url, (char *)pszSOSVersion);
    dtd_url = strcatalloc(dtd_url, "/sosGetCapabilities.xsd");
    xmlNewNsProp(psRootNode, NULL, BAD_CAST "xsi:schemaLocation", BAD_CAST dtd_url);

    /*service identification*/
    psTmpNode = xmlAddChild(psRootNode, msOWSCommonServiceIdentification(map, "SOS", pszSOSVersion));

    /*service provider*/
    psTmpNode = xmlAddChild(psRootNode, msOWSCommonServiceProvider(map));

    /*operation metadata */

    if ((script_url=msOWSGetOnlineResource(map, "SO", "onlineresource", req)) == NULL ||
        (script_url_encoded = msEncodeHTMLEntities(script_url)) == NULL)
    {
        return msSOSException(map, "NoApplicableCode", "NoApplicableCode");
    }

    psMainNode = xmlAddChild(psRootNode, msOWSCommonOperationsMetadata());

    psNode     = xmlAddChild(psMainNode, msOWSCommonOperationsMetadataOperation("GetCapabilities", 1, script_url_encoded));
    psTmpNode  = xmlAddChild(psNode, msOWSCommonOperationsMetadataParameter("service", 1, "SOS"));
    psTmpNode  = xmlAddChild(psNode, msOWSCommonOperationsMetadataParameter("version", 0, (char *)pszSOSVersion));

    psNode     = xmlAddChild(psMainNode, msOWSCommonOperationsMetadataOperation("DescribeSensor", 1, script_url_encoded));
    psTmpNode  = xmlAddChild(psNode, msOWSCommonOperationsMetadataParameter("service", 1, "SOS"));
    psTmpNode  = xmlAddChild(psNode, msOWSCommonOperationsMetadataParameter("version", 1, (char *)pszSOSVersion));
    psTmpNode  = xmlAddChild(psNode, msOWSCommonOperationsMetadataParameter("sensorid", 1, NULL));
    psTmpNode  = xmlAddChild(psNode, msOWSCommonOperationsMetadataParameter("outputFormat", 1, (char *)pszSOSDescribeSensorMimeType));

    psNode     = xmlAddChild(psMainNode, msOWSCommonOperationsMetadataOperation("GetObservation", 1, script_url_encoded));
    psTmpNode  = xmlAddChild(psNode, msOWSCommonOperationsMetadataParameter("service", 1, "SOS"));
    psTmpNode  = xmlAddChild(psNode, msOWSCommonOperationsMetadataParameter("version", 1, (char *)pszSOSVersion));
    psTmpNode  = xmlAddChild(psNode, msOWSCommonOperationsMetadataParameter("offering", 1, NULL));
    psTmpNode  = xmlAddChild(psNode, msOWSCommonOperationsMetadataParameter("observedproperty", 1, NULL));
    psTmpNode  = xmlAddChild(psNode, msOWSCommonOperationsMetadataParameter("eventtime", 0, NULL));
    psTmpNode  = xmlAddChild(psNode, msOWSCommonOperationsMetadataParameter("procedure", 0, NULL));
    psTmpNode  = xmlAddChild(psNode, msOWSCommonOperationsMetadataParameter("featureofinterest", 0, NULL));
    psTmpNode  = xmlAddChild(psNode, msOWSCommonOperationsMetadataParameter("result", 0, NULL));
    psTmpNode  = xmlAddChild(psNode, msOWSCommonOperationsMetadataParameter("responseFormat", 1, (char *)pszSOSGetObservationMimeType));

    /*TODO : add <ogc:Filter_Capabilities> */

    /*Offerings */
     psNode = xmlNewChild(psRootNode, NULL, BAD_CAST "Content", NULL);
     psMainNode = xmlNewChild(psNode, NULL, BAD_CAST "ObservationOfferingList", NULL);
                                             
     
     /*go through the layers and check for metadata sos_offering_id.
       One or more layers could have the same offering id. In that case they
       are adverized as the same offering. The first layer that has*/

     if (map->numlayers)
     {
         

         papsOfferings = (char **)malloc(sizeof(char *)*map->numlayers);
         panOfferingLayers = (int *)malloc(sizeof(int)*map->numlayers);
         for (i=0; i<map->numlayers; i++)
           panOfferingLayers[i] = -1;

         
         for (i=0; i<map->numlayers; i++)
         {
             lp = &(map->layers[i]);
             value = msOWSLookupMetadata(&(lp->metadata), "S", "offering_id");
             if (value)
             {
                 nCurrentOff = -1;
                 for (j=0; j<nOfferings; j++)
                 {
                     if (strcasecmp(value, papsOfferings[j]) == 0)
                     {
                         nCurrentOff = j;
                         break;
                     }
                 }
                 if (nCurrentOff >= 0) /* existing offering */
                   panOfferingLayers[i] = nCurrentOff;
                 else /*new offering */
                 {
                     papsOfferings[nOfferings] = strdup(value);
                     panOfferingLayers[i] = nOfferings;
                     nOfferings++;
                 }
             }
         }

         if (nOfferings > 0)
         {
             for (i=0; i<nOfferings; i++)
             {
                 psOfferingNode = 
                   xmlNewChild(psMainNode, NULL,BAD_CAST "ObservationOffering", NULL);
                 xmlNewNsProp(psOfferingNode, psNsGml,
                              BAD_CAST "id", BAD_CAST papsOfferings[i]);
                 for (j=0; j<map->numlayers; j++)
                 {
                     if (panOfferingLayers[j] == i) /*first layer of the offering */
                       break;
                 }
                 lp = &(map->layers[j]); /*first layer*/
                 value = msOWSLookupMetadata(&(lp->metadata), "S", "offering_name");
                 if (value)
                 {
                     psNode = xmlNewChild(psOfferingNode, psNsGml, BAD_CAST "name", BAD_CAST value);
                 }
                 
                 /*bounding box */
                 /*TODO : if sos_offering_extent does not exist compute extents 
                          Check also what happen if epsg not present */
                 value = msOWSLookupMetadata(&(lp->metadata), "S", "offering_extent");
                 if (value)
                 {
                     char **tokens;
                     int n;
                     tokens = split(value, ',', &n);
                     if (tokens==NULL || n != 4) {
                         msSetError(MS_SOSERR, "Wrong number of arguments for offering_extent.",
                                    "msSOSGetCapabilities()");
                         return msSOSException(map, "offering_extent", "InvalidParameterValue");
                     }
                     value = msOWSGetEPSGProj(&(lp->projection),
                                              &(lp->metadata), "SO", MS_TRUE);
                     if (value)
                       msSOSAddBBNode(psOfferingNode, atof(tokens[0]), atof(tokens[1]),
                                      atof(tokens[2]), atof(tokens[3]), value, psNsGml);
                     msFreeCharArray(tokens, n);
                       
                 }

                 /*description*/
                 value = msOWSLookupMetadata(&(lp->metadata), "S", 
                                             "offering_description");
                 if (value)
                 {
                     psNode = 
                       xmlNewChild(psOfferingNode, psNsGml, BAD_CAST "description", BAD_CAST value);
                 }

                 /*time*/
                 value = msOWSLookupMetadata(&(lp->metadata), "S", 
                                             "offering_timeextent");
                 if (value)
                 {
                     char **tokens;
                     int n;
                     char *pszEndTime = NULL;
                     tokens = split(value, '/', &n);
                     if (tokens==NULL || (n != 1 && n!=2)) {
                         msSetError(MS_SOSERR, "Wrong number of arguments for offering_timeextent.",
                                    "msSOSGetCapabilities()");
                         return msSOSException(map, "offering_timeextent", "InvalidParameterValue");
                     }

                     if (n == 2) /* end time is empty. It is going to be set as "now*/
                       pszEndTime = tokens[1];

                     msSOSAddTimeNode(psOfferingNode, tokens[0], pszEndTime, psNsGml);
                     msFreeCharArray(tokens, n);
                     
                 }
                 
                 /*procedure : output all procedure links for the offering */
                 for (j=0; j<map->numlayers; j++)
                 {
                     if (panOfferingLayers[j] == i)
                     {
                         
                         
                         value = msOWSLookupMetadata(&(map->layers[j].metadata), "S", 
                                                     "procedure");
                         if (value && strlen(value) > 0)
                         {   
                             /*value could be a list of procedure*/
                             char **tokens;
                             int n = 0;
                             tokens = split(value, ' ', &n);
                             for (k=0; k<n; k++)
                             {
                             /*TODO review the urn output */
                                 sprintf(szTmp, "%s", "urn:ogc:def:procedure:");
                                 pszTmp = strcatalloc(pszTmp, szTmp);
                                 pszTmp = strcatalloc(pszTmp, tokens[k]);

                                 psNode = 
                                   xmlNewChild(psOfferingNode, NULL, BAD_CAST "procedure", NULL);
                                 xmlNewNsProp(psNode,
                                              xmlNewNs(NULL, BAD_CAST "http://www.w3.org/1999/xlink", 
                                                       BAD_CAST "xlink"), BAD_CAST "href", BAD_CAST pszTmp);
                                 msFree(pszTmp);
                                 pszTmp = NULL;
                             }
                             msFreeCharArray(tokens, n);
                         }
                         else if ((value = msOWSLookupMetadata(&(map->layers[j].metadata), "S", 
                                                               "procedure_item")))
                         {
                             /* if a procedure_item is used, it means that the procedure 
                                (or sensor) need to be extracted from the data. Thus we need to 
                                query the layer and get the values from each feature */
                          

                             lpTmp = &map->layers[j];
                             if (lpTmp->template == NULL)
                               lpTmp->template = strdup("ttt");
                             msQueryByRect(map, j, map->extent);

                             /*check if the attribute specified in the procedure_item is available
                               on the layer*/
                             iItemPosition = -1;
                             if (msLayerOpen(lpTmp) == MS_SUCCESS && 
                                 msLayerGetItems(lpTmp) == MS_SUCCESS &&
                                 lpTmp->resultcache && lpTmp->resultcache->numresults > 0)
                             {
                                 for(k=0; k<lpTmp->numitems; k++) 
                                 {
                                     if (strcasecmp(lpTmp->items[k], value) == 0)
                                     {
                                         iItemPosition = k;
                                         break;
                                     }
                                 }
                                 if (iItemPosition == -1)
                                 {
                                     msSetError(MS_SOSERR, "procedure_item %s could not be found on the layer %s",
                                    "msSOSGetCapabilities()", value, lpTmp->name);
                                     return msSOSException(map, "procedure_item", "InvalidValue");
                                 }

                                 /*for each selected feature, grab the value of the prodedire_item*/
                                 /* do not duplicate sensor ids if they are the same */

                                 /*keep list of distinct procedures*/
                                 papsProcedures = 
                                   (char **)malloc(sizeof(char *) * lpTmp->resultcache->numresults);
                                 nDistinctProcedures = 0;
                                 for(k=0; k<lpTmp->resultcache->numresults; k++)
                                   papsProcedures[k] = NULL;
                                 

                                 for(k=0; k<lpTmp->resultcache->numresults; k++)
                                 {      
                                     msInitShape(&sShape);
                                     status = msLayerGetShape(lp, &sShape, 
                                                              lpTmp->resultcache->results[k].tileindex, 
                                                              lpTmp->resultcache->results[k].shapeindex);
                                     if(status != MS_SUCCESS) 
                                       continue;

                                     if (sShape.values[iItemPosition])
                                     {
                                         pszProcedure = strcatalloc(pszProcedure, sShape.values[iItemPosition]);
                                         if (!_IsInList(papsProcedures, nDistinctProcedures, pszProcedure))
                                         {
                                               papsProcedures[nDistinctProcedures] = strdup(pszProcedure);
                                               nDistinctProcedures++;
                                               sprintf(szTmp, "%s", "urn:ogc:def:procedure:");
                                               pszTmp = strcatalloc(pszTmp, szTmp);
                                               pszTmp = strcatalloc(pszTmp, pszProcedure);

                                               psNode = 
                                               xmlNewChild(psOfferingNode, NULL, BAD_CAST "procedure", NULL);
                                               xmlNewNsProp(psNode,
                                                            xmlNewNs(NULL, BAD_CAST "http://www.w3.org/1999/xlink", 
                                                                     BAD_CAST "xlink"), BAD_CAST "href", BAD_CAST pszTmp);
                                               msFree(pszTmp);
                                               pszTmp = NULL;
                                               
                                           }
                                         msFree(pszProcedure);
                                         pszProcedure = NULL;
                                     }
                                 }
                                 for(k=0; k<lpTmp->resultcache->numresults; k++)
                                   if (papsProcedures[k] != NULL)
                                     msFree(papsProcedures[k]);
                                 msFree(papsProcedures);
                                 
                                 msLayerClose(lpTmp);
                                 
                             }
                             else
                             {  
                                 msSetError(MS_SOSERR, "procedure_item %s could not be found on the layer %s",
                                            "msSOSGetCapabilities()", value, lpTmp->name);
                                 return msSOSException(map, "procedure_item", "InvalidValue");
                             }
                         }
                         else
                         {
                              msSetError(MS_SOSERR, "Manadatory metadata procedure could not be found on the layer %s",
                                            "msSOSGetCapabilities()", map->layers[j].name);
                                 return msSOSException(map, "procedure_item", "MissingValue");
                         }
                         
                     }
                 }
                 /*observed property */
                 /* observed property are equivalent to layers. We can group 
                    sevaral layers using the same sos_observedproperty_id. The 
                    components are the attributes. Componenets are exposed 
                    using the metadata sos_%s_componenturl "url value" where 
                    the %s is the name of the  attribute.We need at least one.*/
                 
                 nProperties = 0;
                 papszProperties = 
                   (char **)malloc(sizeof(char *)*map->numlayers);
                 
                 for (j=0; j<map->numlayers; j++)
                 {
                     if (panOfferingLayers[j] == i)
                     {
                         if ((value = 
                             msOWSLookupMetadata(&(map->layers[j].metadata), "S", 
                                                 "observedProperty_id")))
                         {
                             for (k=0; k<nProperties; k++)
                             {
                                 if (strcasecmp(value, papszProperties[k]) == 0)
                                   break;
                             }
                             if (k == nProperties)/*not found*/
                             {
                                 papszProperties[nProperties] = strdup(value);
                                 nProperties++;
                                 msSOSAddPropertyNode(psOfferingNode, 
                                                         &(map->layers[j]), psNsGml);
                             }
                         }
                     }
                 }
                 for (j=0; j<nProperties; j++)
                   free(papszProperties[j]);
                 free(papszProperties);

                 /*TODO <sos:featureOfInterest> : we will use the offering_extent that was used
                  for the bbox. I Think we should generate a gml:FeatureCollection which 
                  gathers the extents on each layer associate with the offering : something like :
                  <sos:featureOfInterest>
                    <gml:FeatureCollection>
	              <gml:featureMember xlink:href="foi_ahlen">
	                  <om:Station xsi:type="om:StationType">
	                     <om:position>
	                        <gml:Point srsName="EPSG:31467">
                                     <gml:coordinates>342539 573506</gml:coordinates>
                                </gml:Point>
                             </om:position>
                              <om:procedureHosted xlink:href="urn:ogc:def:procedure:ifgi-sensor-1b"/>
                           </om:Station>
                      </gml:featureMember>
                      <gml:featureMember xlink:href="foi_ahlen_2">
                     ...
                     </gml:FeatureCollection>
                     </sos:featureOfInterest> */

                 value = msOWSLookupMetadata(&(lp->metadata), "S", "offering_extent");
                 if (value)
                 {
                     char **tokens;
                     int n;
                     tokens = split(value, ',', &n);
                     if (tokens==NULL || n != 4) {
                         msSetError(MS_SOSERR, "Wrong number of arguments for offering_extent.",
                                    "msSOSGetCapabilities()");
                         return msSOSException(map, "offering_extent", "InvalidParameterValue");
                     }
                     value = msOWSGetEPSGProj(&(lp->projection),
                                              &(lp->metadata), "SO", MS_TRUE);
                     if (value)
                     {
                         psNode = xmlNewChild(psOfferingNode, NULL, BAD_CAST "featureOfInterest", 
                                              NULL);

                         msSOSAddBBNode(psNode, atof(tokens[0]), atof(tokens[1]),
                                        atof(tokens[2]), atof(tokens[3]), value, psNsGml);
                     }

                     msFreeCharArray(tokens, n);
                       
                 }
                 
                 psNode = xmlNewChild(psOfferingNode, NULL, BAD_CAST "responseFormat", 
                                      BAD_CAST pszSOSGetObservationMimeType);

             }/*end of offerings*/
         }
             

     }/* end of offerings */

     if ( msIO_needBinaryStdout() == MS_FAILURE )
       return MS_FAILURE;
     
     msIO_printf("Content-type: text/xml%c%c",10,10);
    
    /*TODO* : check the encoding validity. Internally libxml2 uses UTF-8
    msOWSPrintEncodeMetadata(stdout, &(map->web.metadata),
                             "SO", "encoding", OWS_NOERR,
                             "<?xml version='1.0' encoding=\"%s\" standalone=\"no\" ?>\n",
                             "ISO-8859-1");
    */
     /*xmlDocDumpFormatMemoryEnc(psDoc, &buffer, &size, "ISO-8859-1", 1);*/
     
     /* xmlDocDump crashs withe the prebuild windows binaries distibutes at the libxml site???.
      It works with locally build binaries*/
     stream = stdout;

     xmlDocDump(stream, psDoc);

     /*free buffer and the document */
     /*xmlFree(buffer);*/
     xmlFreeDoc(psDoc);

     free(dtd_url);
     free(schemalocation);

    /*
     *Free the global variables that may
     *have been allocated by the parser.
     */
     xmlCleanupParser();


    return(MS_SUCCESS);

    
     /*
    nSize = sizeof(workbuffer);
    nSize = nSize-1;*/ /* the last character for the '\0' */
     
    /*
    if (size > nSize)
    {
         iIndice = 0;
         while ((iIndice + nSize) <= size)
         {
             snprintf(workbuffer, (sizeof(workbuffer)-1), "%s", buffer+iIndice );
             workbuffer[sizeof(workbuffer)-1] = '\0';
             msIO_printf("%s", workbuffer);

             iIndice +=nSize;
         }
         if (iIndice < size)
         {
              sprintf(workbuffer, "%s", buffer+iIndice );
              msIO_printf("%s", workbuffer);
         }
     }
    else
    {
        msIO_printf("%s", buffer);
    }
    */
}

/************************************************************************/
/*                           msSOSGetObservation                        */
/*                                                                      */
/*      GetObservation request handler                                  */
/************************************************************************/
int msSOSGetObservation(mapObj *map, int nVersion, char **names,
                        char **values, int numentries)

{
    char *pszOffering=NULL, *pszProperty=NULL, *pszResponseFormat=NULL, *pszTime = NULL, *pszVersion=NULL;
    char *pszFilter = NULL, *pszProdedure = NULL;
    char *pszBbox = NULL, *pszFeature=NULL;

    char *schemalocation = NULL;
    char *dtd_url = NULL;

    const char *pszTmp = NULL, *pszTmp2 = NULL;
    int i, j, k, bLayerFound = 0;
    layerObj *lp = NULL, *lpfirst = NULL; 
    const char *pszTimeExtent=NULL, *pszTimeField=NULL, *pszValue=NULL;
    FilterEncodingNode *psFilterNode = NULL;
    rectObj sBbox;


    xmlDocPtr psDoc = NULL;
    xmlNodePtr psRootNode,  psNode;
    char **tokens=NULL, **tokens1;
    int n=0, n1=0;
    xmlNsPtr     psNsGml       = NULL;
    FILE *stream=NULL;
    char *pszBuffer = NULL;
    const char *pszProcedureItem = NULL;

    sBbox = map->extent;

    psNsGml =xmlNewNs(NULL, BAD_CAST "http://www.opengis.net/gml", BAD_CAST "gml");

    for(i=0; i<numentries; i++) 
    {
         if (strcasecmp(names[i], "OFFERING") == 0)
           pszOffering = values[i];
         else if (strcasecmp(names[i], "OBSERVEDPROPERTY") == 0)
           pszProperty = values[i];
         else if ((strcasecmp(names[i], "EVENTTIME") == 0) ||
                  (strcasecmp(names[i], "TIME") == 0))
           pszTime = values[i];
         else if (strcasecmp(names[i], "RESULT") == 0)
           pszFilter = values[i];
         else if (strcasecmp(names[i], "PROCEDURE") == 0)
           pszProdedure = values[i];
         else if (strcasecmp(names[i], "FEATUREOFINTEREST") == 0)
           pszFeature = values[i];
         else if (strcasecmp(names[i], "BBOX") == 0)
           pszBbox = values[i];
         else if (strcasecmp(names[i], "RESPONSEFORMAT") == 0)
           pszResponseFormat = values[i];
         else if (strcasecmp(names[i], "VERSION") == 0)
           pszVersion = values[i];
     }

    /*TODO : validate for version number*/

    /* validates mandatory request elements */
    if (!pszVersion)
    {
        msSetError(MS_SOSERR, "Missing mandatory version parameter.",
                   "msSOSGetObservation()");
        return msSOSException(map, "version", "MissingParameterValue");
    }

    if (!pszOffering) 
    {
        msSetError(MS_SOSERR, "Missing mandatory Offering parameter.",
                   "msSOSGetObservation()");
        return msSOSException(map, "offering", "MissingParameterValue");
    }

    if (!pszProperty)
    {
        msSetError(MS_SOSERR, "Missing mandatory ObservedProperty parameter.",
                   "msSOSGetObservation()");
        return msSOSException(map, "observedproperty", "MissingParameterValue");
    }

    if (!pszResponseFormat)
    {
        msSetError(MS_SOSERR, "Missing mandatory responseFormat parameter.",
                   "msSOSGetObservation()");
        return msSOSException(map, "responseformat", "MissingParameterValue");
    }

    if (strcasecmp(pszResponseFormat, pszSOSGetObservationMimeType) != 0) {
        msSetError(MS_SOSERR, "Invalid responseFormat parameter %s.  Allowable values are: %s",
                   "msSOSDescribeSensor()", pszResponseFormat, pszSOSGetObservationMimeType);
        return msSOSException(map, "responseformat", "InvalidParameterValue");
    }

    /*validate if offering exists*/
    for (i=0; i<map->numlayers; i++)
    {
        pszTmp = msOWSLookupMetadata(&(map->layers[i].metadata), "S", "offering_id");
        if (pszTmp && (strcasecmp(pszTmp, pszOffering) == 0))
          break;
    }


    if (i==map->numlayers)
    {
        msSetError(MS_SOSERR, "Offering %s not found.",
                   "msSOSGetObservation()", pszOffering);
        return msSOSException(map, "offering", "InvalidParameterValue");
    }

    /*validate if observed property exist*/
    /* Allow more the 1 oberved property comma separated (specs is unclear on it). If we
      do it, we need to see if other parameters like result (filter encoding)
      should be given for each property too) */

    bLayerFound = 0;
    tokens = split(pszProperty, ',', &n);
    
    for (i=0; i<map->numlayers; i++)
    {
        pszTmp = msOWSLookupMetadata(&(map->layers[i].metadata), "S", "offering_id");
        pszTmp2 = msOWSLookupMetadata(&(map->layers[i].metadata), "S", 
                                      "observedproperty_id");

        map->layers[i].status = MS_OFF;
        
        if (pszTmp && pszTmp2)
        {
            if (strcasecmp(pszTmp, pszOffering) == 0)
            {   
                if (tokens && n > 0)
                {
                    for (j=0; j<n; j++)
                    {
                        if(strcasecmp(pszTmp2, tokens[j]) == 0)
                        {
                            map->layers[i].status = MS_ON;
                            /* Force setting a template to enable query. */
                            if (!map->layers[i].template)
                              map->layers[i].template = strdup("ttt.html");
                            bLayerFound = 1;
                            break;
                        }
                    }
                }                 
            }
        }
    }
    if (tokens && n > 0)
       msFreeCharArray(tokens, n);


    if (bLayerFound == 0)
    {
        msSetError(MS_SOSERR, "ObservedProperty %s not found.",
                   "msSOSGetObservation()", pszProperty);
        return msSOSException(map, "observedproperty", "InvalidParameterValue");
    }
     
    /*apply procedure : could be a comma separated list.
      set status to on those layers that have the sos_procedure metadata
     equals to this parameter. Note that the layer should already have it's status at ON
     by the  offering,observedproperty filter done above */
    if (pszProdedure)
    {
        tokens = split(pszProdedure, ',', &n);
        
        if (tokens && n > 0)
        {
            for (i=0; i<map->numlayers; i++)
            {
                if(map->layers[i].status == MS_ON)
                {
                    pszValue =  msOWSLookupMetadata(&(map->layers[i].metadata), "S",
                                                    "procedure");
                    
                    if (pszValue)
                    {
                        /* the procedure metadata can be a list "sensor1 sensor2..."*/
                        tokens1 = split(pszValue, ' ', &n1);
                        
                        for (j=0; j<n; j++)
                        {
                            for (k=0; k<n1; k++)
                            {
                                if (strcasecmp(tokens1[k], tokens[j]) == 0)
                                  break;
                            }
                            if (k<n1)
                              break;
                        }
                        if (j == n) /*not found*/
                          map->layers[i].status = MS_OFF;
                        else
                        {
                            pszProcedureItem =  msOWSLookupMetadata(&(map->layers[i].metadata), "S",
                                                                    "procedure_item");
                            if (pszProcedureItem)
                            {
                                lp = & map->layers[i];
                                if (&lp->filter)
                                {
                                    if (lp->filter.string && strlen(lp->filter.string) > 0)
                                      pszBuffer = strcatalloc(pszBuffer, lp->filter.string);
                                    freeExpression(&lp->filter);
                                } 
                                pszBuffer = strcatalloc(pszBuffer, " (");
                                for (j=0; j<n; j++)
                                {
                                    if (j > 0)
                                   pszBuffer = strcatalloc(pszBuffer, " OR ");
                                    pszBuffer = strcatalloc(pszBuffer, "(");
                                    pszBuffer = strcatalloc(pszBuffer, (char *)pszProcedureItem);
                                    pszBuffer = strcatalloc(pszBuffer, " = '");
                                    pszBuffer = strcatalloc(pszBuffer,  tokens[j]);
                                    pszBuffer = strcatalloc(pszBuffer,  "')");
                                }
                                pszBuffer = strcatalloc(pszBuffer, ")");
                                loadExpressionString(&lp->filter, pszBuffer);
                                if (pszBuffer)
                                  msFree(pszBuffer);
                            }
                        }

                        msFreeCharArray(tokens1, n1);
                    }
                    else 
                    {
                         pszValue =  msOWSLookupMetadata(&(map->layers[i].metadata), "S",
                                                         "procedure_item");
                         if (!pszValue)
                         {
                             map->layers[i].status = MS_OFF;
                         }
                         else
                         {
                             lp = & map->layers[i];
                             /*
                             if (&lp->filter && lp->filter.type == MS_EXPRESSION)
                             {
                                 pszBuffer = strcatalloc(pszBuffer, "((");
                                 pszBuffer = strcatalloc(pszBuffer, lp->filter.string);
                                 pszBuffer = strcatalloc(pszBuffer, ") and ");
                             }
                             else
                              freeExpression(&lp->filter); 
                             */
                             if (&lp->filter)
                               freeExpression(&lp->filter); 
                             pszBuffer = strcatalloc(pszBuffer, "(");
                             for (j=0; j<n; j++)
                             {
                                 if (j > 0)
                                   pszBuffer = strcatalloc(pszBuffer, " OR ");
                                 pszBuffer = strcatalloc(pszBuffer, "(");
                                 pszBuffer = strcatalloc(pszBuffer, (char *)pszValue);
                                 pszBuffer = strcatalloc(pszBuffer, " = '");
                                 pszBuffer = strcatalloc(pszBuffer,  tokens[j]);
                                 pszBuffer = strcatalloc(pszBuffer,  "')");
                             }
                             pszBuffer = strcatalloc(pszBuffer, ")");
                             loadExpressionString(&lp->filter, pszBuffer);
                             if (pszBuffer)
                               msFree(pszBuffer);
                         }
                    }
                }       
            }
            
            msFreeCharArray(tokens, n);
        }
    }
              
/* -------------------------------------------------------------------- */
/*      supports 2 types of gml:Time : TimePeriod and TimeInstant :     */
/*      - <gml:TimePeriod>                                              */
/*          <gml:beginPosition>2005-09-01T11:54:32</gml:beginPosition>  */
/*         <gml:endPosition>2005-09-02T14:54:32</gml:endPosition>       */
/*       </gml:TimePeriod>                                              */
/*                                                                      */
/*      - <gml:TimeInstant>                                             */
/*           <gml:timePosition>2003-02-13T12:28-08:00</gml:timePosition>*/
/*         </gml:TimeInstant>                                           */
/*                                                                      */
/*       The user can specify mutilple times separated by commas.       */
/*                                                                      */
/*       The gml will be parsed and trasformed into a sting tah         */
/*      looks like timestart/timeend,...                                */
/* -------------------------------------------------------------------- */


    /*apply time filter if available */
    if (pszTime)
    {
        char **apszTimes = NULL;
        int numtimes = 0;
        char *pszTimeString = NULL, *pszTmp = NULL;

        apszTimes = split (pszTime, ',', &numtimes);
        if (numtimes >=1)
        {
            for (i=0; i<numtimes; i++)
            {
                pszTmp = msSOSParseTimeGML(apszTimes[i]);
                if (pszTmp)
                {
                    if (pszTimeString)
                      pszTimeString = strcatalloc(pszTimeString, ",");
                    pszTimeString = strcatalloc(pszTimeString, pszTmp);
                    msFree(pszTmp);
                }
            }
            msFreeCharArray(apszTimes, numtimes);
        }
        if (!pszTimeString)
        {
            msSetError(MS_SOSERR, "Invalid time value given for the eventTime parameter",
                   "msSOSGetObservation()", pszProperty);
            return msSOSException(map, "eventtime", "InvalidParameterValue");
        }
        for (i=0; i<map->numlayers; i++)
        {
            if (map->layers[i].status == MS_ON)
            {
                /* the sos_offering_timeextent should be used for time validation*/
                /*TODO : too documented  ?*/
                lpfirst = 
                  msSOSGetFirstLayerForOffering(map, 
                                                msOWSLookupMetadata(&(map->layers[i].metadata), "S", 
                                                                    "offering_id"),
                                                NULL);
                if (lpfirst)
                  pszTimeExtent = 
                    msOWSLookupMetadata(&lpfirst->metadata, "S", "offering_timeextent");

                pszTimeField =  msOWSLookupMetadata(&(map->layers[i].metadata), "SO",
                                                    "timeitem");

            if (pszTimeField)
              {
                  /*validate only if time extent is set.*/
                  if (pszTimeExtent)
                  {
                      if (msValidateTimeValue(pszTimeString, pszTimeExtent) == MS_TRUE)
                        msLayerSetTimeFilter(&(map->layers[i]), pszTimeString, 
                                             pszTimeField);
                  }
                  else
                    msLayerSetTimeFilter(&(map->layers[i]), pszTimeString, 
                                         pszTimeField);
                }
            }
        }
        if (pszTimeString)
          msFree(pszTimeString);
    }
    /* apply filter */
    if (pszFilter)
    {
        //TODO : preparse parser so that alias for fields can be used
        
        psFilterNode = FLTParseFilterEncoding(pszFilter);
	
	if (!psFilterNode) {
	  msSetError(MS_SOSERR, 
		     "Invalid or Unsupported FILTER in GetObservation", 
		     "msSOSGetObservation()");
	  return msSOSException(map, "filter", "InvalidParameterValue");
	}
        /* apply the filter to all layers thar are on*/
        for (i=0; i<map->numlayers; i++)
        {
            if (map->layers[i].status == MS_ON)
              FLTApplyFilterToLayer(psFilterNode, map, i, MS_FALSE);
        }
    }
 

    /*bbox*/
    /* this is a gml feature
- <gml:Envelope xmlns:gml="http://www.opengis.net/gml">
  <gml:lowerCorner srsName="EPSG:4326">-66 43</gml:lowerCorner> 
  <upperCorner srsName="EPSG:4326">-62 45</upperCorner> 
  </gml:Envelope>
*/

    if (pszFeature)
    {
        CPLXMLNode *psRoot=NULL, *psChild=NULL; 
        CPLXMLNode *psUpperCorner=NULL, *psLowerCorner=NULL;
        char *pszLowerCorner=NULL, *pszUpperCorner=NULL;
        int bValid = 0;
         char **tokens;
        int n;

        psRoot = CPLParseXMLString(pszFeature);
        if(!psRoot)
        {       
            msSetError(MS_SOSERR, "Invalid gml:Envelop value given for featureOfInterest .", 
                       "msSOSGetObservation()");
            return msSOSException(map, "featureofinterest", "InvalidParameterValue");
        }

        CPLStripXMLNamespace(psRoot, "gml", 1);
        bValid = 0;
        if (psRoot->eType == CXT_Element && 
            EQUAL(psRoot->pszValue,"Envelope"))
        {
            psLowerCorner = psRoot->psChild;
            if (psLowerCorner)
              psUpperCorner=  psLowerCorner->psNext;

            if (psLowerCorner && psUpperCorner && 
                EQUAL(psLowerCorner->pszValue,"lowerCorner") &&
                EQUAL(psUpperCorner->pszValue,"upperCorner"))
            {
                /*get the values*/
                psChild = psLowerCorner->psChild;
                while (psChild != NULL)
                {
                    if (psChild->eType != CXT_Text)
                      psChild = psChild->psNext;
                    else
                      break;
                }
                if (psChild && psChild->eType == CXT_Text)
                  pszLowerCorner = psChild->pszValue;

                psChild = psUpperCorner->psChild;
                while (psChild != NULL)
                {
                    if (psChild->eType != CXT_Text)
                      psChild = psChild->psNext;
                    else
                      break;
                }
                if (psChild && psChild->eType == CXT_Text)
                  pszUpperCorner = psChild->pszValue;

                if (pszLowerCorner && pszUpperCorner)
                {
                    tokens = split(pszLowerCorner, ' ', &n);
                    if (tokens && n == 2)
                    {
                        sBbox.minx = atof(tokens[0]);
                        sBbox.miny = atof(tokens[1]);

                         msFreeCharArray(tokens, n);

                         tokens = split(pszUpperCorner, ' ', &n);
                         if (tokens && n == 2)
                         {
                             sBbox.maxx = atof(tokens[0]);
                             sBbox.maxy = atof(tokens[1]);
                             msFreeCharArray(tokens, n);

                             bValid = 1;
                         }
                    }
                }
                    
            }
            
        }

        if (!bValid)
        {
            msSetError(MS_SOSERR, "Invalid gml:Envelope value given for featureOfInterest .", "msSOSGetObservation()");
            return msSOSException(map, "featureofinterest", "InvalidParameterValue");
        }
    }


    /* this is just a fall back if bbox is enetered. The bbox parameter is not supported
       by the sos specs */
    if (pszBbox && !pszFeature)
    {
        char **tokens;
        int n;


        tokens = split(pszBbox, ',', &n);
        if (tokens==NULL || n != 4) 
        {
            msSetError(MS_SOSERR, "Wrong number of arguments for bounding box.", "msSOSGetObservation()");
            return msSOSException(map, "bbox", "InvalidParameterValue");
        }
        sBbox.minx = atof(tokens[0]);
        sBbox.miny = atof(tokens[1]);
        sBbox.maxx = atof(tokens[2]);
        sBbox.maxy = atof(tokens[3]);
        msFreeCharArray(tokens, n);
    }



    /*do the query. use the same logic (?) as wfs. bbox and filer are incomaptible since bbox
     can be given inside a filter*/
    if (!pszFilter) 
    {
        msQueryByRect(map, -1, sBbox);
        
    }

    /*get the first layers of the offering*/
    for (i=0; i<map->numlayers; i++)
    {
        pszTmp = msOWSLookupMetadata(&(map->layers[i].metadata), "S", "offering_id");
        if (pszTmp && (strcasecmp(pszTmp, pszOffering) == 0))
        {
            lp = &(map->layers[i]);
            break;
        }
    }
    
    
    /* build xml return tree*/
    psDoc = xmlNewDoc(BAD_CAST "1.0");
    psRootNode = xmlNewNode(NULL, BAD_CAST "ObservationCollection");
    xmlDocSetRootElement(psDoc, psRootNode);
    xmlSetNs(psRootNode,  xmlNewNs(psRootNode, BAD_CAST "http://www.opengis.net/gml", BAD_CAST "gml"));
    xmlSetNs(psRootNode,  xmlNewNs(psRootNode, BAD_CAST "http://www.opengis.net/ows", BAD_CAST "ows"));
    xmlSetNs(psRootNode,  xmlNewNs(psRootNode, BAD_CAST "http://www.opengis.net/swe", BAD_CAST "swe"));
    xmlSetNs(psRootNode,  xmlNewNs(psRootNode, BAD_CAST "http://www.w3.org/1999/xlink", BAD_CAST "xlink"));
    xmlSetNs(psRootNode,  xmlNewNs(psRootNode, BAD_CAST "http://www.w3.org/2001/XMLSchema-instance", BAD_CAST "xsi"));
    xmlSetNs(psRootNode,   xmlNewNs(psRootNode, BAD_CAST "http://www.opengis.net/sos", BAD_CAST "sos"));
    xmlSetNs(psRootNode,  xmlNewNs(psRootNode, BAD_CAST "http://www.opengis.net/om", BAD_CAST "om"));
 
    xmlNewNsProp(psRootNode,  xmlNewNs(NULL, BAD_CAST "http://www.opengis.net/gml", BAD_CAST "gml"),
                 BAD_CAST "id", BAD_CAST pszOffering);

    /*schema fixed*/
    schemalocation = msEncodeHTMLEntities( msOWSGetSchemasLocation(map) );
    /*TODO : review this*/
    dtd_url = strdup("http://www.opengis.net/om ");
    dtd_url = strcatalloc(dtd_url, schemalocation);
    dtd_url = strcatalloc(dtd_url, "/0.14.7/om.xsd");
    xmlNewNsProp(psRootNode, NULL, BAD_CAST "xsi:schemaLocation", BAD_CAST dtd_url);


    /*name */
    pszTmp = msOWSLookupMetadata(&(lp->metadata), "S", "offering_name");
    if (pszTmp)
    {
        psNode = xmlNewChild(psRootNode, NULL, BAD_CAST "name", BAD_CAST pszTmp);
        xmlSetNs(psNode, xmlNewNs(psNode, BAD_CAST "http://www.opengis.net/gml", BAD_CAST "gml"));
    }

    /*time*/
    pszTmp = msOWSLookupMetadata(&(lp->metadata), "S","offering_timeextent");
    if (pszTmp)
    {
        char **tokens;
        int n;
        char *pszEndTime = NULL;
        tokens = split(pszTmp, '/', &n);
        if (tokens==NULL || (n != 1 && n!=2)) {
            msSetError(MS_WMSERR, "Wrong number of arguments for offering_timeextent.",
                       "msSOSGetCapabilities()");
            return msSOSException(map, "offering_timeextent", "InvalidParameterValue");
        }

        if (n == 2) /* end time is empty. It is going to be set as "now*/
          pszEndTime = tokens[1];

        msSOSAddTimeNode(psRootNode, tokens[0], pszEndTime, psNsGml);
        msFreeCharArray(tokens, n);
                     
    }

    /* output result members */
    for (i=0; i<map->numlayers; i++)
    {
        if (map->layers[i].resultcache && map->layers[i].resultcache->numresults > 0)
        {       
            if(msLayerOpen(&(map->layers[i])) == MS_SUCCESS)
            {
                msLayerGetItems(&(map->layers[i]));
                for(j=0; j<map->layers[i].resultcache->numresults; j++) 
                {
                    msSOSAddMemberNode(psRootNode, map, &(map->layers[i]), j);
                }
                msLayerClose(&(map->layers[i]));
            }
        }
    }


    /* output results */    
     msIO_printf("Content-type: text/xml%c%c",10,10);
     stream = stdout;

     xmlDocDump(stream, psDoc);

    /*free  document */
     xmlFreeDoc(psDoc);
     /*
     *Free the global variables that may
     *have been allocated by the parser.
     */
     xmlCleanupParser();
     

    return(MS_SUCCESS);
}


/************************************************************************/
/*                           msSOSDescribeSensor                        */
/*                                                                      */
/*      Describe sensor request handler.                               */
/************************************************************************/
int msSOSDescribeSensor(mapObj *map, int nVersion, char **names,
                        char **values, int numentries)

{
    char *pszVersion=NULL;
    char *pszSensorId=NULL;
    char *pszOutputFormat=NULL;
    char *pszEncodedUrl = NULL;
    const char *pszId = NULL, *pszUrl = NULL;
    int i = 0, j=0, k=0;
    layerObj *lp = NULL;
    int iItemPosition = -1;
    shapeObj sShape;
    int status;
    char *tmpstr = NULL, *pszTmp = NULL;

    for(i=0; i<numentries; i++) 
    {
        if (strcasecmp(names[i], "VERSION") == 0) {
          pszVersion = values[i];
        }
        if (strcasecmp(names[i], "SENSORID") == 0) {
          pszSensorId = values[i];
        }
        if (strcasecmp(names[i], "OUTPUTFORMAT") == 0) {
          pszOutputFormat = values[i];
        }
    }

    if (!pszVersion)
    {
        msSetError(MS_SOSERR, "Missing mandatory parameter version.",
                   "msSOSDescribeSensor()");
        return msSOSException(map, "version", "MissingParameterValue");
    }

    if (!pszSensorId)
    {
        msSetError(MS_SOSERR, "Missing mandatory parameter sensorid.",
                   "msSOSDescribeSensor()");
        return msSOSException(map, "sensorid", "MissingParameterValue");
    }

    if (!pszOutputFormat)
    {
        msSetError(MS_SOSERR, "Missing mandatory parameter outputFormat.",
                   "msSOSDescribeSensor()");
        return msSOSException(map, "outputformat", "MissingParameterValue");
    }

    if (strcasecmp(pszOutputFormat, pszSOSDescribeSensorMimeType) != 0) {
        msSetError(MS_SOSERR, "Invalid outputformat parameter %s.  Allowable values are: %s",
                   "msSOSDescribeSensor()", pszOutputFormat, pszSOSDescribeSensorMimeType);
        return msSOSException(map, "outputformat", "InvalidParameterValue");
    }
 
    for (i=0; i<map->numlayers; i++)
    {
        lp = &map->layers[i];
        pszId = msOWSLookupMetadata(&(lp->metadata), "S", "procedure");
        if (pszId && strlen(pszId) > 0)
        {
            /*procdedure could be a list*/
            char **tokens = NULL;
            int n=0;
            int bFound = 0;
            tokens = split(pszId, ' ', &n);
            for (k=0; k<n; k++)
            {
                if (tokens[k] && strlen(tokens[k]) > 0 &&
                    strcasecmp(tokens[k], pszSensorId) == 0)
                {
                    bFound = 1; 
                    break;
                }
            }
            if (bFound)
            {
                pszUrl = msOWSLookupMetadata(&(lp->metadata), "S", "describesensor_url");
                
                if (pszUrl)
                {
                    pszTmp = strdup(pszUrl);
                    for(k=0; k<numentries; k++) 
                    {
                        tmpstr = (char *)malloc(sizeof(char)*strlen(names[k]) + 3);
                        sprintf(tmpstr,"%%%s%%", names[k]);
                        if (stristr(pszUrl, tmpstr) != NULL)
                        {
                            pszTmp = gisub(pszTmp, tmpstr, values[k]);
                            break;
                        }
                        msFree(tmpstr);
                    }
                    pszEncodedUrl = msEncodeHTMLEntities(pszTmp); 
                    msIO_printf("Location: %s\n\n", pszEncodedUrl);
                    msFree(pszTmp);
                    return(MS_SUCCESS);
                }
                else
                {
                    msSetError(MS_SOSERR, "Missing mandatory metadata sos_describesensor_url on layer %s",
                               "msSOSDescribeSensor()", lp->name);
                    return msSOSException(map, "sos_describesensor_url", "MissingValue");
                }
            }
        }
        else if ((pszId = msOWSLookupMetadata(&(lp->metadata), "S", "procedure_item")))
        {   
            iItemPosition = -1;
            if (msLayerOpen(lp) == MS_SUCCESS && 
                msLayerGetItems(lp) == MS_SUCCESS)
            {
                for(j=0; j<lp->numitems; j++) 
                {
                    if (strcasecmp(lp->items[j], pszId) == 0)
                    {
                        iItemPosition = j;
                        break;
                    }
                }
                msLayerClose(lp);
            }
            if (iItemPosition >=0)
            {

                if (lp->template == NULL)
                  lp->template = strdup("ttt");
                msQueryByRect(map, i, map->extent);
                
                msLayerOpen(lp);
                msLayerGetItems(lp);
                
                if (lp->resultcache && lp->resultcache->numresults > 0)
                {
                    for(j=0; j<lp->resultcache->numresults; j++)
                    {      
                        msInitShape(&sShape);     
                        status = msLayerGetShape(lp, &sShape, 
                                                 lp->resultcache->results[j].tileindex, 
                                                 lp->resultcache->results[j].shapeindex);
                        if(status != MS_SUCCESS) 
                          continue;

                        if (sShape.values[iItemPosition] && 
                            strcasecmp(sShape.values[iItemPosition], pszSensorId) == 0)
                        {
                            pszUrl = msOWSLookupMetadata(&(lp->metadata), "S", "describesensor_url");
                            if (pszUrl)
                            {   
                                pszTmp = strdup(pszUrl);
                                for(k=0; k<numentries; k++) 
                                {
                                    tmpstr = (char *)malloc(sizeof(char)*strlen(names[k]) + 3);
                                    sprintf(tmpstr,"%%%s%%", names[k]);
                                    if (stristr(pszUrl, tmpstr) != NULL)
                                    {
                                        pszTmp = gisub(pszTmp, tmpstr, values[k]);
                                        break;
                                    }
                                    msFree(tmpstr);
                                }
                                pszEncodedUrl = msEncodeHTMLEntities(pszTmp); 
                                msIO_printf("Location: %s\n\n", pszEncodedUrl);
                                msFree(pszTmp);
                                return(MS_SUCCESS);
                            }
                            else
                            {
                                msSetError(MS_SOSERR, "Missing mandatory metadata sos_describesensor_url on layer %s",
                                           "msSOSDescribeSensor()", lp->name);
                                return msSOSException(map, "sos_describesensor_url", "MissingValue");
                            }
                        }
                    }
                }
                msLayerClose(lp);
            }
            
        }
    }

     msSetError(MS_SOSERR, "Sensor not found.",
                   "msSOSDescribeSensor()");
     return msSOSException(map, "sensorid", "InvalidParameterValue");
    
}


#endif /* USE_SOS_SVR*/

/*
** msSOSDispatch() is the entry point for SOS requests.
** - If this is a valid request then it is processed and MS_SUCCESS is returned
**   on success, or MS_FAILURE on failure.
*/
int msSOSDispatch(mapObj *map, cgiRequestObj *req)
{
#ifdef USE_SOS_SVR
    int i,  nVersion=-1;
    static char *request=NULL, *service=NULL;


     for(i=0; i<req->NumParams; i++) 
     {
         if (strcasecmp(req->ParamNames[i], "SERVICE") == 0)
           service = req->ParamValues[i];
         else if (strcasecmp(req->ParamNames[i], "REQUEST") == 0)
           request = req->ParamValues[i];
     }

     /* SERVICE must be specified and be SOS */
     if (service == NULL || request == NULL || 
         strcasecmp(service, "SOS") != 0)
       return MS_DONE;  /* Not a SOS request */

     if (strcasecmp(request, "GetCapabilities") == 0)
       return  msSOSGetCapabilities(map, nVersion, req);
     else if (strcasecmp(request, "GetObservation") == 0)
       return  msSOSGetObservation(map, nVersion, req->ParamNames, 
                                   req->ParamValues, req->NumParams);
     else if (strcasecmp(request, "DescribeSensor") == 0)
       return  msSOSDescribeSensor(map, nVersion, req->ParamNames, 
                                   req->ParamValues, req->NumParams);
     else
       return MS_DONE;  /* Not an SOS request */

#else
  msSetError(MS_SOSERR, "SOS support is not available.", "msWMSDispatch()");
  return(MS_FAILURE);

#endif

}

