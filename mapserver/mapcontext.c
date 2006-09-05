/**********************************************************************
 * $Id$
 *
 * Name:     mapcontext.c
 * Project:  MapServer
 * Language: C
 * Purpose:  OGC Web Map Context implementation
 * Author:   Julien-Samuel Lacroix, DM Solutions Group (lacroix@dmsolutions.ca)
 *
 **********************************************************************
 * Copyright (c) 2002-2003, Julien-Samuel Lacroix, DM Solutions Group Inc
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
 *
 * $Log$
 * Revision 1.78  2006/09/05 13:49:42  julien
 * WMC true/false bool and use format when formatlist not avail. bug 1723,1692
 *
 * Revision 1.77  2006/06/15 14:58:24  julien
 * Add SLD xsd and 1.1.0 reference in the root element
 *
 * Revision 1.76  2006/06/14 18:13:39  julien
 * Support WMC Min/Max scale in write mode. bug 1581
 *
 * Revision 1.75  2006/03/10 15:30:15  julien
 * Set the wms_time metadata when we have the time dimension in context1.1
 *
 * Revision 1.74  2006/03/09 21:08:54  julien
 * Remove XML header tag check
 *
 * Revision 1.73  2006/02/14 03:53:04  julien
 * Change layer server type for 1.1.0 version
 *
 * Revision 1.72  2006/02/14 03:38:47  julien
 * Update to MapContext 1.1.0, add dimensions support in context bug 1581
 *
 * Revision 1.71  2006/02/09 16:57:14  julien
 * Support SLD_BODY in Web Map Context
 *
 * Revision 1.70  2005/02/18 03:06:45  dan
 * Turned all C++ (//) comments into C comments (bug 1238)
 *
 * Revision 1.69  2004/11/16 21:57:49  dan
 * Final pass at updating WMS/WFS client/server interfaces to lookup "ows_*"
 * metadata in addition to default "wms_*"/"wfs_*" metadata (bug 568)
 *
 * Revision 1.68  2004/11/10 20:55:40  assefa
 * Do not output <StyleList> if the metadata wms_stylelist is an empty
 * string (Bug 595).
 *
 * Revision 1.67  2004/11/02 21:01:00  assefa
 * Add a 2nd optional argument to msLoadMapContext function (Bug 1023).
 *
 * Revision 1.66  2004/10/29 22:48:03  assefa
 * Use of metadata ows_schema_location (Bug 1013).
 *
 * Revision 1.65  2004/10/25 17:30:38  julien
 * Print function for OGC URLs components. msOWSPrintURLType() (Bug 944)
 *
 * Revision 1.64  2004/10/21 04:30:55  frank
 * Added standardized headers.  Added MS_CVSID().
 *
 * Revision 1.63  2004/10/15 20:29:03  assefa
 * Add support for OGC mapcontext through mapserver cgi : Bug 946.
 *
 * Revision 1.62  2004/10/01 21:26:55  frank
 * Use msIO_ API.
 *
 * Revision 1.61  2004/09/30 13:29:56  julien
 * Fix a typo in Format encoding that print all formats in each tags.
 *
 * Revision 1.60  2004/09/23 19:18:10  julien
 * Encode all metadata and parameter printed in an XML document (Bug 802)
 *
 * Revision 1.59  2004/09/20 12:31:08  julien
 * Output parameters (SRS and DataURL) in order required by the spec. Bug 863
 *
 * Revision 1.58  2004/09/06 16:06:43  julien
 * Cleanup code to separate parsing into different functions.
 *
 * Revision 1.57  2004/08/03 23:26:24  dan
 * Cleanup OWS version tests in the code, mapwms.c (bug 799)
 *
 * Revision 1.56  2004/08/03 22:12:34  dan
 * Cleanup OWS version tests in the code, started with mapcontext.c (bug 799)
 *
 * Revision 1.55  2004/06/22 20:55:20  sean
 * Towards resolving issue 737 changed hashTableObj to a structure which contains a hashObj **items.  Changed all hash table access functions to operate on the target table by reference.  msFreeHashTable should not be used on the hashTableObj type members of mapserver structures, use msFreeHashItems instead.
 *
 * Revision 1.54  2004/04/16 19:12:31  assefa
 * Correct bug on windows when opening xml file (open it in binary mode).
 *
 * Revision 1.53  2004/04/14 05:14:54  dan
 * Added ability to pass a default value to msOWSPrintMetadataList() (bug 616)
 *
 * Revision 1.52  2004/04/14 04:54:30  dan
 * Created msOWSLookupMetadata() and added namespaces lookup in all
 * msOWSPrint*Metadata() functions. Also pass namespaces=NULL everywhere
 * that calls those functions for now to avoid breaking something just
 * before the release. (bug 615, 568)
 *
 * Revision 1.51  2003/12/23 20:40:38  julien
 * Replace legendurl, logourl, descriptionurl, dataurl and metadataurl metadata
 * by four new metadata by metadata replaced. The new metadata are called
 * legendurl_width, legendurl_height, legendurl_format, legendurl_href,
 * logourl_width, etc...
 * Old dependancy to the metadata with four value, space separated, are kept.
 *
 * Revision 1.50  2003/12/22 17:00:21  julien
 * Implement DataURL, MetadataURL and DescriptionURL (Bug 523)
 *
 * Revision 1.49  2003/07/31 16:10:34  dan
 * Enable map context stuff only if USE_OGR is set (cpl_minixml dependency)
 *
 * Revision 1.48  2003/07/15 15:22:23  assefa
 * Modify schema location url.
 *
 * Revision 1.47  2003/07/15 14:07:07  assefa
 * replace View_context by ViewContext for 1.0. support.
 *
 * Revision 1.46  2003/07/11 15:43:20  dan
 * Try to pick a supported format when current format is not supported
 *
 * Revision 1.45  2003/06/26 12:43:14  assefa
 * typo : replace printf by fprintf.
 *
 * Revision 1.44  2003/06/26 02:49:47  assefa
 * Add support for version 1.0.0
 *
 * Revision 1.43  2003/04/09 07:13:49  dan
 * Added GetContext (custom) request in WMS interface.
 * Added missing gml: namespace in 0.1.7 context output.
 *
 * Revision 1.42  2003/03/07 21:22:50  julien
 * Fix a typo in ContactFacsimileTelephone
 *
 * Revision 1.41  2003/02/21 19:19:49  julien
 * Do not put 'init=' before the srs to proj when it begin by 'AUTO:'
 *
 * Revision 1.40  2003/02/04 14:33:18  julien
 * Fix the closing tag of View_Context
 *
 * Revision 1.39  2003/01/30 22:46:32  julien
 * mv context_* metadata to wms_context_*
 *
 * Revision 1.38  2003/01/30 22:43:29  julien
 * Remove logourl heritage and customize encoding
 *
 * Revision 1.37  2003/01/30 21:17:03  julien
 * Implement the version 0.1.7
 *
 * Revision 1.36  2002/12/20 20:21:13  julien
 * wms_style__title is now set correctly
 *
 * Revision 1.35  2002/12/19 19:26:11  julien
 * Don't set the projection for each layer
 *
 * Revision 1.34  2002/12/11 18:10:39  julien
 * Remove possible WARNING inside other tags
 *
 * Revision 1.33  2002/11/29 19:28:17  julien
 * Replace ' ' by ',' in stylelist and formatlist srs
 *
 * Revision 1.32  2002/11/27 21:00:44  julien
 * Fatal error if server version is missing in load function
 *
 * Revision 1.31  2002/11/27 20:14:19  julien
 * Use the map srs if no layer srs is specify
 *
 * Revision 1.30  2002/11/26 01:37:55  dan
 * Fixed compile warnings
 *
 * Revision 1.29  2002/11/25 21:48:07  dan
 * Set map units after setting new projections in msLoadMapContext()
 *
 * Revision 1.28  2002/11/25 14:48:10  julien
 * One SRS tag with multiple SRS elements space separated
 *
 * Revision 1.27  2002/11/22 21:50:33  julien
 * Fix SRS and LegendURL for 0.1.2
 *
 * Revision 1.26  2002/11/22 17:42:52  julien
 * Support DataURL and LogoURL for 0.1.2 version
 *
 * Revision 1.25  2002/11/22 15:12:51  julien
 * Fix the seg fault temporaly fixed on 2002/11/21 17:07:34
 *
 * Revision 1.24  2002/11/21 20:39:40  julien
 * Support the wms_srs metadata and support multiple SRS tag
 *
 * Revision 1.23  2002/11/21 17:07:34  julien
 * temporaly fix a seg. fault with pszSLD2
 *
 * Revision 1.22  2002/11/21 15:54:46  julien
 * Valid empty Format and style, some chage to 0.1.2 version
 *
 * Revision 1.21  2002/11/20 23:57:55  julien
 * Remove duplicated code of style and format and create a wms_name
 *
 * Revision 1.20  2002/11/20 22:17:09  julien
 * Replace fatal error by msDebug
 *
 * Revision 1.19  2002/11/20 21:25:35  dan
 * Duh! Forgot to set the proper path for the contexts/0.1.4/context.xsd
 *
 * Revision 1.18  2002/11/20 21:22:32  dan
 * Added msOWSGetSchemasLocation() for use by both WFS and WMS Map Context
 *
 * Revision 1.17  2002/11/20 19:08:55  julien
 * Support onlineResource of version 0.1.2
 *
 * Revision 1.16  2002/11/20 17:17:21  julien
 * Support version 0.1.2 of MapContext
 * Remove warning from tags
 * Encode and decode all url
 *
 * Revision 1.15  2002/11/15 18:53:10  assefa
 * Correct test on fread cuasing problems on Windows.
 *
 * Revision 1.14  2002/11/14 18:46:14  julien
 * Include the ifdef to compile without the USE_WMS_LYR tag
 *
 * Revision 1.13  2002/11/13 16:54:23  julien
 * Change the search of the header to be flexible.
 *
 * Revision 1.12  2002/11/07 21:50:19  julien
 * Set the layer type to RASTER
 *
 * Revision 1.11  2002/11/07 21:16:45  julien
 * Fix warning in ContactInfo
 *
 * Revision 1.10  2002/11/07 15:53:14  julien
 * Put duplicated code in a single function
 * Fix many typo error
 *
 * Revision 1.9  2002/11/05 21:56:13  julien
 * Remove fatal write mistake in msSaveMapContext
 *
 * Revision 1.8  2002/11/04 20:39:17  julien
 * Change a validation to prevent a crash
 *
 * Revision 1.6  2002/11/04 20:16:09  julien
 * Change a validation to prevent a crash
 *
 * Revision 1.5  2002/10/31 21:25:55  julien
 * transform EPSG:*** to init=epsg:***
 *
 * Revision 1.4  2002/10/31 20:00:07  julien
 * transform EPSG:*** to init=epsg:***
 *
 * Revision 1.3  2002/10/31 18:57:35  sacha
 * Fill layerorder and layer.index in msLoadMapContext
 *
 * Revision 1.2  2002/10/28 22:31:09  dan
 * Added map arg to initLayer() call
 *
 * Revision 1.1  2002/10/28 20:31:20  dan
 * New support for WMS Map Context (from Julien)
 *
 * Revision 1.1  2002/10/22 20:03:57  julien
 * Add the mapcontext support
 *
 **********************************************************************/

#include "map.h"

MS_CVSID("$Id$")

#if defined(USE_WMS_LYR) && defined(USE_OGR)

/* There is a dependency to GDAL/OGR for the GML driver and MiniXML parser */
#include "cpl_minixml.h"

#endif

/* msGetMapContextFileText()
**
** Read a file and return is content
**
** Take the filename in argument
** Return value must be freed by caller
*/
char * msGetMapContextFileText(char *filename)
{
  char *pszBuffer;
  FILE *stream;
  int	 nLength;
 
  /* open file */
  if(filename != NULL && strlen(filename) > 0) {
      stream = fopen(filename, "rb");
      if(!stream) {
          msSetError(MS_IOERR, "(%s)", "msGetMapContextFileText()", filename);
          return NULL;
      }
  }
  else
  {
      msSetError(MS_IOERR, "(%s)", "msGetMapContextFileText()", filename);
      return NULL;
  }

  fseek( stream, 0, SEEK_END );
  nLength = ftell( stream );
  fseek( stream, 0, SEEK_SET );

  pszBuffer = (char *) malloc(nLength+1);
  if( pszBuffer == NULL )
  {
      msSetError(MS_MEMERR, "(%s)", "msGetMapContextFileText()", filename);
      fclose( stream );
      return NULL;
  }
  
  if(fread( pszBuffer, nLength, 1, stream ) == 0 &&  !feof(stream))
  {
      free( pszBuffer );
      fclose( stream );
      msSetError(MS_IOERR, "(%s)", "msGetMapContextFileText()", filename);
      return NULL;
  }
  pszBuffer[nLength] = '\0';

  fclose( stream );

  return pszBuffer;
}


#if defined(USE_WMS_LYR) && defined(USE_OGR)

/*
**msGetMapContextXMLHashValue()
**
**Get the xml value and put it in the hash table
**
*/
int msGetMapContextXMLHashValue( CPLXMLNode *psRoot, const char *pszXMLPath, 
                                 hashTableObj *metadata, char *pszMetadata )
{
  char *pszValue;

  pszValue = (char*)CPLGetXMLValue( psRoot, pszXMLPath, NULL);
  if(pszValue != NULL)
  {
      if( metadata != NULL )
      {
          msInsertHashTable(metadata, pszMetadata, pszValue );
      }
      else
      {
          return MS_FAILURE;
      }
  }
  else
  {
      return MS_FAILURE;
  }

  return MS_SUCCESS;
}

/*
**msGetMapContextXMLHashValue()
**
**Get the xml value and put it in the hash table
**
*/
int msGetMapContextXMLHashValueDecode( CPLXMLNode *psRoot, 
                                       const char *pszXMLPath, 
                                       hashTableObj *metadata, 
                                       char *pszMetadata )
{
  char *pszValue;

  pszValue = (char*)CPLGetXMLValue( psRoot, pszXMLPath, NULL);
  if(pszValue != NULL)
  {
      if( metadata != NULL )
      {
          msDecodeHTMLEntities(pszValue);
          msInsertHashTable(metadata, pszMetadata, pszValue );
      }
      else
      {
          return MS_FAILURE;
      }
  }
  else
  {
      return MS_FAILURE;
  }

  return MS_SUCCESS;
}


/*
**msGetMapContextXMLStringValue()
**
**Get the xml value and put it in the string field
**
*/
int msGetMapContextXMLStringValue( CPLXMLNode *psRoot, char *pszXMLPath, 
                                   char **pszField)
{
  char *pszValue;

  pszValue = (char*)CPLGetXMLValue( psRoot, pszXMLPath, NULL);
  if(pszValue != NULL)
  {
      if( pszField != NULL )
      {
           *pszField = strdup(pszValue);
      }
      else
      {
          return MS_FAILURE;
      }
  }
  else
  {
      return MS_FAILURE;
  }

  return MS_SUCCESS;
}


/*
**msGetMapContextXMLStringValue()
**
**Get the xml value and put it in the string field
**
*/
int msGetMapContextXMLStringValueDecode( CPLXMLNode *psRoot, char *pszXMLPath, 
                                         char **pszField)
{
  char *pszValue;

  pszValue = (char*)CPLGetXMLValue( psRoot, pszXMLPath, NULL);
  if(pszValue != NULL)
  {
      if( pszField != NULL )
      {
          msDecodeHTMLEntities(pszValue);
          *pszField = strdup(pszValue);
      }
      else
      {
          return MS_FAILURE;
      }
  }
  else
  {
      return MS_FAILURE;
  }

  return MS_SUCCESS;
}


/*
**msGetMapContextXMLFloatValue()
**
**Get the xml value and put it in the string field
**
*/
int msGetMapContextXMLFloatValue( CPLXMLNode *psRoot, char *pszXMLPath, 
                                        double *pszField)
{
  char *pszValue;

  pszValue = (char*)CPLGetXMLValue( psRoot, pszXMLPath, NULL);
  if(pszValue != NULL)
  {
      if( pszField != NULL )
      {
          *pszField = atof(pszValue);
      }
      else
      {
          return MS_FAILURE;
      }
  }
  else
  {
      return MS_FAILURE;
  }

  return MS_SUCCESS;
}

/*
** msLoadMapContextURLELements
**
** Take a Node and get the width, height, format and href from it.
** Then put this info in metadatas.
*/
int msLoadMapContextURLELements( CPLXMLNode *psRoot, hashTableObj *metadata, 
                                 const char *pszMetadataRoot)
{
  char *pszMetadataName;

  if( psRoot == NULL || metadata == NULL || pszMetadataRoot == NULL )
      return MS_FAILURE;

  pszMetadataName = (char*) malloc( strlen(pszMetadataRoot) + 10 );

  sprintf( pszMetadataName, "%s_width", pszMetadataRoot );
  msGetMapContextXMLHashValue( psRoot, "width", metadata, pszMetadataName );

  sprintf( pszMetadataName, "%s_height", pszMetadataRoot );
  msGetMapContextXMLHashValue( psRoot, "height", metadata, pszMetadataName );

  sprintf( pszMetadataName, "%s_format", pszMetadataRoot );
  msGetMapContextXMLHashValue( psRoot, "format", metadata, pszMetadataName );

  sprintf( pszMetadataName, "%s_href", pszMetadataRoot );
  msGetMapContextXMLHashValue( psRoot, "OnlineResource.xlink:href", metadata, 
                               pszMetadataName );

  free(pszMetadataName);

  return MS_SUCCESS;
}

/* msLoadMapContextKeyword
**
** Put the keywords from a XML node and put them in a metadata.
** psRoot should be set to keywordlist
*/
int msLoadMapContextListInMetadata( CPLXMLNode *psRoot, hashTableObj *metadata,
                                    char *pszXMLName, char *pszMetadataName, 
                                    char *pszHashDelimiter)
{
  char *pszHash, *pszXMLValue, *pszMetadata;

  if(psRoot == NULL || psRoot->psChild == NULL || 
     metadata == NULL || pszMetadataName == NULL || pszXMLName == NULL)
      return MS_FAILURE;

  /* Pass from KeywordList to Keyword level */
  psRoot = psRoot->psChild;

  /* Loop on all elements and append keywords to the hash table */
  while (psRoot)
  {
      if (psRoot->psChild && strcasecmp(psRoot->pszValue, pszXMLName) == 0)
      {
          pszXMLValue = psRoot->psChild->pszValue;
          pszHash = msLookupHashTable(metadata, pszMetadataName);
          if (pszHash != NULL)
          {
              pszMetadata = (char*)malloc(strlen(pszHash)+
                                          strlen(pszXMLValue)+2);
              if(pszHashDelimiter == NULL)
                  sprintf( pszMetadata, "%s%s", pszHash, pszXMLValue );
              else
                  sprintf( pszMetadata, "%s%s%s", pszHash, pszHashDelimiter, 
                           pszXMLValue );
              msInsertHashTable(metadata, pszMetadataName, pszMetadata);
              free(pszMetadata);
          }
          else
              msInsertHashTable(metadata, pszMetadataName, pszXMLValue);
      }
      psRoot = psRoot->psNext;   
  }

  return MS_SUCCESS;
}

/* msLoadMapContextContactInfo
**
** Put the Contact informations from a XML node and put them in a metadata.
**
*/
int msLoadMapContextContactInfo( CPLXMLNode *psRoot, hashTableObj *metadata )
{
    if(psRoot == NULL || metadata == NULL)
        return MS_FAILURE;

    /* Contact Person primary */
    msGetMapContextXMLHashValue(psRoot, 
                              "ContactPersonPrimary.ContactPerson", 
                              metadata, "wms_contactperson");
  msGetMapContextXMLHashValue(psRoot, 
                              "ContactPersonPrimary.ContactOrganization", 
                              metadata, "wms_contactorganization");
  /* Contact Position */
  msGetMapContextXMLHashValue(psRoot, 
                              "ContactPosition", 
                              metadata, "wms_contactposition");
  /* Contact Address */
  msGetMapContextXMLHashValue(psRoot, "ContactAddress.AddressType", 
                              metadata, "wms_addresstype");
  msGetMapContextXMLHashValue(psRoot, "ContactAddress.Address", 
                              metadata, "wms_address");
  msGetMapContextXMLHashValue(psRoot, "ContactAddress.City", 
                              metadata, "wms_city");
  msGetMapContextXMLHashValue(psRoot, "ContactAddress.StateOrProvince", 
                              metadata, "wms_stateorprovince");
  msGetMapContextXMLHashValue(psRoot, "ContactAddress.PostCode", 
                              metadata, "wms_postcode");
  msGetMapContextXMLHashValue(psRoot, "ContactAddress.Country", 
                              metadata, "wms_country");

  /* Others */
  msGetMapContextXMLHashValue(psRoot, "ContactVoiceTelephone", 
                              metadata, "wms_contactvoicetelephone");
  msGetMapContextXMLHashValue(psRoot, "ContactFacsimileTelephone", 
                              metadata, "wms_contactfacsimiletelephone");
  msGetMapContextXMLHashValue(psRoot, "ContactElectronicMailAddress", 
                              metadata, "wms_contactelectronicmailaddress");

  return MS_SUCCESS;
}

/*
** msLoadMapContextLayerFormat
**
**
*/
int msLoadMapContextLayerFormat(CPLXMLNode *psFormat, layerObj *layer)
{
  char *pszValue, *pszValue1, *pszHash;

  if(psFormat->psChild != NULL && 
     strcasecmp(psFormat->pszValue, "Format") == 0 )
  {
      if(psFormat->psChild->psNext == NULL)
          pszValue = psFormat->psChild->pszValue;
      else
          pszValue = psFormat->psChild->psNext->pszValue;
  }
  else
      pszValue = NULL;

  if(pszValue != NULL && strcasecmp(pszValue, "") != 0)
  {
      /* wms_format */
      pszValue1 = (char*)CPLGetXMLValue(psFormat, 
                                        "current", NULL);
      if(pszValue1 != NULL && 
         (strcasecmp(pszValue1, "1") == 0 || strcasecmp(pszValue1, "true")==0))
          msInsertHashTable(&(layer->metadata), 
                            "wms_format", pszValue);
      /* wms_formatlist */
      pszHash = msLookupHashTable(&(layer->metadata), 
                                  "wms_formatlist");
      if(pszHash != NULL)
      {
          pszValue1 = (char*)malloc(strlen(pszHash)+
                                    strlen(pszValue)+2);
          sprintf(pszValue1, "%s,%s", pszHash, pszValue);
          msInsertHashTable(&(layer->metadata), 
                            "wms_formatlist", pszValue1);
          free(pszValue1);
      }
      else
          msInsertHashTable(&(layer->metadata), 
                            "wms_formatlist", pszValue);
  }

  /* Make sure selected format is supported or select another
   * supported format.  Note that we can efficiently do this
   * only for GIF/PNG/JPEG, can't try to handle all GDAL
   * formats.
   */
  pszValue = msLookupHashTable(&(layer->metadata), "wms_format");

  if (
#ifndef USE_GD_PNG
      strcasecmp(pszValue, "image/png") == 0 || 
      strcasecmp(pszValue, "PNG") == 0 ||
#endif
#ifndef USE_GD_JPEG
      strcasecmp(pszValue, "image/jpeg") == 0 || 
      strcasecmp(pszValue, "JPEG") == 0 ||
#endif
#ifndef USE_GD_GIF
      strcasecmp(pszValue, "image/gif") == 0 || 
      strcasecmp(pszValue, "GIF") == 0 ||
#endif
      0 )
  {
      char **papszList=NULL;
      int i, numformats=0;

      pszValue = msLookupHashTable(&(layer->metadata), 
                                   "wms_formatlist");

      papszList = split(pszValue, ',', &numformats);
      for(i=0; i < numformats; i++)
      {
          if (
#ifdef USE_GD_PNG
              strcasecmp(papszList[i], "image/png") == 0 || 
              strcasecmp(papszList[i], "PNG") == 0 ||
#endif
#ifdef USE_GD_JPEG
              strcasecmp(papszList[i], "image/jpeg") == 0 || 
              strcasecmp(papszList[i], "JPEG") == 0 ||
#endif
#ifdef USE_GD_GIF
              strcasecmp(papszList[i], "image/gif") == 0 || 
              strcasecmp(papszList[i], "GIF") == 0 ||
#endif
              0 )
          {
              /* Found a match */
              msInsertHashTable(&(layer->metadata), 
                                "wms_format", papszList[i]);
              break;
          }
      }
      if(papszList)
          msFreeCharArray(papszList, numformats);

  } /* end if unsupported format */

  return MS_SUCCESS;
}

int msLoadMapContextLayerStyle(CPLXMLNode *psStyle, layerObj *layer, 
                               int nStyle)
{
  char *pszValue, *pszValue1, *pszValue2;
  char *pszHash, *pszStyle=NULL, *pszStyleName;
  CPLXMLNode *psStyleSLDBody;

  pszStyleName =(char*)CPLGetXMLValue(psStyle,"Name",NULL);
  if(pszStyleName == NULL)
  {
       pszStyleName = (char*)malloc(15);
       sprintf(pszStyleName, "Style{%d}", nStyle);
  }
  else
      pszStyleName = strdup(pszStyleName);

  /* wms_style */
  pszValue = (char*)CPLGetXMLValue(psStyle,"current",NULL);
  if(pszValue != NULL && 
     (strcasecmp(pszValue, "1") == 0 || 
      strcasecmp(pszValue, "true") == 0))
      msInsertHashTable(&(layer->metadata), 
                        "wms_style", pszStyleName);
  /* wms_stylelist */
  pszHash = msLookupHashTable(&(layer->metadata), 
                              "wms_stylelist");
  if(pszHash != NULL)
  {
      pszValue1 = (char*)malloc(strlen(pszHash)+
                                strlen(pszStyleName)+2);
      sprintf(pszValue1, "%s,%s", pszHash, pszStyleName);
      msInsertHashTable(&(layer->metadata), 
                        "wms_stylelist", pszValue1);
      free(pszValue1);
  }
  else
      msInsertHashTable(&(layer->metadata), 
                        "wms_stylelist", pszStyleName);

  /* Title */
  pszStyle = (char*)malloc(strlen(pszStyleName)+20);
  sprintf(pszStyle,"wms_style_%s_title",pszStyleName);

  if( msGetMapContextXMLHashValue(psStyle, "Title", &(layer->metadata), 
                                  pszStyle) == MS_FAILURE )
      msInsertHashTable(&(layer->metadata), pszStyle, layer->name);

  free(pszStyle);

  /* SLD */
  pszStyle = (char*)malloc(strlen(pszStyleName)+15);
  sprintf(pszStyle, "wms_style_%s_sld", pszStyleName);
  
  msGetMapContextXMLHashValueDecode( psStyle, "SLD.OnlineResource.xlink:href", 
                                     &(layer->metadata), pszStyle );
  free(pszStyle);

  /* SLDBODY */
  pszStyle = (char*)malloc(strlen(pszStyleName)+20);
  sprintf(pszStyle, "wms_style_%s_sld_body", pszStyleName);

  psStyleSLDBody = CPLGetXMLNode(psStyle, "SLD.StyledLayerDescriptor");
  if(psStyleSLDBody != NULL && &(layer->metadata) != NULL)
  {
      pszValue = CPLSerializeXMLTree(psStyleSLDBody);
      if(pszValue != NULL)
      {
          /* Before including SLDBody in the mapfile, we must replace the */
          /* double quote for single quote. This is to prevent having this: */
          /* "metadata" "<string attriute="ttt">" */
          char *c;
          for(c=pszValue; *c != '\0'; c++)
              if(*c == '"')
                  *c = '\'';
          msInsertHashTable(&(layer->metadata), pszStyle, pszValue );
          msFree(pszValue);
      }
  }

  free(pszStyle);

  /* LegendURL */
  pszStyle = (char*) malloc(strlen(pszStyleName) + 25);

  sprintf( pszStyle, "wms_style_%s_legendurl",
           pszStyleName);
  msLoadMapContextURLELements( CPLGetXMLNode(psStyle, "LegendURL"), 
                               &(layer->metadata), pszStyle );

  free(pszStyle);

  free(pszStyleName);

  /*  */
  /* Add the stylelist to the layer connection */
  /*  */
  if(msLookupHashTable(&(layer->metadata), 
                       "wms_stylelist") == NULL)
  {
      if(layer->connection)
          pszValue = strdup(layer->connection);
      else
          pszValue = strdup( "" ); 
      pszValue1 = strstr(pszValue, "STYLELIST=");
      if(pszValue1 != NULL)
      {                          
          pszValue1 += 10;
          pszValue2 = strchr(pszValue, '&');
          if(pszValue2 != NULL)
              pszValue1[pszValue2-pszValue1] = '\0';
          msInsertHashTable(&(layer->metadata), "wms_stylelist",
                            pszValue1);
      }
      free(pszValue);
  }

  /*  */
  /* Add the style to the layer connection */
  /*  */
  if(msLookupHashTable(&(layer->metadata), "wms_style") == NULL)
  {
      if(layer->connection)
          pszValue = strdup(layer->connection);
      else
          pszValue = strdup( "" ); 
      pszValue1 = strstr(pszValue, "STYLE=");
      if(pszValue1 != NULL)
      {                          
          pszValue1 += 6;
          pszValue2 = strchr(pszValue, '&');
          if(pszValue2 != NULL)
              pszValue1[pszValue2-pszValue1] = '\0';
          msInsertHashTable(&(layer->metadata), "wms_style",
                            pszValue1);
      }
      free(pszValue);
  }

  return MS_SUCCESS;
}

int msLoadMapContextLayerDimension(CPLXMLNode *psDimension, layerObj *layer)
{
    char *pszValue, *pszHash;
  char *pszDimension=NULL, *pszDimensionName=NULL;

  pszDimensionName =(char*)CPLGetXMLValue(psDimension,"name",NULL);
  if(pszDimensionName == NULL)
  {
      return MS_FALSE;
  }
  else
      pszDimensionName = strdup(pszDimensionName);

  pszDimension = (char*)malloc(strlen(pszDimensionName)+50);

  /* wms_dimension: This is the current dimension */
  pszValue = (char*)CPLGetXMLValue(psDimension, "current", NULL);
  if(pszValue != NULL && (strcasecmp(pszValue, "1") == 0 || 
                          strcasecmp(pszValue, "true") == 0))
      msInsertHashTable(&(layer->metadata), 
                        "wms_dimension", pszDimensionName);
  /* wms_dimensionlist */
  pszHash = msLookupHashTable(&(layer->metadata), 
                              "wms_dimensionlist");
  if(pszHash != NULL)
  {
      pszValue = (char*)malloc(strlen(pszHash)+
                                strlen(pszDimensionName)+2);
      sprintf(pszValue, "%s,%s", pszHash, pszDimensionName);
      msInsertHashTable(&(layer->metadata), 
                        "wms_dimensionlist", pszValue);
      free(pszValue);
  }
  else
      msInsertHashTable(&(layer->metadata), 
                        "wms_dimensionlist", pszDimensionName);

  /* Units */
  sprintf(pszDimension, "wms_dimension_%s_units", pszDimensionName);
  msGetMapContextXMLHashValue(psDimension, "units", &(layer->metadata), 
                              pszDimension);

  /* UnitSymbol */
  sprintf(pszDimension, "wms_dimension_%s_unitsymbol", pszDimensionName);
  msGetMapContextXMLHashValue(psDimension, "unitSymbol", &(layer->metadata),
                              pszDimension);

  /* userValue */
  sprintf(pszDimension, "wms_dimension_%s_uservalue", pszDimensionName);
  msGetMapContextXMLHashValue(psDimension, "userValue", &(layer->metadata),
                              pszDimension);
  if(strcasecmp(pszDimensionName, "time") == 0)
      msGetMapContextXMLHashValue(psDimension, "userValue", &(layer->metadata),
                                  "wms_time");

  /* default */
  sprintf(pszDimension, "wms_dimension_%s_default", pszDimensionName);
  msGetMapContextXMLHashValue(psDimension, "default", &(layer->metadata),
                              pszDimension);

  /* multipleValues */
  sprintf(pszDimension, "wms_dimension_%s_multiplevalues", pszDimensionName);
  msGetMapContextXMLHashValue(psDimension, "multipleValues",&(layer->metadata),
                              pszDimension);

  /* nearestValue */
  sprintf(pszDimension, "wms_dimension_%s_nearestvalue", pszDimensionName);
  msGetMapContextXMLHashValue(psDimension, "nearestValue", &(layer->metadata),
                              pszDimension);

  free(pszDimension);

  free(pszDimensionName);

  return MS_SUCCESS;
}



/*
** msLoadMapContextGeneral
**
** Load the General block of the mapcontext document
*/
int msLoadMapContextGeneral(mapObj *map, CPLXMLNode *psGeneral, 
                            CPLXMLNode *psMapContext, int nVersion, 
                            char *filename)
{

  char *pszProj=NULL;
  char *pszValue, *pszValue1, *pszValue2;

  /* Projection */
  pszValue = (char*)CPLGetXMLValue(psGeneral, 
                                   "BoundingBox.SRS", NULL);
  if(pszValue != NULL)
  {
      if(strncasecmp(pszValue, "AUTO:", 5) == 0)
      {
          pszProj = strdup(pszValue);
      }
      else
      {
          pszProj = (char*) malloc(sizeof(char)*(strlen(pszValue)+10));
          sprintf(pszProj, "init=epsg:%s", pszValue+5);
      }

      msInitProjection(&map->projection);
      map->projection.args[map->projection.numargs] = strdup(pszProj);
      map->projection.numargs++;
      msProcessProjection(&map->projection);

      if( (map->units = GetMapserverUnitUsingProj(&(map->projection))) == -1)
      {
          free(pszProj);
          msSetError( MS_MAPCONTEXTERR, 
                      "Unable to set units for projection '%s'",
                      "msLoadMapContext()", pszProj );
          return MS_FAILURE;
      }
      free(pszProj);
  }
  else
  {
      msDebug("Mandatory data General.BoundingBox.SRS missing in %s.",
              filename);
  }

  /* Extent */
  if( msGetMapContextXMLFloatValue(psGeneral, "BoundingBox.minx",
                                   &(map->extent.minx)) == MS_FAILURE)
  {
      msDebug("Mandatory data General.BoundingBox.minx missing in %s.",
              filename);
  }
  if( msGetMapContextXMLFloatValue(psGeneral, "BoundingBox.miny",
                               &(map->extent.miny)) == MS_FAILURE)
  {
      msDebug("Mandatory data General.BoundingBox.miny missing in %s.",
              filename);
  }
  if( msGetMapContextXMLFloatValue(psGeneral, "BoundingBox.maxx",
                               &(map->extent.maxx)) == MS_FAILURE)
  {
      msDebug("Mandatory data General.BoundingBox.maxx missing in %s.",
              filename);
  }
  if( msGetMapContextXMLFloatValue(psGeneral, "BoundingBox.maxy",
                               &(map->extent.maxy)) == MS_FAILURE)
  {
      msDebug("Mandatory data General.BoundingBox.maxy missing in %s.",
              filename);
  }

  /* Title */
  if( msGetMapContextXMLHashValue(psGeneral, "Title", 
                              &(map->web.metadata), "wms_title") == MS_FAILURE)
  {
      if ( nVersion >= OWS_1_0_0 )
         msDebug("Mandatory data General.Title missing in %s.", filename);
      else
      {
          if( msGetMapContextXMLHashValue(psGeneral, "gml:name", 
                             &(map->web.metadata), "wms_title") == MS_FAILURE )
          {
              if( nVersion < OWS_0_1_7 )
                msDebug("Mandatory data General.Title missing in %s.", filename);
              else
                msDebug("Mandatory data General.gml:name missing in %s.", 
                        filename);
          }
      }
  }

  /* Name */
  if( nVersion >= OWS_1_0_0 )
  {
      pszValue = (char*)CPLGetXMLValue(psMapContext, 
                                       "id", NULL);
      if (pszValue)
        map->name = strdup(pszValue);
  }
  else
  {
      if(msGetMapContextXMLStringValue(psGeneral, "Name", 
                                       &(map->name)) == MS_FAILURE)
      {
          msGetMapContextXMLStringValue(psGeneral, "gml:name", 
                                        &(map->name));
      }
  }
  /* Keyword */
  if( nVersion >= OWS_1_0_0 )
  {
      msLoadMapContextListInMetadata( 
          CPLGetXMLNode(psGeneral, "KeywordList"),
          &(map->web.metadata), "KEYWORD", "wms_keywordlist", "," );
  }
  else
    msGetMapContextXMLHashValue(psGeneral, "Keywords", 
                                &(map->web.metadata), "wms_keywordlist");

  /* Window */
  pszValue1 = (char*)CPLGetXMLValue(psGeneral,"Window.width",NULL);
  pszValue2 = (char*)CPLGetXMLValue(psGeneral,"Window.height",NULL);
  if(pszValue1 != NULL && pszValue2 != NULL)
  {
      map->width = atoi(pszValue1);
      map->height = atoi(pszValue2);
  }

  /* Abstract */
  if( msGetMapContextXMLHashValue( psGeneral, 
                                   "Abstract", &(map->web.metadata), 
                                   "wms_abstract") == MS_FAILURE )
  {
      msGetMapContextXMLHashValue( psGeneral, "gml:description", 
                                   &(map->web.metadata), "wms_abstract");
  }

  /* DataURL */
  msGetMapContextXMLHashValueDecode(psGeneral, 
                                   "DataURL.OnlineResource.xlink:href",
                                   &(map->web.metadata), "wms_dataurl");

  /* LogoURL */
  /* The logourl have a width, height, format and an URL */
  msLoadMapContextURLELements( CPLGetXMLNode(psGeneral, "LogoURL"), 
                               &(map->web.metadata), "wms_logourl" );

  /* DescriptionURL */
  /* The descriptionurl have a width, height, format and an URL */
  msLoadMapContextURLELements( CPLGetXMLNode(psGeneral, 
                                             "DescriptionURL"), 
                               &(map->web.metadata), "wms_descriptionurl" );

  /* Contact Info */
  msLoadMapContextContactInfo( 
      CPLGetXMLNode(psGeneral, "ContactInformation"), 
      &(map->web.metadata) );

  return MS_SUCCESS;
}

/*
** msLoadMapContextLayer
**
** Load a Layer block from a MapContext document
*/
int msLoadMapContextLayer(mapObj *map, CPLXMLNode *psLayer, int nVersion,
                          char *filename, int unique_layer_names)
{
  char *pszProj=NULL;
  char *pszValue;
  char *pszHash, *pszName=NULL;
  CPLXMLNode *psFormatList, *psFormat, *psStyleList, *psStyle;
  CPLXMLNode *psDimensionList, *psDimension;
  int nStyle;
  layerObj *layer;

  /* Init new layer */
  layer = &(map->layers[map->numlayers]);
  initLayer(layer, map);
  layer->map = (mapObj *)map;
  layer->type = MS_LAYER_RASTER;
  /* save the index */
  map->layers[map->numlayers].index = map->numlayers;
  map->layerorder[map->numlayers] = map->numlayers;
  map->numlayers++;
  
  
  /* Status */
  pszValue = (char*)CPLGetXMLValue(psLayer, "hidden", "1");
  if((pszValue != NULL) && (atoi(pszValue) == 0 && 
                            !strcasecmp(pszValue, "true") == 0))
      layer->status = MS_ON;
  else
      layer->status = MS_OFF;

  /* Queryable */
  pszValue = (char*)CPLGetXMLValue(psLayer, "queryable", "0");
  if(pszValue !=NULL && (atoi(pszValue) == 1  || 
                         strcasecmp(pszValue, "true") == 0))
      layer->template = strdup("ttt");

  /* Name and Title */
  pszValue = (char*)CPLGetXMLValue(psLayer, "Name", NULL);
  if(pszValue != NULL)
  {
      msInsertHashTable( &(layer->metadata), "wms_name", pszValue );

      if (unique_layer_names)
      {
          pszName = (char*)malloc(sizeof(char)*(strlen(pszValue)+10));
          sprintf(pszName, "l%d:%s", layer->index, pszValue);
          layer->name = strdup(pszName);
          free(pszName);
      }
      else
        layer->name  = strdup(pszValue);
  }
  else
  {
      pszName = (char*)malloc(sizeof(char)*10);
      sprintf(pszName, "l%d:", layer->index);
      layer->name = strdup(pszName);
      free(pszName);
  }

  if(msGetMapContextXMLHashValue(psLayer, "Title", &(layer->metadata), 
                                 "wms_title") == MS_FAILURE)
  {
      if(msGetMapContextXMLHashValue(psLayer, "Server.title", 
                          &(layer->metadata), "wms_title") == MS_FAILURE)
      {
          msDebug("Mandatory data Layer.Title missing in %s.", filename);
      }
  }

  /* Abstract */
  msGetMapContextXMLHashValue(psLayer, "Abstract", &(layer->metadata), 
                              "wms_abstract");

  /* DataURL */
  if(nVersion <= OWS_0_1_4)
  {
      msGetMapContextXMLHashValueDecode(psLayer, 
                                        "DataURL.OnlineResource.xlink:href",
                                        &(layer->metadata), "wms_dataurl");
  }
  else
  {
      /* The DataURL have a width, height, format and an URL */
      /* Width and height are not used, but they are included to */
      /* be consistent with the spec. */
      msLoadMapContextURLELements( CPLGetXMLNode(psLayer, "DataURL"), 
                                           &(layer->metadata), "wms_dataurl" );
  }

  /* The MetadataURL have a width, height, format and an URL */
  /* Width and height are not used, but they are included to */
  /* be consistent with the spec. */
  msLoadMapContextURLELements( CPLGetXMLNode(psLayer, "MetadataURL"), 
                                       &(layer->metadata), "wms_metadataurl" );


  /* MinScale && MaxScale */
  pszValue = (char*)CPLGetXMLValue(psLayer, "sld:MinScaleDenominator", NULL);
  if(pszValue != NULL)
  {
      layer->minscale = atof(pszValue);
  }

  pszValue = (char*)CPLGetXMLValue(psLayer, "sld:MaxScaleDenominator", NULL);
  if(pszValue != NULL)
  {
      layer->maxscale = atof(pszValue);
  }

  /*  */
  /* Server */
  /*  */
  if(nVersion >= OWS_0_1_4)
  {
      if(msGetMapContextXMLStringValueDecode(psLayer, 
                                          "Server.OnlineResource.xlink:href",
                                          &(layer->connection)) == MS_FAILURE)
      {
          msSetError(MS_MAPCONTEXTERR, 
              "Mandatory data Server.OnlineResource.xlink:href missing in %s.",
                     "msLoadMapContext()", filename);
          return MS_FAILURE;
      }
      else
      {
          msGetMapContextXMLHashValueDecode(psLayer, 
                                          "Server.OnlineResource.xlink:href", 
                                     &(layer->metadata), "wms_onlineresource");
          layer->connectiontype = MS_WMS;
      }
  }
  else
  {
      if(msGetMapContextXMLStringValueDecode(psLayer, 
                                             "Server.onlineResource", 
                                           &(layer->connection)) == MS_FAILURE)
      {
          msSetError(MS_MAPCONTEXTERR, 
                     "Mandatory data Server.onlineResource missing in %s.",
                     "msLoadMapContext()", filename);
          return MS_FAILURE;
      }
      else
      {
          msGetMapContextXMLHashValueDecode(psLayer, "Server.onlineResource", 
                                     &(layer->metadata), "wms_onlineresource");
          layer->connectiontype = MS_WMS;
      }
  }

  if(nVersion >= OWS_0_1_4)
  {
      if(msGetMapContextXMLHashValue(psLayer, "Server.version", 
                      &(layer->metadata), "wms_server_version") == MS_FAILURE)
      {
          msSetError(MS_MAPCONTEXTERR, 
                     "Mandatory data Server.version missing in %s.",
                     "msLoadMapContext()", filename);
          return MS_FAILURE;
      }
  }
  else
  {
      if(msGetMapContextXMLHashValue(psLayer, "Server.wmtver", 
                      &(layer->metadata), "wms_server_version") == MS_FAILURE)
      {
          msSetError(MS_MAPCONTEXTERR, 
                     "Mandatory data Server.wmtver missing in %s.",
                     "msLoadMapContext()", filename);
          return MS_FAILURE;
      }
  }

  /* Projection */
  msLoadMapContextListInMetadata( psLayer, &(layer->metadata), 
                                  "SRS", "wms_srs", " " );

  pszHash = msLookupHashTable(&(layer->metadata), "wms_srs");
  if(((pszHash == NULL) || (strcasecmp(pszHash, "") == 0)) && 
     map->projection.numargs != 0)
  {
      pszProj = map->projection.args[map->projection.numargs-1];

      if(pszProj != NULL)
      {
          if(strncasecmp(pszProj, "AUTO:", 5) == 0)
          {
              msInsertHashTable(&(layer->metadata),"wms_srs", pszProj);
          }
          else
          {
              if(strlen(pszProj) > 10)
              {
                  pszProj = (char*) malloc(sizeof(char) * (strlen(pszProj)));
                  sprintf( pszProj, "EPSG:%s", 
                           map->projection.args[map->projection.numargs-1]+10);
                  msInsertHashTable(&(layer->metadata),"wms_srs", pszProj);
              }
              else
              {
                  msDebug("Unable to set data for layer wms_srs from this"
                          " value %s.", 
                          pszProj);
              }
          }
      }
  }

  /*  */
  /* Format */
  /*  */
  if( nVersion >= OWS_0_1_4 )
  {
      psFormatList = CPLGetXMLNode(psLayer, "FormatList");
  }
  else
  {
      psFormatList = psLayer;
  }

  if(psFormatList != NULL)
  {
      for(psFormat = psFormatList->psChild; 
          psFormat != NULL; 
          psFormat = psFormat->psNext)
      {
          msLoadMapContextLayerFormat(psFormat, layer);
      }
                   
  } /* end FormatList parsing */

  /* Style */
  if( nVersion >= OWS_0_1_4 )
  {
      psStyleList = CPLGetXMLNode(psLayer, "StyleList");
  }
  else
  {
      psStyleList = psLayer;
  }

  if(psStyleList != NULL)
  {
      nStyle = 0;
      for(psStyle = psStyleList->psChild; 
          psStyle != NULL; 
          psStyle = psStyle->psNext)
      {
          if(strcasecmp(psStyle->pszValue, "Style") == 0)
          {
              nStyle++;
              msLoadMapContextLayerStyle(psStyle, layer, nStyle);
          }
      }
  }

  /* Dimension */
  psDimensionList = CPLGetXMLNode(psLayer, "DimensionList");
  if(psDimensionList != NULL)
  {
      for(psDimension = psDimensionList->psChild; 
          psDimension != NULL; 
          psDimension = psDimension->psNext)
      {
          if(strcasecmp(psDimension->pszValue, "Dimension") == 0)
          {
              msLoadMapContextLayerDimension(psDimension, layer);
          }
      }
  }
  

  return MS_SUCCESS;
}

#endif



/* msLoadMapContextURL()
**
** load an OGC Web Map Context format from an URL
**
** Take a map object and a URL to a conect file in arguments
*/

int msLoadMapContextURL(mapObj *map, char *urlfilename, int unique_layer_names)
{
#if defined(USE_WMS_LYR) && defined(USE_OGR)
    char *pszTmpFile = NULL;
    int status = 0;

    if (!map || !urlfilename)
    {
        msSetError(MS_MAPCONTEXTERR, 
                   "Invalid map or url given.",
                   "msGetMapContextURL()");
        return MS_FAILURE;
    }
    
    pszTmpFile = msTmpFile(map->mappath, map->web.imagepath, "context.xml");
    if (msHTTPGetFile(urlfilename, pszTmpFile, &status,-1, 0, 0) ==  MS_SUCCESS)
    {
        return msLoadMapContext(map, pszTmpFile, unique_layer_names);
    }
    else
    {
        msSetError(MS_MAPCONTEXTERR, 
                   "Could not open context file %s.",
                   "msGetMapContextURL()", urlfilename);
        return MS_FAILURE;
    }
    
#else
    msSetError(MS_MAPCONTEXTERR, 
               "Not implemented since Map Context is not enabled.",
               "msGetMapContextURL()");
    return MS_FAILURE;
#endif
}
/* msLoadMapContext()
**
** Get a mapfile from a OGC Web Map Context format
**
** Take as first map object and a file in arguments
** If The 2nd aregument unique_layer_names is set to MS_TRUE, the layer
** name created would be unique and be prefixed with an l plus the layers's index
** (eg l:1:park. l:2:road ...). If It is set to MS_FALSE, the layer name 
** would be the same name as the layer name in the context
*/
int msLoadMapContext(mapObj *map, char *filename, int unique_layer_names)
{
#if defined(USE_WMS_LYR) && defined(USE_OGR)
  char *pszWholeText, *pszValue;
  CPLXMLNode *psRoot, *psMapContext, *psLayer, *psLayerList, *psChild;
  char szPath[MS_MAXPATHLEN];
  int nVersion=-1;
  char szVersionBuf[OWS_VERSION_MAXLEN];

  /*  */
  /* Load the raw XML file */
  /*  */
  
  pszWholeText = msGetMapContextFileText(
      msBuildPath(szPath, map->mappath, filename));
  if(pszWholeText == NULL)
  {
      msSetError( MS_MAPCONTEXTERR, "Unable to read %s", 
                  "msLoadMapContext()", filename );
      return MS_FAILURE;
  }

  if( ( strstr( pszWholeText, "<WMS_Viewer_Context" ) == NULL ) &&
      ( strstr( pszWholeText, "<View_Context" ) == NULL ) &&
      ( strstr( pszWholeText, "<ViewContext" ) == NULL ) )
    
  {
      free( pszWholeText );
      msSetError( MS_MAPCONTEXTERR, "Not a Map Context file (%s)", 
                  "msLoadMapContext()", filename );
      return MS_FAILURE;
  }

  /*  */
  /* Convert to XML parse tree. */
  /*  */
  psRoot = CPLParseXMLString( pszWholeText );
  free( pszWholeText );

  /* We assume parser will report errors via CPL. */
  if( psRoot == NULL )
  {
      msSetError( MS_MAPCONTEXTERR, "Invalid XML file (%s)", 
                  "msLoadMapContext()", filename );
      if(psRoot != NULL)
          CPLDestroyXMLNode(psRoot);

      return MS_FAILURE;
  }

  /*  */
  /* Valid the MapContext file and get the root of the document */
  /*  */
  psChild = psRoot;
  psMapContext = NULL;
  while( psChild != NULL )
  {
      if( psChild->eType == CXT_Element && 
          (EQUAL(psChild->pszValue,"WMS_Viewer_Context") ||
           EQUAL(psChild->pszValue,"View_Context") ||
           EQUAL(psChild->pszValue,"ViewContext")) )
      {
          psMapContext = psChild;
          break;
      }
      else
      {
          psChild = psChild->psNext;
      }
  }

  if( psMapContext == NULL )
  {
      CPLDestroyXMLNode(psRoot);
      msSetError( MS_MAPCONTEXTERR, "Invalid Map Context File (%s)", 
                  "msLoadMapContext()", filename );
      return MS_FAILURE;
  }

  /* Fetch document version number */
  pszValue = (char*)CPLGetXMLValue(psMapContext, 
                                   "version", NULL);
  if( !pszValue )
  {
      msDebug( "msLoadMapContext(): Mandatory data version missing in %s, assuming 0.1.4.",
               filename );
      pszValue = "0.1.4";
  }

  nVersion = msOWSParseVersionString(pszValue);

  /* Make sure this is a supported version */
  switch (nVersion)
  {
    case OWS_0_1_2:
    case OWS_0_1_4:
    case OWS_0_1_7:
    case OWS_1_0_0:
    case OWS_1_1_0:
      /* All is good, this is a supported version. */
      break;
    default:
      /* Not a supported version */
      msSetError(MS_MAPCONTEXTERR, 
                 "This version of Map Context is not supported (%s).",
                 "msLoadMapContext()", pszValue);
      CPLDestroyXMLNode(psRoot);
      return MS_FAILURE;
  }

  /* Reformat and save Version in metadata */
  msInsertHashTable( &(map->web.metadata), "wms_context_version",
                     msOWSGetVersionString(nVersion, szVersionBuf));

  if( nVersion >= OWS_0_1_7 && nVersion < OWS_1_0_0)
  {
      if( msGetMapContextXMLHashValue(psMapContext, "fid", 
                           &(map->web.metadata), "wms_context_fid") == MS_FAILURE )
      {
          msDebug("Mandatory data fid missing in %s.", filename);
      }
  }

  /*  */
  /* Load the General bloc */
  /*  */
  psChild = CPLGetXMLNode( psMapContext, "General" );
  if( psChild == NULL )
  {
      CPLDestroyXMLNode(psRoot);
      msSetError(MS_MAPCONTEXTERR, 
                 "The Map Context document provided (%s) does not contain any "
                 "General elements.",
                 "msLoadMapContext()", filename);
      return MS_FAILURE;
  }

  if( msLoadMapContextGeneral(map, psChild, psMapContext, 
                              nVersion, filename) == MS_FAILURE )
  {
      CPLDestroyXMLNode(psRoot);
      return MS_FAILURE;
  }

  /*  */
  /* Load the bloc LayerList */
  /*  */
  psLayerList = CPLGetXMLNode(psMapContext, "LayerList");
  if( psLayerList != NULL )
  {
      for(psLayer = psLayerList->psChild; 
          psLayer != NULL; 
          psLayer = psLayer->psNext)
      {
          if(EQUAL(psLayer->pszValue, "Layer"))
          {
              if( msLoadMapContextLayer(map, psLayer, nVersion, 
                                        filename, unique_layer_names) == MS_FAILURE )
              {
                  CPLDestroyXMLNode(psRoot);
                  return MS_FAILURE;
              }
          }/* end Layer parsing */
      }/* for */
  }

  CPLDestroyXMLNode(psRoot);

  return MS_SUCCESS;

#else
  msSetError(MS_MAPCONTEXTERR, 
             "Not implemented since Map Context is not enabled.",
             "msGetMapContext()");
  return MS_FAILURE;
#endif
}


/* msSaveMapContext()
**
** Save a mapfile into the OGC Web Map Context format
**
** Take a map object and a file in arguments
*/
int msSaveMapContext(mapObj *map, char *filename)
{
#if defined(USE_WMS_LYR) && defined(USE_OGR)
  FILE *stream;
  char szPath[MS_MAXPATHLEN];
  int nStatus;

  /* open file */
  if(filename != NULL && strlen(filename) > 0) {
    stream = fopen(msBuildPath(szPath, map->mappath, filename), "wb");
    if(!stream) {
      msSetError(MS_IOERR, "(%s)", "msSaveMapContext()", filename);
      return(MS_FAILURE);
    }
  }
  else
  {
      msSetError(MS_IOERR, "Filename is undefined.", "msSaveMapContext()");
      return MS_FAILURE;
  }

  nStatus = msWriteMapContext(map, stream);

  fclose(stream);

  return nStatus;
#else
  msSetError(MS_MAPCONTEXTERR, 
             "Not implemented since Map Context is not enabled.",
             "msSaveMapContext()");
  return MS_FAILURE;
#endif
}



int msWriteMapContext(mapObj *map, FILE *stream)
{
#if defined(USE_WMS_LYR) && defined(USE_OGR)
  const char * version, *value;
  char * tabspace=NULL, *pszValue, *pszChar,*pszSLD=NULL,*pszURL,*pszSLD2=NULL;
  char *pszStyle, *pszCurrent, *pszStyleItem, *pszSLDBody;
  char *pszEncodedVal;
  int i, nValue, nVersion=-1;
  /* Dimension element */
  char *pszDimension;
  const char *pszDimUserValue=NULL, *pszDimUnits=NULL, *pszDimDefault=NULL;
  const char *pszDimNearValue=NULL, *pszDimUnitSymbol=NULL;
  const char *pszDimMultiValue=NULL;
  int bDimensionList = 0;

  /* Decide which version we're going to return... */
  version = msLookupHashTable(&(map->web.metadata), "wms_context_version");
  if(version == NULL)
    version = "1.1.0";

  nVersion = msOWSParseVersionString(version);
  if (nVersion < 0)
      return MS_FAILURE;  /* msSetError() already called. */

  /* Make sure this is a supported version */
  /* Note that we don't write 0.1.2 even if we read it. */
  switch (nVersion)
  {
    case OWS_0_1_4:
    case OWS_0_1_7:
    case OWS_1_0_0:
    case OWS_1_1_0:
      /* All is good, this is a supported version. */
      break;
    default:
      /* Not a supported version */
      msSetError(MS_MAPCONTEXTERR, 
                 "This version of Map Context is not supported (%s).",
                 "msSaveMapContext()", version);
      return MS_FAILURE;
  }

  /* file header */
  msOWSPrintEncodeMetadata(stream, &(map->web.metadata), 
                     NULL, "wms_encoding", OWS_NOERR,
                "<?xml version='1.0' encoding=\"%s\" standalone=\"no\" ?>\n",
                    "ISO-8859-1");

  /* set the WMS_Viewer_Context information */
  pszEncodedVal = msEncodeHTMLEntities(version);
  if(nVersion >= OWS_1_0_0)
  {
      msIO_fprintf( stream, "<ViewContext version=\"%s\"", pszEncodedVal );
  }
  else if(nVersion >= OWS_0_1_7)
  {
      msIO_fprintf( stream, "<View_Context version=\"%s\"", pszEncodedVal );
      
  }
  else /* 0.1.4 */
  {
      msIO_fprintf( stream, "<WMS_Viewer_Context version=\"%s\"", pszEncodedVal );
  }
  msFree(pszEncodedVal);

  if ( nVersion >= OWS_0_1_7 && nVersion < OWS_1_0_0 )
  {
      msOWSPrintEncodeMetadata(stream, &(map->web.metadata), NULL, 
                               "wms_context_fid", OWS_NOERR," fid=\"%s\"","0");
  }
  if ( nVersion >= OWS_1_0_0 )
      msOWSPrintEncodeParam(stream, "MAP.NAME", map->name, OWS_NOERR, 
                            " id=\"%s\"", NULL);

  msIO_fprintf( stream, " xmlns:xsi=\"http://www.w3.org/2001/XMLSchema-instance\"");

  if( nVersion >= OWS_0_1_7 && nVersion < OWS_1_0_0 )
  {
      msIO_fprintf( stream, " xmlns:gml=\"http://www.opengis.net/gml\"");
  }
  if( nVersion >= OWS_1_0_0 )
  {
      msIO_fprintf( stream, " xmlns:xlink=\"http://www.w3.org/1999/xlink\"");
      msIO_fprintf( stream, " xmlns=\"http://www.opengis.net/context\"");
      msIO_fprintf( stream, " xmlns:sld=\"http://www.opengis.net/sld\"");
      pszEncodedVal = msEncodeHTMLEntities(msOWSGetSchemasLocation(map));
      if( nVersion >= OWS_1_1_0 )
          msIO_fprintf( stream, 
                        " xsi:schemaLocation=\"http://www.opengis.net/context %s/context/1.1.0/context.xsd\">\n",
                        pszEncodedVal);
      else
          msIO_fprintf( stream, 
                        " xsi:schemaLocation=\"http://www.opengis.net/context %s/context/1.0.0/context.xsd\">\n",
                        pszEncodedVal);
      msFree(pszEncodedVal);
  }
  else
  {
      msIO_fprintf( stream, " xmlns:xlink=\"http://www.w3.org/TR/xlink\"");

      pszEncodedVal = msEncodeHTMLEntities(msOWSGetSchemasLocation(map));
      msIO_fprintf( stream, " xsi:noNamespaceSchemaLocation=\"%s/contexts/",
               pszEncodedVal );
      msFree(pszEncodedVal);
      pszEncodedVal = msEncodeHTMLEntities(msOWSGetSchemasLocation(map));
      msIO_fprintf( stream, "%s/context.xsd\">\n", pszEncodedVal);
      msFree(pszEncodedVal);
  }

  /* set the General information */
  msIO_fprintf( stream, "  <General>\n" );

  /* Window */
  if( map->width != -1 || map->height != -1 )
      msIO_fprintf( stream, "    <Window width=\"%d\" height=\"%d\"/>\n", 
               map->width, map->height );

  /* Bounding box corners and spatial reference system */
  if(tabspace)
      free(tabspace);
  tabspace = strdup("    ");
  value = msOWSGetEPSGProj(&(map->projection), &(map->web.metadata), "MO", MS_TRUE);
  msIO_fprintf( stream, 
          "%s<!-- Bounding box corners and spatial reference system -->\n", 
           tabspace );
  if(!value || (strcasecmp(value, "(null)") == 0))
      msIO_fprintf(stream, "<!-- WARNING: Mandatory data 'projection' was missing in this context. -->\n");

  pszEncodedVal = msEncodeHTMLEntities(value);
  msIO_fprintf( stream, "%s<BoundingBox SRS=\"%s\" minx=\"%f\" miny=\"%f\" maxx=\"%f\" maxy=\"%f\"/>\n", 
           tabspace, pszEncodedVal, map->extent.minx, map->extent.miny, 
           map->extent.maxx, map->extent.maxy );
  msFree(pszEncodedVal);

  /* Title, name */
  if( nVersion >= OWS_0_1_7 && nVersion < OWS_1_0_0 )
  {
      msOWSPrintEncodeParam(stream, "MAP.NAME", map->name, OWS_NOERR, 
                            "    <gml:name>%s</gml:name>\n", NULL);
  }
  else 
  {
      if (nVersion < OWS_0_1_7)
          msOWSPrintEncodeParam(stream, "MAP.NAME", map->name, OWS_NOERR, 
                                "    <Name>%s</Name>\n", NULL);

      msIO_fprintf( stream, "%s<!-- Title of Context -->\n", tabspace );
      msOWSPrintEncodeMetadata(stream, &(map->web.metadata), 
                               NULL, "wms_title", OWS_WARN,
                               "    <Title>%s</Title>\n", map->name);
  }

  /* keyword */
  if (nVersion >= OWS_1_0_0)
  {
      if (msLookupHashTable(&(map->web.metadata),"wms_keywordlist")!=NULL)
      {
          char **papszKeywords;
          int nKeywords, iKey;

          pszValue = msLookupHashTable(&(map->web.metadata), 
                                       "wms_keywordlist");
          papszKeywords = split(pszValue, ',', &nKeywords);
          if(nKeywords > 0 && papszKeywords)
          {
              msIO_fprintf( stream, "    <KeywordList>\n");
              for(iKey=0; iKey<nKeywords; iKey++)
              {
                  pszEncodedVal = msEncodeHTMLEntities(papszKeywords[iKey]);
                  msIO_fprintf( stream, "      <Keyword>%s</Keyword>\n", 
                          pszEncodedVal);
                  msFree(pszEncodedVal);
              }
              msIO_fprintf( stream, "    </KeywordList>\n");
          }
      }
  }
  else
    msOWSPrintEncodeMetadataList(stream, &(map->web.metadata), NULL, 
                                 "wms_keywordlist", 
                                 "    <Keywords>\n", "    </Keywords>\n",
                                 "      %s\n", NULL);

  /* abstract */
  if( nVersion >= OWS_0_1_7 && nVersion < OWS_1_0_0 )
  {
      msOWSPrintEncodeMetadata(stream, &(map->web.metadata), 
                               NULL, "wms_abstract", OWS_NOERR,
                         "    <gml:description>%s</gml:description>\n", NULL);
  }
  else
  {
      msOWSPrintEncodeMetadata(stream, &(map->web.metadata), 
                               NULL, "wms_abstract", OWS_NOERR,
                               "    <Abstract>%s</Abstract>\n", NULL);
  }

  /* LogoURL */
  /* The LogoURL have a width, height, format and an URL */
  msOWSPrintURLType(stream, &(map->web.metadata), "MO", "logourl", 
                    OWS_NOERR, NULL, "LogoURL", NULL, " width=\"%s\"", 
                    " height=\"%s\""," format=\"%s\"", 
          "      <OnlineResource xlink:type=\"simple\" xlink:href=\"%s\"/>\n", 
                    MS_FALSE, MS_FALSE, MS_FALSE, MS_FALSE, MS_TRUE, 
                    NULL, NULL, NULL, NULL, NULL, "    ");

  /* DataURL */
  msOWSPrintEncodeMetadata(stream, &(map->web.metadata), 
                           NULL, "wms_dataurl", OWS_NOERR,
                "    <DataURL>\n      <OnlineResource xlink:type=\"simple\" xlink:href=\"%s\"/>\n    </DataURL>\n", NULL);

  /* DescriptionURL */
  /* The DescriptionURL have a width, height, format and an URL */
  /* The metadata is structured like this: "width height format url" */
  msOWSPrintURLType(stream, &(map->web.metadata), "MO", "descriptionurl", 
                    OWS_NOERR, NULL, "DescriptionURL", NULL, " width=\"%s\"", 
                    " height=\"%s\""," format=\"%s\"", 
          "      <OnlineResource xlink:type=\"simple\" xlink:href=\"%s\"/>\n", 
                    MS_FALSE, MS_FALSE, MS_FALSE, MS_FALSE, MS_TRUE, 
                    NULL, NULL, NULL, NULL, NULL, "    ");

  /* Contact Info */
  msOWSPrintContactInfo( stream, tabspace, OWS_1_1_0, &(map->web.metadata), "MO" );

  /* Close General */
  msIO_fprintf( stream, "  </General>\n" );
  free(tabspace);

  /* Set the layer list */
  msIO_fprintf(stream, "  <LayerList>\n");

  /* Loop on all layer   */
  for(i=0; i<map->numlayers; i++)
  {
      if(map->layers[i].connectiontype == MS_WMS)
      {
          if(map->layers[i].status == MS_OFF)
              nValue = 1;
          else
              nValue = 0;
          msIO_fprintf(stream, "    <Layer queryable=\"%d\" hidden=\"%d\">\n", 
                  msIsLayerQueryable(&(map->layers[i])), nValue);

          /*  */
          /* Server definition */
          /*  */
          if(nVersion <= OWS_1_0_0 )
              msOWSPrintEncodeMetadata(stream, &(map->layers[i].metadata), 
                                       NULL, "wms_server_version", OWS_WARN,
                             "      <Server service=\"WMS\" version=\"%s\" ",
                                       "1.0.0");
          else
              msOWSPrintEncodeMetadata(stream, &(map->layers[i].metadata), 
                                       NULL, "wms_server_version", OWS_WARN,
                          "      <Server service=\"OGC:WMS\" version=\"%s\" ",
                                       "1.0.0");
          if(map->layers[i].name)
              msOWSPrintEncodeMetadata(stream, &(map->layers[i].metadata), 
                                       NULL, "wms_title", OWS_NOERR, 
                                       "title=\"%s\">\n", map->layers[i].name);
          else
          {
              msOWSPrintEncodeMetadata(stream, &(map->layers[i].metadata), 
                                       NULL, "wms_title", OWS_NOERR, 
                                       "title=\"%s\">\n", "");
          }

          /* Get base url of the online resource to be the default value */
          if(map->layers[i].connection)
              pszValue = strdup( map->layers[i].connection );
          else
              pszValue = strdup( "" );
          pszChar = strchr(pszValue, '?');
          if( pszChar )
              pszValue[pszChar - pszValue] = '\0';
          if(msOWSPrintEncodeMetadata(stream, &(map->layers[i].metadata), 
                                      NULL, "wms_onlineresource", OWS_WARN, 
         "        <OnlineResource xlink:type=\"simple\" xlink:href=\"%s\"/>\n",
                                      pszValue) == OWS_WARN)
              msIO_fprintf(stream, "<!-- wms_onlineresource not set, using base URL"
                      " , but probably not what you want -->\n");
          msIO_fprintf(stream, "      </Server>\n");
          if(pszValue)
              free(pszValue);

          /*  */
          /* Layer information */
          /*  */
          msOWSPrintEncodeMetadata(stream, &(map->layers[i].metadata), 
                             NULL, "wms_name", OWS_WARN, 
                             "      <Name>%s</Name>\n", 
                             map->layers[i].name);
          msOWSPrintEncodeMetadata(stream, &(map->layers[i].metadata), 
                             NULL, "wms_title", OWS_WARN, 
                             "      <Title>%s</Title>\n", 
                             map->layers[i].name);
          msOWSPrintEncodeMetadata(stream, &(map->layers[i].metadata), 
                             NULL, "wms_abstract", OWS_NOERR, 
                             "      <Abstract>%s</Abstract>\n", 
                             NULL);

          /* DataURL */
          if(nVersion <= OWS_0_1_4)
          {
              msOWSPrintEncodeMetadata(stream, &(map->layers[i].metadata), 
                                 NULL, "wms_dataurl", OWS_NOERR, 
                                 "      <DataURL>%s</DataURL>\n", 
                                 NULL);
          }
          else
          {
              /* The DataURL have a width, height, format and an URL */
              /* The metadata will be structured like this:  */
              /* "width height format url" */
              /* Note: in version 0.1.7 the width and height are not included  */
              /* in the Context file, but they are included in the metadata for */
              /* for consistency with the URLType. */
              msOWSPrintURLType(stream, &(map->layers[i].metadata), "MO", 
                                "dataurl", OWS_NOERR, NULL, "DataURL", NULL, 
                                " width=\"%s\"", " height=\"%s\"",
                                " format=\"%s\"", 
                                "        <OnlineResource xlink:type=\"simple\""
                                " xlink:href=\"%s\"/>\n", 
                                MS_FALSE, MS_FALSE, MS_FALSE, MS_FALSE, 
                                MS_TRUE, NULL, NULL, NULL,NULL,NULL, "      ");
          }

          /* MetadataURL */
          /* The MetadataURL have a width, height, format and an URL */
          /* The metadata will be structured like this:  */
          /* "width height format url" */
          msOWSPrintURLType(stream, &(map->layers[i].metadata), "MO", 
                            "metadataurl", OWS_NOERR, NULL, "MetadataURL",NULL,
                            " width=\"%s\"", " height=\"%s\""," format=\"%s\"",
                            "        <OnlineResource xlink:type=\"simple\""
                            " xlink:href=\"%s\"/>\n", 
                            MS_FALSE, MS_FALSE, MS_FALSE, MS_FALSE, 
                            MS_TRUE, NULL, NULL, NULL, NULL, NULL, "      ");

          /* MinScale && MaxScale */
          if(nVersion >= OWS_1_1_0 && map->layers[i].minscale > 0)
              msIO_fprintf(stream, 
               "      <sld:MinScaleDenominator>%g</sld:MinScaleDenominator>\n",
                           map->layers[i].minscale);
          if(nVersion >= OWS_1_1_0 && map->layers[i].maxscale > 0)
              msIO_fprintf(stream, 
               "      <sld:MaxScaleDenominator>%g</sld:MaxScaleDenominator>\n",
                           map->layers[i].maxscale);

          /* Layer SRS */
          pszValue = (char*)msOWSGetEPSGProj(&(map->layers[i].projection), 
                                             &(map->layers[i].metadata),
                                             "MO", MS_FALSE);
          if(pszValue && (strcasecmp(pszValue, "(null)") != 0))
          {
              pszEncodedVal = msEncodeHTMLEntities(pszValue);
              msIO_fprintf(stream, "      <SRS>%s</SRS>\n", pszEncodedVal);
              msFree(pszEncodedVal);
          }

          /* Format */
          if(msLookupHashTable(&(map->layers[i].metadata),"wms_formatlist")==NULL && 
             msLookupHashTable(&(map->layers[i].metadata),"wms_format")==NULL)
          {
              pszURL = NULL;
              if(map->layers[i].connection)
                  pszURL = strdup( map->layers[i].connection );
              else
                  pszURL = strdup( "" );
              pszValue = pszURL;
              pszValue = strstr( pszValue, "FORMAT=" );
              if( pszValue )
              {
                  pszValue += 7;
                  pszChar = strchr(pszValue, '&');
                  if( pszChar )
                      pszValue[pszChar - pszValue] = '\0';
                  if(strcasecmp(pszValue, "") != 0)
                  {
                      pszEncodedVal = msEncodeHTMLEntities(pszValue);
                      msIO_fprintf( stream, "      <FormatList>\n");
                      msIO_fprintf(stream,"        <Format>%s</Format>\n",pszValue);
                      msIO_fprintf( stream, "      </FormatList>\n");
                      msFree(pszEncodedVal);
                  }
              }
              if(pszURL)
                  free(pszURL);
          }
          else
          {
              char **papszFormats;
              int numFormats, nForm;

              pszValue = msLookupHashTable(&(map->layers[i].metadata), 
                                           "wms_formatlist");
              if(!pszValue)
                  pszValue = msLookupHashTable(&(map->layers[i].metadata), 
                                               "wms_format");
              pszCurrent = msLookupHashTable(&(map->layers[i].metadata), 
                                             "wms_format");

              papszFormats = split(pszValue, ',', &numFormats);
              if(numFormats > 0 && papszFormats)
              {
                  msIO_fprintf( stream, "      <FormatList>\n");
                  for(nForm=0; nForm<numFormats; nForm++)
                  {
                      pszEncodedVal =msEncodeHTMLEntities(papszFormats[nForm]);
                      if(pszCurrent && (strcasecmp(papszFormats[nForm], 
                                                   pszCurrent) == 0))
                          msIO_fprintf( stream,
                                 "        <Format current=\"1\">%s</Format>\n",
                                   pszEncodedVal);
                      else
                          msIO_fprintf( stream, "        <Format>%s</Format>\n", 
                                   pszEncodedVal);
                      msFree(pszEncodedVal);
                  }
                  msIO_fprintf( stream, "      </FormatList>\n");
              }
              if(papszFormats)
                  msFreeCharArray(papszFormats, numFormats);
          }
          /* Style */
          /* First check the stylelist */
          pszValue = msLookupHashTable(&(map->layers[i].metadata), 
                                       "wms_stylelist");
          if(pszValue == NULL || strlen(trimLeft(pszValue)) < 1)
          {
              /* Check if the style is in the connection URL */
              pszURL = "";
              if(map->layers[i].connection)
                  pszURL = strdup( map->layers[i].connection );
              else
                  pszURL = strdup( "" );
              pszValue = pszURL;
              /* Grab the STYLES in the URL */
              pszValue = strstr( pszValue, "STYLES=" );
              if( pszValue )
              {
                  pszValue += 7;
                  pszChar = strchr(pszValue, '&');
                  if( pszChar )
                      pszValue[pszChar - pszValue] = '\0';

                  /* Check the SLD string from the URL */
                  if(map->layers[i].connection)
                      pszSLD2 = strdup(map->layers[i].connection);
                  else
                      pszSLD2 = strdup( "" );
                  if(pszSLD2)
                  {
                      pszSLD = strstr(pszSLD2, "SLD=");
                      pszSLDBody = strstr(pszSLD2, "SLD_BODY=");
                  }
                  else
                  {
                      pszSLD = NULL;
                      pszSLDBody = NULL;
                  }
                  /* Check SLD */
                  if( pszSLD )
                  {
                      pszChar = strchr(pszSLD, '&');
                      if( pszChar )
                          pszSLD[pszChar - pszSLD] = '\0';
                      pszSLD += 4;
                  }
                  /* Check SLDBody  */
                  if( pszSLDBody )
                  {
                      pszChar = strchr(pszSLDBody, '&');
                      if( pszChar )
                          pszSLDBody[pszChar - pszSLDBody] = '\0';
                      pszSLDBody += 9;
                  }
                  if( (pszValue && (strcasecmp(pszValue, "") != 0)) || 
                      (pszSLD && (strcasecmp(pszSLD, "") != 0)) || 
                      (pszSLDBody && (strcasecmp(pszSLDBody, "") != 0)))
                  {
                      /* Write Name and Title */
                      msIO_fprintf( stream, "      <StyleList>\n");
                      msIO_fprintf( stream, "        <Style current=\"1\">\n");
                      if( pszValue && (strcasecmp(pszValue, "") != 0))
                      {
                          pszEncodedVal = msEncodeHTMLEntities(pszValue);
                          msIO_fprintf(stream, "          <Name>%s</Name>\n", 
                                  pszEncodedVal);
                          msIO_fprintf(stream,"          <Title>%s</Title>\n",
                                  pszEncodedVal);
                          msFree(pszEncodedVal);
                      }
                      /* Write the SLD string from the URL */
                      if( pszSLD && (strcasecmp(pszSLD, "") != 0))
                      {
                          pszEncodedVal = msEncodeHTMLEntities(pszSLD);
                          msIO_fprintf( stream, "          <SLD>\n" );
                          msIO_fprintf( stream, 
                         "            <OnlineResource xlink:type=\"simple\" ");
                          msIO_fprintf(stream,"xlink:href=\"%s\"/>", 
                                       pszEncodedVal);
                          msIO_fprintf( stream, "          </SLD>\n" );
                          free(pszEncodedVal);
                      }
                      else if(pszSLDBody && (strcasecmp(pszSLDBody, "") != 0))
                      {
                          msIO_fprintf( stream, "          <SLD>\n" );
                          msIO_fprintf( stream, "            %s\n",pszSLDBody);
                          msIO_fprintf( stream, "          </SLD>\n" );
                      }
                      msIO_fprintf( stream, "        </Style>\n");
                      msIO_fprintf( stream, "      </StyleList>\n");
                  }
                  if(pszSLD2)
                  {
                      free(pszSLD2);
                      pszSLD2 = NULL;
                  }
              }
              if(pszURL)
              {
                  free(pszURL);
                  pszURL = NULL;
              }
          }
          else
          {
              /* If the style information is not in the connection URL, */
              /* read the metadata. */
              pszValue = msLookupHashTable(&(map->layers[i].metadata), 
                                           "wms_stylelist");
              pszCurrent = msLookupHashTable(&(map->layers[i].metadata), 
                                             "wms_style");
              msIO_fprintf( stream, "      <StyleList>\n");
              /* Loop in each style in the style list */
              while(pszValue != NULL)
              {
                  pszStyle = strdup(pszValue);
                  pszChar = strchr(pszStyle, ',');
                  if(pszChar != NULL)
                      pszStyle[pszChar - pszStyle] = '\0';
                  if(strcasecmp(pszStyle, "") == 0)
                      continue;

                  if(pszCurrent && (strcasecmp(pszStyle, pszCurrent) == 0))
                      msIO_fprintf( stream,"        <Style current=\"1\">\n" );
                  else
                      msIO_fprintf( stream, "        <Style>\n" );

                  /* Write SLDURL if it is in the metadata */
                  pszStyleItem = (char*)malloc(strlen(pszStyle)+10+10);
                  sprintf(pszStyleItem, "wms_style_%s_sld", pszStyle);
                  if(msLookupHashTable(&(map->layers[i].metadata),
                                       pszStyleItem) != NULL)
                  {
                      msIO_fprintf(stream, "          <SLD>\n");
                      msOWSPrintEncodeMetadata(stream, 
                                               &(map->layers[i].metadata),
                                               NULL, pszStyleItem, 
                                               OWS_NOERR, 
     "            <OnlineResource xlink:type=\"simple\" xlink:href=\"%s\"/>\n",
                                               NULL);
                      msIO_fprintf(stream, "          </SLD>\n");
                      free(pszStyleItem);
                  }
                  else
                  {
                      /* If the URL is not there, check for SLDBody */
                      sprintf(pszStyleItem, "wms_style_%s_sld_body", pszStyle);
                      if(msLookupHashTable(&(map->layers[i].metadata),
                                           pszStyleItem) != NULL)
                      {
                          msIO_fprintf(stream, "          <SLD>\n");
                          msOWSPrintMetadata(stream,&(map->layers[i].metadata),
                                             NULL, pszStyleItem, OWS_NOERR, 
                                             "            %s\n", NULL);
                          msIO_fprintf(stream, "          </SLD>\n");
                          free(pszStyleItem);
                      }
                      else
                      {
                          /* If the SLD is not specified, then write the */
                          /* name, Title and LegendURL */
                          free(pszStyleItem);
                          /* Name */
                          pszEncodedVal = msEncodeHTMLEntities(pszStyle);
                          msIO_fprintf(stream, "          <Name>%s</Name>\n", 
                                       pszEncodedVal);
                          msFree(pszEncodedVal);
                          pszStyleItem = (char*)malloc(strlen(pszStyle)+10+8);
                          sprintf(pszStyleItem, "wms_style_%s_title",pszStyle);
                          /* Title */
                          msOWSPrintEncodeMetadata(stream, 
                                                   &(map->layers[i].metadata), 
                                                   NULL, pszStyleItem, 
                                                   OWS_NOERR, 
                                        "          <Title>%s</Title>\n",
                                                   NULL);
                          free(pszStyleItem);

                          /* LegendURL */
                          pszStyleItem = (char*)malloc(strlen(pszStyle)+10+20);
                          sprintf(pszStyleItem, "style_%s_legendurl",
                                  pszStyle);
                          msOWSPrintURLType(stream, &(map->layers[i].metadata),
                                            "M", pszStyleItem, OWS_NOERR, NULL,
                                            "LegendURL", NULL, " width=\"%s\"",
                                            " height=\"%s\""," format=\"%s\"",
                                            "            <OnlineResource "
                                            "xlink:type=\"simple\""
                                            " xlink:href=\"%s\"/>\n          ",
                                            MS_FALSE, MS_FALSE, MS_FALSE, 
                                            MS_FALSE, MS_TRUE, NULL, NULL, 
                                            NULL, NULL, NULL, "          ");
                          free(pszStyleItem);
                      }
                  }

                  msIO_fprintf( stream,"        </Style>\n" );
 
                  free(pszStyle);
                  pszValue = strchr(pszValue, ',');
                  if(pszValue)  
                      pszValue++;
              }
              msIO_fprintf( stream, "      </StyleList>\n");
          }

          /* Dimension element */;
          pszCurrent = NULL;

          pszValue = msLookupHashTable(&(map->layers[i].metadata), 
                                       "wms_dimensionlist");
          pszCurrent = msLookupHashTable(&(map->layers[i].metadata), 
                                         "wms_dimension");
          while(pszValue != NULL)
          {
              /* Extract the dimension name from the list */
              pszDimension = strdup(pszValue);
              pszChar = strchr(pszDimension, ',');
              if(pszChar != NULL)
                  pszDimension[pszChar - pszDimension] = '\0';
              if(strcasecmp(pszDimension, "") == 0)
              {
                  free(pszDimension);
                  pszValue = strchr(pszValue, ',');
                  if(pszValue)  
                      pszValue++;
                  continue;
              }

              /* From the dimension list, extract the required dimension */
              msOWSGetDimensionInfo(&(map->layers[i]), pszDimension, 
                                    &pszDimUserValue, &pszDimUnits, 
                                    &pszDimDefault, &pszDimNearValue, 
                                    &pszDimUnitSymbol, &pszDimMultiValue);

              if(pszDimUserValue == NULL || pszDimUnits == NULL || 
                 pszDimUnitSymbol == NULL)
              {
                  free(pszDimension);
                  pszValue = strchr(pszValue, ',');
                  if(pszValue)  
                      pszValue++;
                  continue;
              }

              if(!bDimensionList)
              {
                  bDimensionList = 1;
                  msIO_fprintf( stream, "      <DimensionList>\n");
              }

              /* name */
              msIO_fprintf( stream, "        <Dimension name=\"%s\"", 
                            pszDimension);
              /* units */
              msIO_fprintf( stream, " units=\"%s\"",      pszDimUnits);
              /* unitSymbol */
              msIO_fprintf( stream, " unitSymbol=\"%s\"", pszDimUnitSymbol);
              /* userValue */
              msIO_fprintf( stream, " userValue=\"%s\"",  pszDimUserValue);
              /* default */
              if(pszDimDefault)
                  msIO_fprintf( stream, " default=\"%s\"", pszDimDefault);
              /* multipleValues */
              if(pszDimMultiValue)
                  msIO_fprintf(stream, " multipleValues=\"%s\"", 
                               pszDimMultiValue);
              /* nearestValue */
              if(pszDimNearValue)
                  msIO_fprintf( stream," nearestValue=\"%s\"",pszDimNearValue);
      
              if(pszCurrent && strcasecmp(pszDimension, pszCurrent) == 0)
                  msIO_fprintf( stream, " current=\"1\"");

              msIO_fprintf( stream, "/>\n");

              free(pszDimension);
              pszValue = strchr(pszValue, ',');
              if(pszValue)  
                  pszValue++;
          }

          if(bDimensionList)
              msIO_fprintf( stream, "      </DimensionList>\n");

          msIO_fprintf(stream, "    </Layer>\n");
      }
  }

  /* Close layer list */
  msIO_fprintf(stream, "  </LayerList>\n");
  /* Close Map Context */

  if(nVersion >= OWS_1_0_0)
  {
      msIO_fprintf(stream, "</ViewContext>\n");
  }
  else if(nVersion >= OWS_0_1_7)
  {
      msIO_fprintf(stream, "</View_Context>\n");
  }
  else /* 0.1.4 */
  {
      msIO_fprintf(stream, "</WMS_Viewer_Context>\n");
  }

  return MS_SUCCESS;
#else
  msSetError(MS_MAPCONTEXTERR, 
             "Not implemented since Map Context is not enabled.",
             "msWriteMapContext()");
  return MS_FAILURE;
#endif
}


