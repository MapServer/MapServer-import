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
 * $Log$
 * Revision 1.58.2.2  2004/09/12 18:32:30  julien
 * Set different metadata for WMS and WFS
 *
 * Revision 1.58.2.1  2004/09/07 20:15:54  julien
 * Multiple changes to support OWS Context
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

#define IS_OWS_CONTEXT(v)       ((v) & 0x01000000)
#define CONTEXT_VERSION(v)  ((v) & 0xFFFFFF)
#define MAKE_OWS_CONTEXT(v)     ((v) + 0x01000000)
#define MAKE_WMS_CONTEXT(v)     ((v) + 0x02000000)

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
 
  // open file
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
                                 hashTableObj *metadata, 
                                 const char *pszMetadata )
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
                                       const char *pszMetadata )
{
  char *pszValue, *pszDecodedVal;

  pszValue = (char*)CPLGetXMLValue( psRoot, pszXMLPath, NULL);
  if(pszValue != NULL)
  {
      if( metadata != NULL )
      {
          pszDecodedVal = strdup(pszValue);
          msDecodeHTMLEntities(pszDecodedVal);
          msInsertHashTable(metadata, pszMetadata, pszDecodedVal );
          free(pszDecodedVal);
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
  char *pszValue, *pszDecodedVal;

  pszValue = (char*)CPLGetXMLValue( psRoot, pszXMLPath, NULL);
  if(pszValue != NULL)
  {
      if( pszField != NULL )
      {
          pszDecodedVal = strdup(pszValue);
          msDecodeHTMLEntities(pszDecodedVal);
          *pszField = strdup(pszDecodedVal);
          free(pszDecodedVal);
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
** msLoadMapContextURLElements
**
** Take a Node and get the width, height, format and href from it.
** Then put this info in metadatas.
*/
int msLoadMapContextURLElements( CPLXMLNode *psRoot, hashTableObj *metadata, 
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
                                    const char *pszXMLName, 
                                    const char *pszMetadataName, 
                                    const char *pszHashDelimiter)
{
  char *pszHash, *pszXMLValue, *pszMetadata;

  if(psRoot == NULL || psRoot->psChild == NULL || 
     metadata == NULL || pszMetadataName == NULL || pszXMLName == NULL)
      return MS_FAILURE;

  // Pass from KeywordList to Keyword level
  psRoot = psRoot->psChild;

  // Loop on all elements and append keywords to the hash table
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

    // Contact Person primary
    msGetMapContextXMLHashValue(psRoot, 
                              "ContactPersonPrimary.ContactPerson", 
                              metadata, "wms_contactperson");
  msGetMapContextXMLHashValue(psRoot, 
                              "ContactPersonPrimary.ContactOrganization", 
                              metadata, "wms_contactorganization");
  // Contact Position
  msGetMapContextXMLHashValue(psRoot, 
                              "ContactPosition", 
                              metadata, "wms_contactposition");
  // Contact Address
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

  // Others
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
int msLoadMapContextLayerFormat(CPLXMLNode *psFormat, layerObj *layer, 
                                const char *pszMFormat)
{
  char *pszValue, *pszValue1, *pszHash, *pszMFormatList;

  pszMFormatList = (char*)malloc(strlen(pszMFormat)+6);
  sprintf(pszMFormatList, "%slist", pszMFormat);

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
      // wms_format
      pszValue1 = (char*)CPLGetXMLValue(psFormat, 
                                        "current", NULL);
      if(pszValue1 != NULL && 
         (strcasecmp(pszValue1, "1") == 0))
          msInsertHashTable(&(layer->metadata), 
                            pszMFormat, pszValue);
      // wms_formatlist
      pszHash = msLookupHashTable(&(layer->metadata), pszMFormatList);
      if(pszHash != NULL)
      {
          pszValue1 = (char*)malloc(strlen(pszHash)+
                                    strlen(pszValue)+2);
          sprintf(pszValue1, "%s,%s", pszHash, pszValue);
          msInsertHashTable(&(layer->metadata), pszMFormatList, pszValue1);
          free(pszValue1);
      }
      else
          msInsertHashTable(&(layer->metadata), pszMFormatList, pszValue);
  }

  /* Make sure selected format is supported or select another
   * supported format.  Note that we can efficiently do this
   * only for GIF/PNG/JPEG, can't try to handle all GDAL
   * formats.
   */
  pszValue = msLookupHashTable(&(layer->metadata), pszMFormat);

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

      pszValue = msLookupHashTable(&(layer->metadata), pszMFormatList);

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
              msInsertHashTable(&(layer->metadata), pszMFormat, papszList[i]);
              break;
          }
      }
      if(papszList)
          msFreeCharArray(papszList, numformats);

  } /* end if unsupported format */

  free(pszMFormatList);

  return MS_SUCCESS;
}

int msLoadMapContextLayerStyle(CPLXMLNode *psStyle, layerObj *layer, 
                               int nStyle, const char *pszMStyle)
{
  char *pszValue, *pszValue1, *pszValue2;
  char *pszHash, *pszStyle=NULL, *pszStyleName, *pszMStyleList;

  pszMStyleList = (char*)malloc(strlen(pszMStyle)+5);
  sprintf(pszMStyleList, "%slist", pszMStyle);

  pszStyleName =(char*)CPLGetXMLValue(psStyle,"Name",NULL);
  if(pszStyleName == NULL)
  {
       pszStyleName = (char*)malloc(15);
       sprintf(pszStyleName, "Style{%d}", nStyle);
  }
  else
      pszStyleName = strdup(pszStyleName);

  // wms_style
  pszValue = (char*)CPLGetXMLValue(psStyle,"current",NULL);
  if(pszValue != NULL && 
     (strcasecmp(pszValue, "1") == 0))
      msInsertHashTable(&(layer->metadata), pszMStyle, pszStyleName);
  // wms_stylelist
  pszHash = msLookupHashTable(&(layer->metadata), pszMStyleList);
  if(pszHash != NULL)
  {
      pszValue1 = (char*)malloc(strlen(pszHash)+
                                strlen(pszStyleName)+2);
      sprintf(pszValue1, "%s,%s", pszHash, pszStyleName);
      msInsertHashTable(&(layer->metadata), pszMStyleList, pszValue1);
      free(pszValue1);
  }
  else
      msInsertHashTable(&(layer->metadata), pszMStyleList, pszStyleName);

  // Title
  pszStyle = (char*)malloc(strlen(pszStyleName)+20);
  sprintf(pszStyle, "%s_%s_title", pszMStyle, pszStyleName);

  if( msGetMapContextXMLHashValue(psStyle, "Title", &(layer->metadata), 
                                  pszStyle) == MS_FAILURE )
      msInsertHashTable(&(layer->metadata), pszStyle, layer->name);

  free(pszStyle);

  // SLD
  pszStyle = (char*)malloc(strlen(pszStyleName)+15);
  sprintf(pszStyle, "%s_%s_sld", pszMStyle, pszStyleName);
  
  msGetMapContextXMLHashValueDecode( psStyle, "SLD.OnlineResource.xlink:href", 
                                     &(layer->metadata), pszStyle );
  free(pszStyle);

  // LegendURL
  pszStyle = (char*) malloc(strlen(pszStyleName) + 25);

  sprintf( pszStyle, "%s_%s_legendurl", pszMStyle, pszStyleName);
  msLoadMapContextURLElements( CPLGetXMLNode(psStyle, "LegendURL"), 
                               &(layer->metadata), pszStyle );

  free(pszStyle);

  free(pszStyleName);

  //
  // Add the stylelist to the layer connection
  //
  if(msLookupHashTable(&(layer->metadata), pszMStyleList) == NULL)
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
          msInsertHashTable(&(layer->metadata), pszMStyleList, pszValue1);
      }
      free(pszValue);
  }

  //
  // Add the style to the layer connection
  //
  if(msLookupHashTable(&(layer->metadata), pszMStyle) == NULL)
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
          msInsertHashTable(&(layer->metadata), pszMStyle, pszValue1);
      }
      free(pszValue);
  }

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

  // Projection
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

  // Extent
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

  // Title
  if( msGetMapContextXMLHashValue(psGeneral, "Title", 
                              &(map->web.metadata), "ows_title") == MS_FAILURE)
  {
      if ( IS_OWS_CONTEXT(nVersion) || 
           CONTEXT_VERSION(nVersion) >= OWS_1_0_0 )
         msDebug("Mandatory data General.Title missing in %s.", filename);
      else
      {
          if( msGetMapContextXMLHashValue(psGeneral, "gml:name", 
                             &(map->web.metadata), "ows_title") == MS_FAILURE )
          {
              if( CONTEXT_VERSION(nVersion) < OWS_0_1_7 )
                msDebug("Mandatory data General.Title missing in %s.", filename);
              else
                msDebug("Mandatory data General.gml:name missing in %s.", 
                        filename);
          }
      }
  }

  // Name
  if( IS_OWS_CONTEXT(nVersion) || CONTEXT_VERSION(nVersion) >= OWS_1_0_0 )
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
  // Keyword
  if( IS_OWS_CONTEXT(nVersion) || CONTEXT_VERSION(nVersion) >= OWS_1_0_0 )
  {
      msLoadMapContextListInMetadata( 
          CPLGetXMLNode(psGeneral, "KeywordList"),
          &(map->web.metadata), "KEYWORD", "ows_keywordlist", "," );
  }
  else
    msGetMapContextXMLHashValue(psGeneral, "Keywords", 
                                &(map->web.metadata), "ows_keywordlist");

  // Window
  pszValue1 = (char*)CPLGetXMLValue(psGeneral,"Window.width",NULL);
  pszValue2 = (char*)CPLGetXMLValue(psGeneral,"Window.height",NULL);
  if(pszValue1 != NULL && pszValue2 != NULL)
  {
      map->width = atoi(pszValue1);
      map->height = atoi(pszValue2);
  }

  // Abstract
  if( msGetMapContextXMLHashValue( psGeneral, 
                                   "Abstract", &(map->web.metadata), 
                                   "ows_abstract") == MS_FAILURE )
  {
      msGetMapContextXMLHashValue( psGeneral, "gml:description", 
                                   &(map->web.metadata), "ows_abstract");
  }

  // DataURL
  msGetMapContextXMLHashValueDecode(psGeneral, 
                                   "DataURL.OnlineResource.xlink:href",
                                   &(map->web.metadata), "ows_dataurl");

  // LogoURL
  // The logourl have a width, height, format and an URL
  msLoadMapContextURLElements( CPLGetXMLNode(psGeneral, "LogoURL"), 
                               &(map->web.metadata), "ows_logourl" );

  // DescriptionURL
  // The descriptionurl have a width, height, format and an URL
  msLoadMapContextURLElements( CPLGetXMLNode(psGeneral, 
                                             "DescriptionURL"), 
                               &(map->web.metadata), "ows_descriptionurl" );

  // Contact Info
  msLoadMapContextContactInfo( 
      CPLGetXMLNode(psGeneral, "ContactInformation"), 
      &(map->web.metadata) );

  return MS_SUCCESS;
}

/*
** msLoadMapContextAbstractView
**
** Load layer informations
*/
int msLoadMapContextAbstractView(layerObj *layer, CPLXMLNode *psLayer, 
                                 int nVersion, char *filename,
                                 // List of metadata names
                                 const char *pszMName,
                                 const char *pszMTitle,
                                 const char *pszMAbstract,
                                 const char *pszMDataURL,
                                 const char *pszMMetadataURL,
                                 const char *pszMOnlineResource,
                                 const char *pszMServerVersion,
                                 const char *pszMSRS,
                                 const char *pszMFormat,
                                 const char *pszMStyle)
{
  char *pszProj=NULL;
  char *pszValue, *pszEncodedVal;
  char *pszHash, *pszName=NULL;
  CPLXMLNode *psFormatList, *psFormat, *psStyleList, *psStyle, *psServer;
  int nStyle;  
  
  // Status
  pszValue = (char*)CPLGetXMLValue(psLayer, "hidden", "1");
  if((pszValue != NULL) && (atoi(pszValue) == 0))
      layer->status = MS_ON;
  else
      layer->status = MS_OFF;

  // Name and Title
  pszValue = (char*)CPLGetXMLValue(psLayer, "Name", NULL);
  if(pszValue != NULL)
  {
      msInsertHashTable( &(layer->metadata), pszMName, pszValue );

      pszName = (char*)malloc(sizeof(char)*(strlen(pszValue)+10));
      sprintf(pszName, "l%d:%s", layer->index, pszValue);
      layer->name = strdup(pszName);
      free(pszName);
  }
  else
  {
      pszName = (char*)malloc(sizeof(char)*10);
      sprintf(pszName, "l%d:", layer->index);
      layer->name = strdup(pszName);
      free(pszName);
  }

  if(msGetMapContextXMLHashValue(psLayer, "Title", &(layer->metadata), 
                                 pszMTitle) == MS_FAILURE)
  {
      if(msGetMapContextXMLHashValue(psLayer, "Server.title", 
                          &(layer->metadata), pszMTitle) == MS_FAILURE)
      {
          msDebug("Mandatory data Layer.Title missing in %s.", filename);
      }
  }

  // Abstract
  msGetMapContextXMLHashValue(psLayer, "Abstract", &(layer->metadata), 
                              pszMAbstract);

  // DataURL
  if(!IS_OWS_CONTEXT(nVersion) && CONTEXT_VERSION(nVersion) <= OWS_0_1_4)
  {
      msGetMapContextXMLHashValueDecode(psLayer, 
                                        "DataURL.OnlineResource.xlink:href",
                                        &(layer->metadata), pszMDataURL);
  }
  else
  {
      // The DataURL have a width, height, format and an URL
      // Width and height are not used, but they are included to
      // be consistent with the spec.
      msLoadMapContextURLElements( CPLGetXMLNode(psLayer, "DataURL"), 
                                           &(layer->metadata), pszMDataURL );
  }

  // The MetadataURL have a width, height, format and an URL
  // Width and height are not used, but they are included to
  // be consistent with the spec.
  msLoadMapContextURLElements( CPLGetXMLNode(psLayer, "MetadataURL"), 
                                       &(layer->metadata), pszMMetadataURL );

  //
  // MinScale && MaxScale
  //
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

  //
  // Server
  //
  // Put server online resource in connection and in wms_onlineresource
  //
  if(IS_OWS_CONTEXT(nVersion))
  {
      //
      // The OWS version should carry al the XML because it's too complex. :S
      //
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
                                            &(layer->metadata), 
                                            pszMOnlineResource);
              
          // Get the Server information
          psServer = CPLGetXMLNode(psLayer, "Server");
          if(psServer != NULL && psServer->psChild != NULL)
          {
              psServer = psServer->psChild;
              while(psServer->eType != CXT_Element)
              {
                  psServer = psServer->psNext;
              }

              pszEncodedVal = NULL;
              pszValue = CPLSerializeXMLTree(psServer);
              if(pszValue != NULL)
              {
                  pszEncodedVal = msEncodeHTMLEntities( pszValue );
                  free(pszValue);
              }
              if(pszEncodedVal != NULL)
              {
                  pszValue = (char*)malloc(strlen(pszMOnlineResource)+5);
                  sprintf(pszValue, "%s_xml", pszMOnlineResource);
                  msInsertHashTable( &(layer->metadata), pszValue, 
                                     pszEncodedVal );
                  free(pszValue);
                  free(pszEncodedVal);
              }
          }
      }
  }
  else if(CONTEXT_VERSION(nVersion) >= OWS_0_1_4)
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
                                     &(layer->metadata), pszMOnlineResource);
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
                                     &(layer->metadata), pszMOnlineResource);
      }
  }

  //
  // Put server version in wms_server_version
  //
  if(IS_OWS_CONTEXT(nVersion) || CONTEXT_VERSION(nVersion) >= OWS_0_1_4)
  {
      if(msGetMapContextXMLHashValue(psLayer, "Server.version", 
                      &(layer->metadata), pszMServerVersion) == MS_FAILURE)
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
                      &(layer->metadata), pszMServerVersion) == MS_FAILURE)
      {
          msSetError(MS_MAPCONTEXTERR, 
                     "Mandatory data Server.wmtver missing in %s.",
                     "msLoadMapContext()", filename);
          return MS_FAILURE;
      }
  }

  // Projection
  msLoadMapContextListInMetadata( psLayer, &(layer->metadata), 
                                  "SRS", pszMSRS, " " );

  pszHash = msLookupHashTable(&(layer->metadata), pszMSRS);
  if(((pszHash == NULL) || (strcasecmp(pszHash, "") == 0)) && 
     layer->map->projection.numargs != 0)
  {
      pszProj = layer->map->projection.args[layer->map->projection.numargs-1];

      if(pszProj != NULL)
      {
          if(strncasecmp(pszProj, "AUTO:", 5) == 0)
          {
              msInsertHashTable(&(layer->metadata), pszMSRS, pszProj);
          }
          else
          {
              if(strlen(pszProj) > 10)
              {
                  pszProj = (char*) malloc(sizeof(char) * (strlen(pszProj)));
                  sprintf( pszProj, "EPSG:%s", 
                           layer->map->projection.args[
                               layer->map->projection.numargs-1]+10);
                  msInsertHashTable(&(layer->metadata), pszMSRS, pszProj);
              }
              else
              {
                  msDebug("Unable to set data for layer %s from this"
                          " value %s.", pszMSRS, pszProj);
              }
          }
      }
  }

  //
  // Format
  //
  if( IS_OWS_CONTEXT(nVersion) || CONTEXT_VERSION(nVersion) >= OWS_0_1_4 )
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
          msLoadMapContextLayerFormat(psFormat, layer, pszMFormat);
      }
                   
  } /* end FormatList parsing */

  // Style
  if( IS_OWS_CONTEXT(nVersion) || CONTEXT_VERSION(nVersion) >= OWS_0_1_4 )
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
              msLoadMapContextLayerStyle(psStyle, layer, nStyle, pszMStyle);
          }
      }
  }

  return MS_SUCCESS;
}

/*
** msLoadMapContextLayer
**
** Load a Layer block from a MapContext document
*/
int msLoadMapContextLayer(mapObj *map, CPLXMLNode *psLayer,int nVersion,
                          char *filename)
{
  char *pszValue;
  layerObj *layer;

  // Init new layer
  layer = &(map->layers[map->numlayers]);
  initLayer(layer, map);
  layer->map = (mapObj *)map;
  layer->type = MS_LAYER_RASTER;
  layer->connectiontype = MS_WMS;
  /* save the index */
  map->layers[map->numlayers].index = map->numlayers;
  map->layerorder[map->numlayers] = map->numlayers;
  map->numlayers++;

  if( msLoadMapContextAbstractView(layer, psLayer, nVersion, filename,
                                   "wms_name",
                                   "wms_title",
                                   "wms_abstract",
                                   "wms_dataurl",
                                   "wms_metadataurl",
                                   "wms_onlineresource",
                                   "wms_server_version",
                                   "wms_srs",
                                   "wms_format",
                                   "wms_style") == MS_FAILURE)
      return MS_FAILURE;

  // Get the queryable attribute
  pszValue = (char*)CPLGetXMLValue(psLayer, "queryable", "0");
  if(pszValue !=NULL && atoi(pszValue) == 1)
      layer->template = strdup("ttt");

  return MS_SUCCESS;
}

/*
** msLoadMapContextLayer
**
** Load a Layer block from a MapContext document
*/
int msLoadMapContextFeature(mapObj *map, CPLXMLNode *psLayer,int nVersion,
                          char *filename)
{
  CPLXMLNode *psFilter=NULL;
  layerObj *layer;
  char *pszEncodedVal;

  // Init new layer
  layer = &(map->layers[map->numlayers]);
  initLayer(layer, map);
  layer->map = (mapObj *)map;
  layer->type = MS_LAYER_RASTER;
  layer->connectiontype = MS_WFS;
  /* save the index */
  map->layers[map->numlayers].index = map->numlayers;
  map->layerorder[map->numlayers] = map->numlayers;
  map->numlayers++;

  if( msLoadMapContextAbstractView(layer, psLayer, nVersion, filename,
                                   "wfs_typename",
                                   "wfs_title",
                                   "wfs_abstract",
                                   "ows_dataurl",
                                   "ows_metadataurl",
                                   "wfs_onlineresource",
                                   "wfs_version",
                                   "wfs_srs", 
                                   "ows_format",
                                   "ows_style") == MS_FAILURE )
      return MS_FAILURE;

  // Get the Filter attribute
  psFilter = CPLGetXMLNode(psLayer, "ogc:Filter");
  if(psFilter != NULL)
  {
      psFilter = psFilter->psChild;
      while(psFilter->eType != CXT_Element)
      {
          psFilter = psFilter->psNext;
      }
      pszEncodedVal = msEncodeHTMLEntities( CPLSerializeXMLTree(psFilter) );
      if(pszEncodedVal != NULL)
      {
          msInsertHashTable( &(layer->metadata), "wfs_filter", pszEncodedVal );
          free(pszEncodedVal);
      }
  }

  return MS_SUCCESS;
}

#endif

/* msLoadMapContext()
**
** Get a mapfile from a OGC Web Map Context format
**
** Take a map object and a file in arguments
*/
int msLoadMapContext(mapObj *map, char *filename)
{
#if defined(USE_WMS_LYR) && defined(USE_OGR)
  char *pszWholeText, *pszValue;
  CPLXMLNode *psRoot, *psMapContext, *psLayer, *psLayerList, *psChild;
  char szPath[MS_MAXPATHLEN];
  int nVersion=-1;
  char szVersionBuf[OWS_VERSION_MAXLEN];

  //
  // Load the raw XML file
  //
  
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
      ( strstr( pszWholeText, "<ViewContext" ) == NULL ) &&
      ( strstr( pszWholeText, "<OWSContext" ) == NULL ) )
    
  {
      free( pszWholeText );
      msSetError( MS_MAPCONTEXTERR, "Not a Map Context file (%s)", 
                  "msLoadMapContext()", filename );
      return MS_FAILURE;
  }

  //
  // Convert to XML parse tree.
  //
  psRoot = CPLParseXMLString( pszWholeText );
  free( pszWholeText );

  // We assume parser will report errors via CPL.
  if( psRoot == NULL || psRoot->psNext == NULL )
  {
      msSetError( MS_MAPCONTEXTERR, "Invalid XML file (%s)", 
                  "msLoadMapContext()", filename );
      if(psRoot != NULL)
          CPLDestroyXMLNode(psRoot);

      return MS_FAILURE;
  }

  //
  // Valid the MapContext file and get the root of the document
  //
  psChild = psRoot;
  psMapContext = NULL;
  while( psChild != NULL )
  {
      if( psChild->eType == CXT_Element && 
          (EQUAL(psChild->pszValue,"WMS_Viewer_Context") ||
           EQUAL(psChild->pszValue,"View_Context") ||
           EQUAL(psChild->pszValue,"ViewContext") || 
           EQUAL(psChild->pszValue,"OWSContext")) )
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

  // Fetch document version number
  pszValue = (char*)CPLGetXMLValue(psMapContext, 
                                   "version", NULL);
  if( !pszValue )
  {
      msDebug( "msLoadMapContext(): Mandatory data version missing in %s, assuming 0.1.4.",
               filename );
      pszValue = "0.1.4";
  }

  nVersion = msOWSParseVersionString(pszValue);

  if( EQUAL( psMapContext->pszValue, "OWSContext" ) )
      nVersion = MAKE_OWS_CONTEXT(nVersion);
  else
      nVersion = MAKE_WMS_CONTEXT(nVersion);

  // Make sure this is a supported version
  switch ( CONTEXT_VERSION(nVersion) )
  {
    case OWS_0_0_7:
    case OWS_0_1_2:
    case OWS_0_1_4:
    case OWS_0_1_7:
    case OWS_1_0_0:
      // All is good, this is a supported version.
      break;
    default:
      // Not a supported version
      msSetError(MS_MAPCONTEXTERR, 
                 "This version of Map Context is not supported (%s).",
                 "msLoadMapContext()", pszValue);
      CPLDestroyXMLNode(psRoot);
      return MS_FAILURE;
  }

  // Reformat and save Version in metadata
  if( IS_OWS_CONTEXT(nVersion) )
      msInsertHashTable( &(map->web.metadata), "ows_context_version",
                         msOWSGetVersionString( CONTEXT_VERSION(nVersion), 
                                                szVersionBuf));
  else
      msInsertHashTable( &(map->web.metadata), "wms_context_version",
                         msOWSGetVersionString( CONTEXT_VERSION(nVersion), 
                                                szVersionBuf));

  if( !IS_OWS_CONTEXT(nVersion) && 
      CONTEXT_VERSION(nVersion) >= OWS_0_1_7 && 
      CONTEXT_VERSION(nVersion) < OWS_1_0_0)
  {
      if( msGetMapContextXMLHashValue(psMapContext, "fid", 
                           &(map->web.metadata), "wms_context_fid") == MS_FAILURE )
      {
          msDebug("Mandatory data fid missing in %s.", filename);
      }
  }

  //
  // Load the General bloc
  //
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

  //
  // Load the bloc LayerList
  //
  if( IS_OWS_CONTEXT(nVersion) )
      psLayerList = CPLGetXMLNode(psMapContext, "ResourceList");
  else
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
                                        filename) == MS_FAILURE )
              {
                  CPLDestroyXMLNode(psRoot);
                  return MS_FAILURE;
              }
          }
          if( IS_OWS_CONTEXT(nVersion) )
          {
              if(EQUAL(psLayer->pszValue, "FeatureType"))
              {
                  // We only support WFS service for now.
                  pszValue = (char*) CPLGetXMLValue(psLayer, 
                                                    "Server.service", NULL);
                  if( pszValue != NULL && EQUAL(pszValue, "OGC:WFS") )
                  {
                      if( msLoadMapContextFeature(map, psLayer, nVersion, 
                                                  filename) == MS_FAILURE )
                      {
                          CPLDestroyXMLNode(psRoot);
                          return MS_FAILURE;
                      }
                  }
              }
          }
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


//
// Save functions
//
#if defined(USE_WMS_LYR) && defined(USE_OGR)

/*
** msWriteMapContextURLElement
**
** Write the XML online resource elements from a given metadata in a stream.
*/
int msWriteMapContextURLElements( FILE *stream, hashTableObj *metadata, 
                                  const char *pszNodeName, 
                                  const char *namespaces, 
                                  const char *pszMetadata, 
                                  const char *pszTabSpace)
{
  char *pszMetadataName;

  if( stream == NULL || pszMetadata == NULL || pszNodeName == NULL || 
      pszTabSpace == NULL )
      return MS_FAILURE;

  pszMetadataName = (char*) malloc( strlen(pszMetadata) + 10 );
  sprintf( pszMetadataName, "%s_href", pszMetadata );

  if( msOWSLookupMetadata(metadata, namespaces, pszMetadataName) == NULL )
      return MS_FAILURE;

  fprintf( stream, "%s<%s", pszTabSpace, pszNodeName);

  sprintf( pszMetadataName, "%s_width", pszMetadata );
  msOWSPrintEncodeMetadata(stream, metadata, 
                           namespaces, pszMetadataName, OWS_NOERR,
                           " width=\"%s\"", NULL);

  sprintf( pszMetadataName, "%s_height", pszMetadata );
  msOWSPrintEncodeMetadata(stream, metadata, 
                           namespaces, pszMetadataName, OWS_NOERR,
                           " height=\"%s\"", NULL);

  sprintf( pszMetadataName, "%s_format", pszMetadata );
  msOWSPrintEncodeMetadata(stream, metadata, 
                           namespaces, pszMetadataName, OWS_NOERR,
                           " format=\"%s\"", NULL);
  fprintf( stream, ">\n");

  sprintf( pszMetadataName, "%s_href", pszMetadata );
  fprintf( stream, "%s  <OnlineResource xlink:type=\"simple\" ", pszTabSpace);
  msOWSPrintEncodeMetadata(stream, metadata, 
                           namespaces, pszMetadataName, OWS_NOERR,
                           "xlink:href=\"%s\"/>\n",
                           NULL);

  fprintf( stream, "%s</%s>\n", pszTabSpace, pszNodeName);

  return MS_SUCCESS;
}

/*
** msWriteMapContextGeneral
**
** Save the general block in a given stream.
*/
int msWriteMapContextGeneral(FILE *stream, mapObj *map, int nVersion)
{
  char *pszValue;
  const char *pszConst;

  // set the General information
  fprintf( stream, "  <General>\n" );

  // Window
  if( map->width != -1 || map->height != -1 )
      fprintf( stream, "    <Window width=\"%d\" height=\"%d\"/>\n", 
               map->width, map->height );

  // Bounding box corners and spatial reference system
  pszConst = msGetEPSGProj(&(map->projection), &(map->web.metadata), MS_TRUE);
  fprintf( stream, 
          "    <!-- Bounding box corners and spatial reference system -->\n" );
  if(!pszConst || (strcasecmp(pszConst, "(null)") == 0))
              fprintf(stream, "<!-- WARNING: Mandatory data 'projection' was missing in this context. -->\n");

  fprintf( stream, "    <BoundingBox SRS=\"%s\" "
           "minx=\"%f\" miny=\"%f\" maxx=\"%f\" maxy=\"%f\"/>\n", 
           pszConst, map->extent.minx, map->extent.miny, 
           map->extent.maxx, map->extent.maxy );

  // Title, name
  if( !IS_OWS_CONTEXT(nVersion) && 
      CONTEXT_VERSION(nVersion) >= OWS_0_1_7 && 
      CONTEXT_VERSION(nVersion) < OWS_1_0_0 )
  {
      fprintf( stream, "    <gml:name>%s</gml:name>\n", map->name );
  }
  else 
  {
      if ( !IS_OWS_CONTEXT(nVersion) && 
           CONTEXT_VERSION(nVersion) < OWS_0_1_7)
        fprintf( stream, "    <Name>%s</Name>\n", map->name );

      fprintf( stream, "    <!-- Title of Context -->\n" );
      msOWSPrintMetadata(stream, &(map->web.metadata), 
                         "OMF", "title", OWS_WARN,
                         "    <Title>%s</Title>\n", map->name);
  }

  //keyword
  if ( IS_OWS_CONTEXT(nVersion) || CONTEXT_VERSION(nVersion) >= OWS_1_0_0 )
  {
      if (msOWSLookupMetadata(&(map->web.metadata),"OMF", "keywordlist")!=NULL)
      {
          char **papszKeywords;
          int nKeywords, iKey;

          pszValue = (char*)msOWSLookupMetadata(&(map->web.metadata), "OMF", 
                                                "keywordlist");
          papszKeywords = split(pszValue, ',', &nKeywords);
          if(nKeywords > 0 && papszKeywords)
          {
              fprintf( stream, "    <KeywordList>\n");
              for(iKey=0; iKey<nKeywords; iKey++)
              { 
                  fprintf( stream, "      <Keyword>%s</Keyword>\n", 
                          papszKeywords[iKey]);
              }
              fprintf( stream, "    </KeywordList>\n");
          }
      }
  }
  else
    msOWSPrintMetadataList(stream, &(map->web.metadata), "OMF", "keywordlist", 
                           "    <Keywords>\n", "    </Keywords>\n",
                           "      %s\n", NULL);

  //abstract
  if( !IS_OWS_CONTEXT(nVersion) && 
      CONTEXT_VERSION(nVersion) >= OWS_0_1_7 && 
      CONTEXT_VERSION(nVersion) < OWS_1_0_0 )
  {
      msOWSPrintMetadata(stream, &(map->web.metadata), 
                         "OMF", "abstract", OWS_NOERR,
                         "    <gml:description>%s</gml:description>\n", NULL);
  }
  else
  {
      msOWSPrintMetadata(stream, &(map->web.metadata), 
                         "OMF", "abstract", OWS_NOERR,
                         "    <Abstract>%s</Abstract>\n", NULL);
  }

  // DataURL
  msOWSPrintEncodeMetadata(stream, &(map->web.metadata), 
                           "OMF", "dataurl", OWS_NOERR,
                "    <DataURL>\n      <OnlineResource xlink:type=\"simple\" xlink:href=\"%s\"/>\n    </DataURL>\n", NULL);

  // LogoURL
  // The LogoURL have a width, height, format and an URL
  msWriteMapContextURLElements(stream, &(map->web.metadata), 
                                   "LogoURL", "OMF", "logourl", "    ");
  
  // DescriptionURL
  // The DescriptionURL have a width, height, format and an URL
  // The metadata is structured like this: "width height format url"
  if( IS_OWS_CONTEXT(nVersion) || CONTEXT_VERSION(nVersion) >= OWS_1_0_0 )
  {
      msWriteMapContextURLElements(stream, &(map->web.metadata), 
                                   "DescriptionURL", 
                                   "OMF", "descriptionurl", "    ");
  }

  // Contact Info
  msOWSPrintContactInfo( stream, "    ", OWS_1_1_0, &(map->web.metadata) );

  // Close General
  fprintf( stream, "  </General>\n" );

  return MS_SUCCESS;

}

/*
** msWriteMapContextAbstractView
**
** Save the generic layer componnents in a given stream.
*/
int msWriteMapContextAbstractView(FILE *stream, layerObj *layer, 
                                  const char *namespaces, int nVersion)
{
  char *pszValue, *pszChar,*pszSLD=NULL,*pszURL,*pszSLD2=NULL;
  char *pszStyle, *pszCurrent, *pszStyleItem;
  char *pszEncodedVal;

  // 
  // Server definition
  //
  if( IS_OWS_CONTEXT(nVersion) )
  {
      if(layer->connectiontype == MS_WFS)
          msOWSPrintMetadata(stream, &(layer->metadata), 
                             namespaces, "version", OWS_WARN,
                             "      <Server service=\"OGC:WFS\" version=\"%s\" ",
                             "1.1.0");
      else if(layer->connectiontype == MS_WMS)
          msOWSPrintMetadata(stream, &(layer->metadata), 
                             namespaces, "server_version", OWS_WARN,
                             "      <Server service=\"OGC:WMS\" version=\"%s\" ",
                             "1.1.0");
  }
  else
      msOWSPrintMetadata(stream, &(layer->metadata), 
                         namespaces, "server_version", OWS_WARN,
                         "      <Server service=\"WMS\" version=\"%s\" ",
                         "1.1.0");
  if(layer->name)
      msOWSPrintMetadata(stream, &(layer->metadata), 
                         namespaces, "title", OWS_NOERR, 
                         "title=\"%s\">\n", layer->name);
  else
  {
      msOWSPrintMetadata(stream, &(layer->metadata), 
                         namespaces, "title", OWS_NOERR, 
                         "title=\"%s\">\n", "");
  }

  // Get base url of the online resource to be the default value
  pszValue = NULL;
  if( IS_OWS_CONTEXT(nVersion) )
  {
      pszValue = (char*)msOWSLookupMetadata( &(layer->metadata), namespaces, 
                                             "onlineresource_xml");
      if(pszValue != NULL)
      {
          pszEncodedVal = strdup(pszValue);
          msDecodeHTMLEntities(pszEncodedVal);
          fprintf(stream, "%s", pszEncodedVal);
          free(pszEncodedVal);
          fprintf(stream, "      </Server>\n");
      }
  }

  if(pszValue == NULL)
  {
      if(layer->connection)
          pszValue = strdup( layer->connection );
      else
          pszValue = strdup( "" );
      pszChar = strchr(pszValue, '?');
      if( pszChar )
          pszValue[pszChar - pszValue] = '\0';
      if(msOWSPrintEncodeMetadata(stream, &(layer->metadata), 
                                  namespaces, "onlineresource", OWS_WARN,
                                  "        <OnlineResource xlink:type=\"simple\" xlink:href=\"%s\"/>\n",
                                  pszValue) == OWS_WARN)
          fprintf(stream, "<!-- onlineresource not set, using "
                  "base URL , but probably not what you want -->\n");
      fprintf(stream, "      </Server>\n");
      if(pszValue)
          free(pszValue);
  }

  //
  // Layer information
  //
  if(layer->connectiontype == MS_WFS)
      msOWSPrintMetadata(stream, &(layer->metadata), namespaces, "typename", 
                         OWS_WARN, "      <Name>%s</Name>\n", layer->name);
  else
      msOWSPrintMetadata(stream, &(layer->metadata), namespaces, "name", 
                         OWS_WARN, "      <Name>%s</Name>\n", layer->name);

  msOWSPrintMetadata(stream, &(layer->metadata), 
                     namespaces, "title", OWS_WARN, 
                     "      <Title>%s</Title>\n", 
                     layer->name);
  msOWSPrintMetadata(stream, &(layer->metadata), 
                     namespaces, "abstract", OWS_NOERR, 
                     "      <Abstract>%s</Abstract>\n", 
                     NULL);

  //
  // Layer min/max scale 
  //
  if( IS_OWS_CONTEXT(nVersion) )
  {
      if( layer->minscale > -1 )
          fprintf(stream, "      <sld:MinScaleDenominator>%g"
                  "</sld:MinScaleDenominator>\n", 
                  layer->minscale);
      if( layer->maxscale > -1 )
          fprintf(stream, "      <sld:MaxScaleDenominator>%g"
                  "</sld:MaxScaleDenominator>\n", 
                  layer->maxscale);
  }

  // Layer SRS
  pszValue = (char*)msGetEPSGProj(&(layer->projection), 
                                  &(layer->metadata), MS_FALSE);
  if(pszValue && (strcasecmp(pszValue, "(null)") != 0))
      fprintf(stream, "      <SRS>%s</SRS>\n", pszValue);

  // DataURL
  if( !IS_OWS_CONTEXT(nVersion) && 
      CONTEXT_VERSION(nVersion) <= OWS_0_1_4 )
  {
      msOWSPrintMetadata(stream, &(layer->metadata), 
                         namespaces, "dataurl", OWS_NOERR, 
                         "      <DataURL>%s</DataURL>\n", 
                         NULL);
  }
  else
  {
      // The DataURL have a width, height, format and an URL
      // The metadata will be structured like this: 
      // "width height format url"
      // Note: in version 0.1.7 the width and height are not included 
      // in the Context file, but they are included in the metadata for
      // for consistency with the URLType.
      msWriteMapContextURLElements(stream, &(layer->metadata), "DataURL", 
                                   namespaces , "dataurl", "      ");
  }

  // MetadataURL
  // The MetadataURL have a width, height, format and an URL
  // The metadata will be structured like this: 
  // "width height format url"
  pszURL = msLookupHashTable(&(layer->metadata),
                             "wms_metadataurl_href");
  if(pszURL != NULL)
  {
      msWriteMapContextURLElements(stream, &(layer->metadata), 
                                   "MetadataURL", namespaces, "metadataurl", 
                                   "      ");
  }

  // Format
  if(msOWSLookupMetadata(&(layer->metadata), namespaces, "formatlist") == NULL)
  {
      pszURL = NULL;
      if(layer->connection)
          pszURL = strdup( layer->connection );
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
              fprintf( stream, "      <FormatList>\n");
              fprintf(stream,"        <Format>%s</Format>\n",pszValue);
              fprintf( stream, "      </FormatList>\n");
          }
      }
      if(pszURL)
          free(pszURL);
  }
  else
  {
      char **papszFormats;
      int numFormats, nForm;

      pszValue = (char*)msOWSLookupMetadata(&(layer->metadata), namespaces, 
                                     "formatlist");
      pszCurrent = (char*)msOWSLookupMetadata(&(layer->metadata), namespaces,
                                              "format");

      papszFormats = split(pszValue, ',', &numFormats);
      if(numFormats > 0 && papszFormats)
      {
          fprintf( stream, "      <FormatList>\n");
          for(nForm=0; nForm<numFormats; nForm++)
          {
              if(pszCurrent && (strcasecmp(papszFormats[nForm], 
                                           pszCurrent) == 0))
                  fprintf( stream,
                           "        <Format current=\"1\">%s</Format>\n",
                           papszFormats[nForm]);
              else
                  fprintf( stream, "        <Format>%s</Format>\n", 
                           papszFormats[nForm]);
          }
          fprintf( stream, "      </FormatList>\n");
      }
      if(papszFormats)
          msFreeCharArray(papszFormats, numFormats);
  }

  // Style
  if(msOWSLookupMetadata(&(layer->metadata), namespaces, "stylelist") == NULL)
  {
      pszURL = "";
      if(layer->connection)
          pszURL = strdup( layer->connection );
      else
          pszURL = strdup( "" );
      pszValue = pszURL;
      pszValue = strstr( pszValue, "STYLES=" );
      if( pszValue )
      {
          pszValue += 7;
          pszChar = strchr(pszValue, '&');
          if( pszChar )
              pszValue[pszChar - pszValue] = '\0';

          if(layer->connection)
              pszSLD2 = strdup(layer->connection);
          else
              pszSLD2 = strdup( "" );
          if(pszSLD2)
              pszSLD = strstr(pszSLD2, "SLD=");
          else
              pszSLD = NULL;
          if( pszSLD )
          {
              pszChar = strchr(pszSLD, '&');
              if( pszChar )
                  pszSLD[pszChar - pszSLD] = '\0';
              pszSLD += 4;
          }
          if( (pszValue && (strcasecmp(pszValue, "") != 0)) || 
              (pszSLD && (strcasecmp(pszSLD, "") != 0)))
          {
              fprintf( stream, "      <StyleList>\n");
              fprintf( stream, "        <Style current=\"1\">\n");
              if( pszValue && (strcasecmp(pszValue, "") != 0))
              {
                  fprintf(stream, "          <Name>%s</Name>\n", 
                          pszValue);
                  fprintf(stream,"          <Title>%s</Title>\n",
                          pszValue);
              }
              if( pszSLD && (strcasecmp(pszSLD, "") != 0))
              {
                  pszEncodedVal = msEncodeHTMLEntities(pszSLD);
                  fprintf( stream, "          <SLD>\n" );
                  fprintf( stream, 
                           "            <OnlineResource xlink:type=\"simple\" ");
                  fprintf(stream,"xlink:href=\"%s\"/>", pszEncodedVal);
                  fprintf( stream, "          </SLD>\n" );
                  free(pszEncodedVal);
              }
              fprintf( stream, "        </Style>\n");
              fprintf( stream, "      </StyleList>\n");
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
      pszValue = (char*)msOWSLookupMetadata(&(layer->metadata), namespaces, 
                                            "stylelist");
      pszCurrent = (char*)msOWSLookupMetadata(&(layer->metadata), namespaces, 
                                              "style");
      fprintf( stream, "      <StyleList>\n");
      while(pszValue != NULL)
      {
          pszStyle = strdup(pszValue);
          pszChar = strchr(pszStyle, ',');
          if(pszChar != NULL)
              pszStyle[pszChar - pszStyle] = '\0';
          if( strcasecmp(pszStyle, "") != 0)
          {
              if(pszCurrent && (strcasecmp(pszStyle, pszCurrent) == 0))
                  fprintf( stream,"        <Style current=\"1\">\n" );
              else
                  fprintf( stream, "        <Style>\n" );

              pszStyleItem = (char*)malloc(strlen(pszStyle)+15);
              sprintf(pszStyleItem, "style_%s_sld", pszStyle);
              if(msOWSLookupMetadata( &(layer->metadata),namespaces, 
                                      pszStyleItem ) != NULL)
              {
                  fprintf(stream, "          <SLD>\n");
                  msOWSPrintEncodeMetadata(stream, 
                                           &(layer->metadata),
                                           namespaces, pszStyleItem, 
                                           OWS_NOERR, 
                                           "            <OnlineResource xlink:type=\"simple\" xlink:href=\"%s\"/>\n",
                                           NULL);
                  fprintf(stream, "          </SLD>\n");
                  free(pszStyleItem);
              }
              else
              {
                  free(pszStyleItem);
                  // Name
                  fprintf(stream, "          <Name>%s</Name>\n", 
                          pszStyle);
                  pszStyleItem = (char*)malloc(strlen(pszStyle)+10+8);
                  sprintf(pszStyleItem, "style_%s_title",pszStyle);
                  // Title
                  msOWSPrintMetadata(stream, &(layer->metadata), 
                                     namespaces, pszStyleItem, OWS_NOERR, 
                                     "          <Title>%s</Title>\n", 
                                     NULL);
                  free(pszStyleItem);

                  // LegendURL
                  pszStyleItem = (char*)malloc(strlen(pszStyle)+10+20);
                  sprintf(pszStyleItem, "style_%s_legendurl_href",
                          pszStyle);
                  pszURL = (char*)msOWSLookupMetadata(&(layer->metadata), 
                                                      namespaces, 
                                                      pszStyleItem);
                  if(pszURL != NULL)
                  {
                      sprintf(pszStyleItem, 
                              "style_%s_legendurl",pszStyle);
                      msWriteMapContextURLElements(stream, &(layer->metadata), 
                                                   "LegendURL", namespaces, 
                                                   pszStyleItem,
                                                   "          ");
                  }
                  free(pszStyleItem);
              }

              fprintf( stream,"        </Style>\n" );
          }
          free(pszStyle);
          pszValue = strchr(pszValue, ',');
          if(pszValue)  
              pszValue++;
      }
      fprintf( stream, "      </StyleList>\n");
  }

  return MS_SUCCESS;
}

/*
** msWriteMapContextLayer
**
** Save the WMS layer componnents in a given stream.
*/
int msWriteMapContextLayer(FILE *stream, layerObj *layer, 
                           const char *namespaces, int nVersion)
{
    int nValue;
    char *pszValue, *pszDecodedVal;

    if(layer->status == MS_OFF)
        nValue = 1;
    else
        nValue = 0;

    fprintf(stream, "    <Layer queryable=\"%d\" hidden=\"%d\">\n", 
            msIsLayerQueryable(layer), nValue);

    msWriteMapContextAbstractView(stream, layer, namespaces, nVersion);

    if( IS_OWS_CONTEXT(nVersion) )
    {
        //
        // Print the filter of the layer
        //
        pszValue = msLookupHashTable(&(layer->metadata), 
                                     "wfs_filter");
        if(pszValue != NULL)
        {
            pszDecodedVal = strdup(pszValue);
            msDecodeHTMLEntities(pszDecodedVal);
            fprintf(stream, "      <ogc:Filter>%s</ogc:Filter>\n", 
                    pszDecodedVal);
            free(pszDecodedVal);
        }
    }

    fprintf(stream, "    </Layer>\n");

    return MS_SUCCESS;
}

/*
** msWriteMapContextFeature
**
** Save the WFS layer componnents in a given stream.
*/
int msWriteMapContextFeature(FILE *stream, layerObj *layer, 
                             const char *namespaces, int nVersion)
{
    int nValue;
    char *pszValue, *pszDecodedVal;

    if(layer->status == MS_OFF)
        nValue = 1;
    else
        nValue = 0;

    fprintf(stream, "    <FeatureType hidden=\"%d\">\n", nValue);

    msWriteMapContextAbstractView(stream, layer, namespaces, nVersion);

    if( IS_OWS_CONTEXT(nVersion) )
    {
        //
        // Print the filter of the layer
        //
        pszValue = (char*)msOWSLookupMetadata(&(layer->metadata), namespaces, 
                                              "filter");
        if(pszValue != NULL)
        {
            pszDecodedVal = strdup(pszValue);
            msDecodeHTMLEntities(pszDecodedVal);
            fprintf(stream, "      <ogc:Filter>%s</ogc:Filter>\n", 
                    pszDecodedVal);
            free(pszDecodedVal);
        }
    }

    fprintf(stream, "    </FeatureType>\n");

    return MS_SUCCESS;
}

#endif


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

  // open file
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
  const char * version;
  char *pszValue;
  int i, nVersion=-1;

  // Decide which version we're going to return...
  version = msLookupHashTable(&(map->web.metadata), "ows_context_version");
  if(version == NULL)
  {
      version = msLookupHashTable(&(map->web.metadata), "wms_context_version");
      if(version == NULL)
          version = "1.0.0";

      nVersion = msOWSParseVersionString(version);
      if (nVersion < 0)
          return MS_FAILURE;  // msSetError() already called.
      nVersion = MAKE_WMS_CONTEXT(nVersion);
  }
  else
  {
      nVersion = msOWSParseVersionString(version);
      if (nVersion < 0)
          return MS_FAILURE;  // msSetError() already called.
      nVersion = MAKE_OWS_CONTEXT(nVersion);
  }

  // Make sure this is a supported version
  // Note that we don't write 0.1.2 even if we read it.
  switch ( CONTEXT_VERSION(nVersion) )
  {
    case OWS_0_0_7:
    case OWS_0_1_4:
    case OWS_0_1_7:
    case OWS_1_0_0:
      // All is good, this is a supported version.
      break;
    default:
      // Not a supported version
      msSetError(MS_MAPCONTEXTERR, 
                 "This version of Map Context is not supported (%s).",
                 "msSaveMapContext()", version);
      return MS_FAILURE;
  }

  // file header
  msOWSPrintMetadata(stream, &(map->web.metadata), 
                     NULL, "wms_encoding", OWS_NOERR,
                "<?xml version='1.0' encoding=\"%s\" standalone=\"no\" ?>\n",
                    "ISO-8859-1");

  // set the WMS_Viewer_Context information
  if( IS_OWS_CONTEXT(nVersion) )
  {
      char szVersionBuf[OWS_VERSION_MAXLEN];

      fprintf( stream, "<OWSContext version=\"%s\"", 
               msOWSGetVersionString( (nVersion - 0x010000), szVersionBuf ) );
  }
  else if( CONTEXT_VERSION(nVersion) >= OWS_1_0_0 )
  {
      fprintf( stream, "<ViewContext version=\"%s\"", version );
  }
  else if( CONTEXT_VERSION(nVersion) >= OWS_0_1_7 )
  {
      fprintf( stream, "<View_Context version=\"%s\"", version );
      
  }
  else // 0.1.4
  {
      fprintf( stream, "<WMS_Viewer_Context version=\"%s\"", version );
  }

  if ( !IS_OWS_CONTEXT(nVersion) && 
       CONTEXT_VERSION(nVersion) >= OWS_0_1_7 && 
       CONTEXT_VERSION(nVersion) < OWS_1_0_0 )
  {
      pszValue = msLookupHashTable(&(map->web.metadata), "wms_context_fid");
      if(pszValue != NULL)
          fprintf( stream, " fid=\"%s\"", pszValue );
      else
          fprintf( stream, " fid=\"0\"");
  }
  if ( IS_OWS_CONTEXT(nVersion) || CONTEXT_VERSION(nVersion) >= OWS_1_0_0 )
        fprintf( stream, " id=\"%s\"", map->name);

  fprintf( stream, " xmlns:xsi=\"http://www.w3.org/2001/XMLSchema-instance\"");

  if( !IS_OWS_CONTEXT(nVersion) && 
      CONTEXT_VERSION(nVersion) >= OWS_0_1_7 && 
      CONTEXT_VERSION(nVersion) < OWS_1_0_0 )
  {
      fprintf( stream, " xmlns:gml=\"http://www.opengis.net/gml\"");
  }
  if( IS_OWS_CONTEXT(nVersion) )
  {
      fprintf( stream, 
               " xsi:schemaLocation=\"http://www.opengis.net/context context_0_0_5.xsd\">\n");
  }
  else if( CONTEXT_VERSION(nVersion) >= OWS_1_0_0 )
  {
      fprintf( stream, " xmlns:xlink=\"http://www.w3.org/1999/xlink\"");
      fprintf( stream, " xmlns=\"http://www.opengis.net/context\"");
      //fprintf( stream, " xmlns:sld=\"http://www.opengis.net/sld");
      fprintf( stream, 
               " xsi:schemaLocation=\"http://www.opengis.net/context http://schemas.opengis.net/context/1.0.0/context.xsd\">\n");
  }
  else
  {
      fprintf( stream, " xmlns:xlink=\"http://www.w3.org/TR/xlink\"");
                   
      fprintf( stream, 
               " xsi:noNamespaceSchemaLocation=\"%s/contexts/%s/context.xsd\">\n",
               msOWSGetSchemasLocation(map), version );
  }

  msWriteMapContextGeneral(stream, map, nVersion);

  // Set the layer list
  if( IS_OWS_CONTEXT(nVersion) )
      fprintf(stream, "  <ResourceList>\n");
  else
      fprintf(stream, "  <LayerList>\n");

  // Loop on all layer  
  for(i=0; i<map->numlayers; i++)
  {
      if( map->layers[i].connectiontype == MS_WMS || 
          ( map->layers[i].connectiontype == MS_WFS && 
            IS_OWS_CONTEXT(nVersion) ) )
      {
          if(map->layers[i].connectiontype == MS_WFS && 
            IS_OWS_CONTEXT(nVersion))
              msWriteMapContextFeature(stream, &(map->layers[i]), "FO", 
                                       nVersion);
          else
              msWriteMapContextLayer(stream, &(map->layers[i]), "MO", 
                                     nVersion);
      }
  }

  // Close layer list
  if( IS_OWS_CONTEXT(nVersion) )
      fprintf(stream, "  </ResourceList>\n");
  else
      fprintf(stream, "  </LayerList>\n");
  // Close Map Context

  if( IS_OWS_CONTEXT(nVersion) )
  {
      fprintf(stream, "</OWSContext>\n");
  }
  else if( CONTEXT_VERSION(nVersion) >= OWS_1_0_0 )
  {
      fprintf(stream, "</ViewContext>\n");
  }
  else if( CONTEXT_VERSION(nVersion) >= OWS_0_1_7)
  {
      fprintf(stream, "</View_Context>\n");
  }
  else // 0.1.4
  {
      fprintf(stream, "</WMS_Viewer_Context>\n");
  }

  return MS_SUCCESS;
#else
  msSetError(MS_MAPCONTEXTERR, 
             "Not implemented since Map Context is not enabled.",
             "msWriteMapContext()");
  return MS_FAILURE;
#endif
}

