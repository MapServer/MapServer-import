/* $Id$ */

#include "maptemplate.h"
#include "maphash.h"
#include "map.h"

#include <sys/types.h>
#include <sys/stat.h>
#include <time.h>

char *processLine(mapservObj* msObj, char* instr, int mode);

/*
 * Redirect to (only use in CGI)
 * 
*/
int msRedirect(char *url)
{
  printf("Status: 302 Found\n");
  printf("Uri: %s\n", url);
  printf("Location: %s\n", url);
  printf("Content-type: text/html%c%c",10,10);
  fflush(stdout);
  return MS_SUCCESS;
}

/*
** Sets the map extent under a variety of scenarios.
*/
int setExtent(mapservObj *msObj)
{
  double cellx,celly,cellsize;

  switch(msObj->CoordSource) 
  {
   case FROMUSERBOX: /* user passed in a map extent */
     break;
   case FROMIMGBOX: /* fully interactive web, most likely with java front end */
     cellx = MS_CELLSIZE(msObj->ImgExt.minx, msObj->ImgExt.maxx, msObj->ImgCols);
     celly = MS_CELLSIZE(msObj->ImgExt.miny, msObj->ImgExt.maxy, msObj->ImgRows);
     msObj->Map->extent.minx = MS_IMAGE2MAP_X(msObj->ImgBox.minx, msObj->ImgExt.minx, cellx);
     msObj->Map->extent.maxx = MS_IMAGE2MAP_X(msObj->ImgBox.maxx, msObj->ImgExt.minx, cellx);
     msObj->Map->extent.maxy = MS_IMAGE2MAP_Y(msObj->ImgBox.miny, msObj->ImgExt.maxy, celly); // y's are flip flopped because img/map coordinate systems are
     msObj->Map->extent.miny = MS_IMAGE2MAP_Y(msObj->ImgBox.maxy, msObj->ImgExt.maxy, celly);
     break;
   case FROMIMGPNT:
     cellx = MS_CELLSIZE(msObj->ImgExt.minx, msObj->ImgExt.maxx, msObj->ImgCols);
     celly = MS_CELLSIZE(msObj->ImgExt.miny, msObj->ImgExt.maxy, msObj->ImgRows);
     msObj->MapPnt.x = MS_IMAGE2MAP_X(msObj->ImgPnt.x, msObj->ImgExt.minx, cellx);
     msObj->MapPnt.y = MS_IMAGE2MAP_Y(msObj->ImgPnt.y, msObj->ImgExt.maxy, celly);

     msObj->Map->extent.minx = msObj->MapPnt.x - .5*((msObj->ImgExt.maxx - msObj->ImgExt.minx)/msObj->fZoom); // create an extent around that point
     msObj->Map->extent.miny = msObj->MapPnt.y - .5*((msObj->ImgExt.maxy - msObj->ImgExt.miny)/msObj->fZoom);
     msObj->Map->extent.maxx = msObj->MapPnt.x + .5*((msObj->ImgExt.maxx - msObj->ImgExt.minx)/msObj->fZoom);
     msObj->Map->extent.maxy = msObj->MapPnt.y + .5*((msObj->ImgExt.maxy - msObj->ImgExt.miny)/msObj->fZoom);
     break;
   case FROMREFPNT:
     cellx = MS_CELLSIZE(msObj->Map->reference.extent.minx, msObj->Map->reference.extent.maxx, msObj->Map->reference.width);
     celly = MS_CELLSIZE(msObj->Map->reference.extent.miny, msObj->Map->reference.extent.maxy, msObj->Map->reference.height);
     msObj->MapPnt.x = MS_IMAGE2MAP_X(msObj->RefPnt.x, msObj->Map->reference.extent.minx, cellx);
     msObj->MapPnt.y = MS_IMAGE2MAP_Y(msObj->RefPnt.y, msObj->Map->reference.extent.maxy, celly);  

     msObj->Map->extent.minx = msObj->MapPnt.x - .5*(msObj->ImgExt.maxx - msObj->ImgExt.minx); // create an extent around that point
     msObj->Map->extent.miny = msObj->MapPnt.y - .5*(msObj->ImgExt.maxy - msObj->ImgExt.miny);
     msObj->Map->extent.maxx = msObj->MapPnt.x + .5*(msObj->ImgExt.maxx - msObj->ImgExt.minx);
     msObj->Map->extent.maxy = msObj->MapPnt.y + .5*(msObj->ImgExt.maxy - msObj->ImgExt.miny);
     break;
   case FROMBUF:
     msObj->Map->extent.minx = msObj->MapPnt.x - msObj->Buffer; // create an extent around that point, using the buffer
     msObj->Map->extent.miny = msObj->MapPnt.y - msObj->Buffer;
     msObj->Map->extent.maxx = msObj->MapPnt.x + msObj->Buffer;
     msObj->Map->extent.maxy = msObj->MapPnt.y + msObj->Buffer;
     break;
   case FROMSCALE: 
     cellsize = (msObj->Scale/msObj->Map->resolution)/msInchesPerUnit(msObj->Map->units,0); // user supplied a point and a scale
     msObj->Map->extent.minx = msObj->MapPnt.x - cellsize*msObj->Map->width/2.0;
     msObj->Map->extent.miny = msObj->MapPnt.y - cellsize*msObj->Map->height/2.0;
     msObj->Map->extent.maxx = msObj->MapPnt.x + cellsize*msObj->Map->width/2.0;
     msObj->Map->extent.maxy = msObj->MapPnt.y + cellsize*msObj->Map->height/2.0;
     break;
   default: /* use the default in the mapfile if it exists */
     if((msObj->Map->extent.minx == msObj->Map->extent.maxx) && (msObj->Map->extent.miny == msObj->Map->extent.maxy)) {
        msSetError(MS_WEBERR, "No way to generate map extent.", "mapserv()");
        return MS_FAILURE;
     }
  }

   msObj->RawExt = msObj->Map->extent; /* save unaltered extent */
   
   return MS_SUCCESS;
}

int checkWebExtent(mapservObj *msObj)
{
   return MS_SUCCESS;
}

int checkWebScale(mapservObj *msObj) 
{
   int status;

   msObj->Map->cellsize = msAdjustExtent(&(msObj->Map->extent), msObj->Map->width, msObj->Map->height); // we do this cause we need a scale
   if((status = msCalculateScale(msObj->Map->extent, msObj->Map->units, msObj->Map->width, msObj->Map->height, msObj->Map->resolution, &msObj->Map->scale)) != MS_SUCCESS) return status;

   if((msObj->Map->scale < msObj->Map->web.minscale) && (msObj->Map->web.minscale > 0)) {
      if(msObj->Map->web.mintemplate) { // use the template provided
         if(TEMPLATE_TYPE(msObj->Map->web.mintemplate) == MS_FILE) {
            if ((status = msReturnPage(msObj, msObj->Map->web.mintemplate, BROWSE, NULL)) != MS_SUCCESS) return status;
         }
         else
         {
            if ((status = msReturnURL(msObj, msObj->Map->web.mintemplate, BROWSE)) != MS_SUCCESS) return status;
         }
      } 
      else 
      { /* force zoom = 1 (i.e. pan) */
         msObj->fZoom = msObj->Zoom = 1;
         msObj->ZoomDirection = 0;
         msObj->CoordSource = FROMSCALE;
         msObj->Scale = msObj->Map->web.minscale;
         msObj->MapPnt.x = (msObj->Map->extent.maxx + msObj->Map->extent.minx)/2; // use center of bad extent
         msObj->MapPnt.y = (msObj->Map->extent.maxy + msObj->Map->extent.miny)/2;
         setExtent(msObj);
         msObj->Map->cellsize = msAdjustExtent(&(msObj->Map->extent), msObj->Map->width, msObj->Map->height);      
         if((status = msCalculateScale(msObj->Map->extent, msObj->Map->units, msObj->Map->width, msObj->Map->height, msObj->Map->resolution, &msObj->Map->scale)) != MS_SUCCESS) return status;
      }
   } 
   else 
   if((msObj->Map->scale > msObj->Map->web.maxscale) && (msObj->Map->web.maxscale > 0)) {
      if(msObj->Map->web.maxtemplate) { // use the template provided
         if(TEMPLATE_TYPE(msObj->Map->web.maxtemplate) == MS_FILE) {
            if ((status = msReturnPage(msObj, msObj->Map->web.maxtemplate, BROWSE, NULL)) != MS_SUCCESS) return status;
         }
         else {
            if ((status = msReturnURL(msObj, msObj->Map->web.maxtemplate, BROWSE)) != MS_SUCCESS) return status;
         }
      } else { /* force zoom = 1 (i.e. pan) */
         msObj->fZoom = msObj->Zoom = 1;
         msObj->ZoomDirection = 0;
         msObj->CoordSource = FROMSCALE;
         msObj->Scale = msObj->Map->web.maxscale;
         msObj->MapPnt.x = (msObj->Map->extent.maxx + msObj->Map->extent.minx)/2; // use center of bad extent
         msObj->MapPnt.y = (msObj->Map->extent.maxy + msObj->Map->extent.miny)/2;
         setExtent(msObj);
         msObj->Map->cellsize = msAdjustExtent(&(msObj->Map->extent), msObj->Map->width, msObj->Map->height);
         if((status = msCalculateScale(msObj->Map->extent, msObj->Map->units, msObj->Map->width, msObj->Map->height, msObj->Map->resolution, &msObj->Map->scale)) != MS_SUCCESS) return status;
      }
   }
   
   return MS_SUCCESS;
}


int msReturnTemplateQuery(mapservObj *msObj, char* pszMimeType,
                          char **papszBuffer)
{
    imageObj *img = NULL;
    int status;
    char buffer[1024];

   if (!pszMimeType)
   {
      msSetError(MS_WEBERR, "Mime type not specified.", "msReturnTemplateQuery()");
      return MS_FAILURE;
   }
   
   if(msObj->Map->querymap.status)
   {
      checkWebScale(msObj);

      img = msDrawQueryMap(msObj->Map);
      if(!img) return MS_FAILURE;

      snprintf(buffer, 1024, "%s%s%s.%s", msObj->Map->web.imagepath, msObj->Map->name, msObj->Id, MS_IMAGE_EXTENSION(msObj->Map->outputformat));

      status = msSaveImage(msObj->Map, img, buffer);
      if(status != MS_SUCCESS) return status;

      msFreeImage(img);

      if((msObj->Map->legend.status == MS_ON || msObj->UseShapes) && msObj->Map->legend.template == NULL)
      {
         img = msDrawLegend(msObj->Map);
         if(!img) return MS_FAILURE;
         snprintf(buffer, 1024, "%s%sleg%s.%s", msObj->Map->web.imagepath, msObj->Map->name, msObj->Id, MS_IMAGE_EXTENSION(msObj->Map->outputformat));
         status = msSaveImage(NULL, img, buffer);
         if(status != MS_SUCCESS) return status;
         msFreeImage(img);
      }
	  
      if(msObj->Map->scalebar.status == MS_ON) 
      {
         img = msDrawScalebar(msObj->Map);
         if(!img) return MS_FAILURE;
         snprintf(buffer, 1024, "%s%ssb%s.%s", msObj->Map->web.imagepath, msObj->Map->name, msObj->Id, MS_IMAGE_EXTENSION(msObj->Map->outputformat));
         status = msSaveImage( NULL, img, buffer);
         if(status != MS_SUCCESS) return status;
         msFreeImage(img);
      }
	  
      if(msObj->Map->reference.status == MS_ON) 
      {
         img = msDrawReferenceMap(msObj->Map);
         if(!img) return MS_FAILURE;
         snprintf(buffer, 1024, "%s%sref%s.%s", msObj->Map->web.imagepath, msObj->Map->name, msObj->Id, MS_IMAGE_EXTENSION(msObj->Map->outputformat));
         status = msSaveImage(NULL, img, buffer);
         if(status != MS_SUCCESS) return status;
         msFreeImage(img);
      }
   }
   
   if ((status = msReturnQuery(msObj, pszMimeType, papszBuffer)) != MS_SUCCESS)
     return status;

   return MS_SUCCESS;
}

/*
** Is a particular layer or group on, that is was it requested explicitly by the user.
*/
int isOn(mapservObj *msObj, char *name, char *group)
{
  int i;

  for(i=0;i<msObj->NumLayers;i++) {
    if(name && strcmp(msObj->Layers[i], name) == 0)  return(MS_TRUE);
    if(group && strcmp(msObj->Layers[i], group) == 0) return(MS_TRUE);
  }

  return(MS_FALSE);
}

/************************************************************************/
/*            int sortLayerByOrder(mapObj *map, char* pszOrder)         */
/*                                                                      */
/*      sorth the displaying in ascending or descending order.          */
/************************************************************************/
int sortLayerByOrder(mapObj *map, char* pszOrder)
{
    int *panCurrentOrder = NULL;
    int i = 0;

    if (!map) 
    {
        msSetError(MS_WEBERR, "Invalid pointer.", "sortLayerByOrder()");
        return MS_FAILURE;
    }
/* ==================================================================== */
/*      The flag "ascending" is in fact not useful since the            */
/*      default ordering is ascending.                                  */
/* ==================================================================== */

/* -------------------------------------------------------------------- */
/*      the map->layerorder should be set at this point in the          */
/*      sortLayerByMetadata.                                            */
/* -------------------------------------------------------------------- */
    if (map->layerorder)
    {
        panCurrentOrder = (int*)malloc(map->numlayers * sizeof(int));
         for (i=0; i<map->numlayers ;i++)
           panCurrentOrder[i] = map->layerorder[i];
         
         if (strcasecmp(pszOrder, "DESCENDING") == 0)
         {
             for (i=0; i<map->numlayers; i++)
               map->layerorder[i] = panCurrentOrder[map->numlayers-1-i];
         }

         free(panCurrentOrder);
    }

    return MS_SUCCESS;
}
             
             
/*!
 * This function set the map->layerorder
 * index order by the metadata collumn name
*/
int sortLayerByMetadata(mapObj *map, char* pszMetadata)
{
   int nLegendOrder1;
   int nLegendOrder2;
   char *pszLegendOrder1;
   char *pszLegendOrder2;
   int i, j;
   int tmp;

   if (!map) {
     msSetError(MS_WEBERR, "Invalid pointer.", "sortLayerByMetadata()");
     return MS_FAILURE;
   }
   
   /*
    * Initiate to default order (Reverse mapfile order)
    */
   if (map->layerorder)
   {
     int *pnLayerOrder;

     // Backup the original layer order to be able to reverse it
     pnLayerOrder = (int*)malloc(map->numlayers * sizeof(int));
     for (i=0; i<map->numlayers ;i++)
       pnLayerOrder[i] = map->layerorder[i];

     // Get a new layerorder array
     free(map->layerorder);
     map->layerorder = (int*)malloc(map->numlayers * sizeof(int));

     // Reverse the layerorder array
     for (i=0; i<map->numlayers ;i++)
       map->layerorder[i] = pnLayerOrder[map->numlayers - i - 1];

     free(pnLayerOrder);
   }
   else
   {
     map->layerorder = (int*)malloc(map->numlayers * sizeof(int));

     for (i=0; i<map->numlayers ;i++)
       map->layerorder[i] = map->numlayers - i - 1;
   }

   if (!pszMetadata)
     return MS_SUCCESS;
   
   /* 
    * Bubble sort algo (not very efficient)
    * should implement a kind of quick sort
    * alog instead
   */
   for (i=0; i<map->numlayers-1; i++) {
      for (j=0; j<map->numlayers-1-i; j++) {
         pszLegendOrder1 = msLookupHashTable(map->layers[map->layerorder[j+1]].metadata, pszMetadata);
         pszLegendOrder2 = msLookupHashTable(map->layers[map->layerorder[j]].metadata, pszMetadata);
     
         if (!pszLegendOrder1 || !pszLegendOrder2)
           continue;
         
         nLegendOrder1 = atoi(pszLegendOrder1);
         nLegendOrder2 = atoi(pszLegendOrder2);      
         
         if (nLegendOrder1 < nLegendOrder2) {  /* compare the two neighbors */
            tmp = map->layerorder[j];         /* swap a[j] and a[j+1]      */
            map->layerorder[j] = map->layerorder[j+1];
            map->layerorder[j+1] = tmp;
         }
      }
   }
   
   return MS_SUCCESS;
}

/*!
 * This function return a pointer
 * at the begining of the first occurence
 * of pszTag in pszInstr.
 * 
 * Tag can be [TAG] or [TAG something]
*/
char* findTag(char* pszInstr, char* pszTag)
{
   char *pszTag1, *pszTag2, *pszStart;

   if (!pszInstr || !pszTag) {
     msSetError(MS_WEBERR, "Invalid pointer.", "findTag()");
     return NULL;
   }

   pszTag1 = (char*)malloc(strlen(pszTag) + 3);
   pszTag2 = (char*)malloc(strlen(pszTag) + 3);

   strcpy(pszTag1, "[");   
   strcat(pszTag1, pszTag);
   strcat(pszTag1, " ");

   strcpy(pszTag2, "[");      
   strcat(pszTag2, pszTag);
   strcat(pszTag2, "]");

   pszStart = strstr(pszInstr, pszTag1);
   if (pszStart == NULL)
      pszStart = strstr(pszInstr, pszTag2);

   free(pszTag1);
   free(pszTag2);
   
   return pszStart;
}

/*!
 * return a hashtableobj from instr of all
 * arguments. hashtable must be freed by caller.
 */
int getTagArgs(char* pszTag, char* pszInstr, hashTableObj *oHashTable)
{
   char *pszStart, *pszEnd, *pszArgs;
   int nLength;
   char **papszArgs, **papszVarVal;
   int nArgs, nDummy;
   int i;
   char *pszQuoteStr, *pszQuoteStart, *pszQuoteEnd;
   
   if (!pszTag || !pszInstr) {
     msSetError(MS_WEBERR, "Invalid pointer.", "getTagArgs()");
     return MS_FAILURE;
   }
   
   // set position to the begining of tag
   pszStart = findTag(pszInstr, pszTag);

   if (pszStart) {
      // find ending position
      pszEnd = strchr(pszStart, ']');
   
      if (pszEnd) {
         // skit the tag name
         pszStart = pszStart + strlen(pszTag) + 1;

         // get lenght of all args
         nLength = pszEnd - pszStart;
   
         if (nLength > 0) { // is there arguments ?
            pszArgs = (char*)malloc(nLength + 1);
            strncpy(pszArgs, pszStart, nLength);
            pszArgs[nLength] = '\0';
            
            if (!*oHashTable)
              *oHashTable = msCreateHashTable();
            
            // Enable the use of "" in args
            // To do so, extract all "" values 
            // and replace the " in it by spaces
            if(strchr(pszArgs, '"'))
            {
                pszQuoteEnd = pszArgs;
                while((pszQuoteStart = strchr(pszQuoteEnd, '"')))
                {
                    pszQuoteEnd = strchr(pszQuoteStart+1, '"');
                    if(pszQuoteEnd)
                    {
                        pszQuoteEnd[0] = '\0';
                        while((pszQuoteStr = strchr(pszQuoteStart, ' ')))
                            pszQuoteStr[0] = '"';

                        // Then remove the starting and ending quote
                        pszQuoteEnd[0] = '"';
                        for(i=(pszQuoteStart-pszArgs); i<nLength; i++)
                        {
                            if(i+1 >= pszQuoteEnd-pszArgs)
                                if(i+2 >= nLength)
                                    pszArgs[i] = '\0';
                                else
                                    pszArgs[i] = pszArgs[i+2];
                            else
                                pszArgs[i] = pszArgs[i+1];
                        }
                    }
                }
            }

            // put all arguments seperate by space in a hash table
            papszArgs = split(pszArgs, ' ', &nArgs);

            // msReturnTemplateQuerycheck all argument if they have values
            for (i=0; i<nArgs; i++) {
               // Quotes are in fact spaces
               if(strchr(papszArgs[i],'"'))
                   while((pszQuoteStr = strchr(papszArgs[i],'"')))
                       pszQuoteStr[0] = ' ';

               if (strchr(papszArgs[i], '='))
               {
                  papszVarVal = split(papszArgs[i], '=', &nDummy);
               
                  msInsertHashTable(*oHashTable, papszVarVal[0], papszVarVal[1]);
                  free(papszVarVal[0]);
                  free(papszVarVal[1]);
                  free(papszVarVal);                  
               }
               else // no value specified. set it to 1
                  msInsertHashTable(*oHashTable, papszArgs[i], "1");
               
               free(papszArgs[i]);
            }
            free(papszArgs);
            free(pszArgs);
         }
      }
   }  

   return MS_SUCCESS;
}   

/*!
 * return a substring from instr beetween [tag] and [/tag]
 * char* returned must be freed by caller.
 * pszNextInstr will be a pointer at the end of the 
 * first occurence founded.
 */
int getInlineTag(char* pszTag, char* pszInstr, char **pszResult)
{
   char *pszStart, *pszEnd=NULL,  *pszEndTag, *pszPatIn, *pszPatOut=NULL, *pszTmp;
   int nInst=0;
   int nLength;

   *pszResult = NULL;

   if (!pszInstr || !pszTag) {
     msSetError(MS_WEBERR, "Invalid pointer.", "getInlineTag()");
     return MS_FAILURE;
   }

   pszEndTag = (char*)malloc(strlen(pszTag) + 3);
   strcpy(pszEndTag, "[/");
   strcat(pszEndTag, pszTag);

   // find start tag
   pszPatIn  = findTag(pszInstr, pszTag);
   pszPatOut = strstr(pszInstr, pszEndTag);      

   pszStart = pszPatIn;

   pszTmp = pszInstr;

   if (pszPatIn)
   {
      do 
      {
         if (pszPatIn && pszPatIn < pszPatOut)
         {
            nInst++;
         
            pszTmp = pszPatIn;
         }
      
         if (pszPatOut && ((pszPatIn == NULL) || pszPatOut < pszPatIn))
         {
            pszEnd = pszPatOut;
            nInst--;
         
            pszTmp = pszPatOut;
         }

         pszPatIn  = findTag(pszTmp+1, pszTag);
         pszPatOut = strstr(pszTmp+1, pszEndTag);
      
      }while (pszTmp != NULL && nInst > 0);
   }

   if (pszStart && pszEnd) {
      // find end of start tag
      pszStart = strchr(pszStart, ']');
   
      if (pszStart) {
         pszStart++;

         nLength = pszEnd - pszStart;
            
         if (nLength > 0) {
            *pszResult = (char*)malloc(nLength + 1);

            // copy string beetween start and end tag
            strncpy(*pszResult, pszStart, nLength);

            (*pszResult)[nLength] = '\0';
         }
      }
      else
      {
         msSetError(MS_WEBERR, "Malformed [%s] tag.", "getInlineTag()", pszTag);
         return MS_FAILURE;
      }
   }

   msFree(pszEndTag);

   return MS_SUCCESS;
}

/*!
 * this function process all if tag in pszInstr.
 * this function return a modified pszInstr.
 * ht mus contain all variables needed by the function
 * to interpret if expression.
 *
 * If bLastPass is true then all tests for 'null' values will be
 * considered true if the corresponding value is not set.
*/
int processIf(char** pszInstr, hashTableObj ht, int bLastPass)
{
//   char *pszNextInstr = pszInstr;
   char *pszStart, *pszEnd=NULL;
   char *pszName, *pszValue, *pszOperator, *pszThen=NULL, *pszHTValue;
   char *pszIfTag;
   char *pszPatIn=NULL, *pszPatOut=NULL, *pszTmp;
   int nInst = 0;
   int bEmpty = 0;
   int nLength;

   hashTableObj ifArgs=NULL;

   if (!*pszInstr) {
     msSetError(MS_WEBERR, "Invalid pointer.", "processIf()");
     return MS_FAILURE;
   }

   // find the if start tag
   
   pszStart  = findTag(*pszInstr, "if");

   while (pszStart)
   {   
      pszPatIn  = findTag(pszStart, "if");
      pszPatOut = strstr(pszStart, "[/if]");
      pszTmp = pszPatIn;
      
      do 
      {
         if (pszPatIn && pszPatIn < pszPatOut)
         {
            nInst++;
         
            pszTmp = pszPatIn;
         }
      
         if (pszPatOut && ((pszPatIn == NULL) || pszPatOut < pszPatIn))
         {
            pszEnd = pszPatOut;
            nInst--;
         
            pszTmp = pszPatOut;
         
         }

         pszPatIn  = findTag(pszTmp+1, "if");
         pszPatOut = strstr(pszTmp+1, "[/if]");
      
      }while (pszTmp != NULL && nInst > 0);

      // get the then string (if expression is true)
      if (getInlineTag("if", pszStart, &pszThen) != MS_SUCCESS)
      {
         msSetError(MS_WEBERR, "Malformed then if tag.", "processIf()");
         return MS_FAILURE;
      }
      
      // retrieve if tag args
      if (getTagArgs("if", pszStart, &ifArgs) != MS_SUCCESS)
      {
         msSetError(MS_WEBERR, "Malformed args if tag.", "processIf()");
         return MS_FAILURE;
      }
      
      pszName = msLookupHashTable(ifArgs, "name");
      pszValue = msLookupHashTable(ifArgs, "value");
      pszOperator = msLookupHashTable(ifArgs, "oper");
      // Default operator if not set is "eq"
      if (pszOperator == NULL)
          pszOperator = "eq";

      bEmpty = 0;
      
      if (pszName) {
         // build the complete if tag ([if all_args]then string[/if])
         // to replace if by then string if expression is true
         // or by a white space if not.
         nLength = pszEnd - pszStart;
         pszIfTag = (char*)malloc(nLength + 6);
         strncpy(pszIfTag, pszStart, nLength);
         pszIfTag[nLength] = '\0';
         strcat(pszIfTag, "[/if]");
         
         pszHTValue = msLookupHashTable(ht, pszName);

         if (strcmp(pszOperator, "neq") == 0) {
             if (pszValue && pszHTValue && strcasecmp(pszValue, pszHTValue) != 0)
             {
                 *pszInstr = gsub(*pszInstr, pszIfTag, pszThen);
             }
             else if (pszHTValue)
             {
                 *pszInstr = gsub(*pszInstr, pszIfTag, "");
                 bEmpty = 1;
             }
         }
         else if (strcmp(pszOperator, "eq") == 0) {
             if (pszValue && pszHTValue && strcasecmp(pszValue, pszHTValue) == 0)
             {
                 *pszInstr = gsub(*pszInstr, pszIfTag, pszThen);
             }
             else if (pszHTValue)
             {
                 *pszInstr = gsub(*pszInstr, pszIfTag, "");
                 bEmpty = 1;
             }
         }
         else if (strcmp(pszOperator, "isnull") == 0) {
             if (pszHTValue != NULL)
             {
                 // We met a non-null value... condition is false
                 *pszInstr = gsub(*pszInstr, pszIfTag, "");
                 bEmpty = 1;
             }
             else if (bLastPass)
             {
                 // On last pass, if value is still null then condition is true
                 *pszInstr = gsub(*pszInstr, pszIfTag, pszThen);
             }
         }
         else if (strcmp(pszOperator, "isset") == 0) {
             if (pszHTValue != NULL)
             {
                 // Found a non-null value... condition is true
                 *pszInstr = gsub(*pszInstr, pszIfTag, pszThen);
             }
             else if (bLastPass)
             {
                 // On last pass, if value still not set then condition is false
                 *pszInstr = gsub(*pszInstr, pszIfTag, "");
                 bEmpty = 1;
             }
         }
         else {
             msSetError(MS_WEBERR, "Unsupported operator (%s) in if tag.", 
                        "processIf()", pszOperator);
             return MS_FAILURE;
         }                    

         if (pszIfTag)
             free(pszIfTag);

         pszIfTag = NULL;
      }
      
      if (pszThen)
        free (pszThen);

      pszThen=NULL;
      
      msFreeHashTable(ifArgs);
      ifArgs=NULL;
      
      // find the if start tag
      if (bEmpty)
        pszStart = findTag(pszStart, "if");
      else
        pszStart = findTag(pszStart + 1, "if");
   }
   
   return MS_SUCCESS;
}

/*
** Function to process a [shpxy ...] tag: line contains the tag, shape holds the coordinates. 
**
** TODO's: 
**   - Probably need a seperator for coordinate pairs. 
**   - May need to change attribute names.
**   - Need generalization routines (not here, but in mapprimative.c).
**   - Try to avoid all the realloc calls.
*/
static int processCoords(mapObj *map, char **line, shapeObj *shape) 
{
  int i,j;
  int status;
  
  char *tag, *tagStart, *tagEnd;
  hashTableObj tagArgs=NULL;
  int tagOffset, tagLength;

  char *argValue;
  char *pointFormat;
  int pointFormatLength;

  char *xh=" ", *xf=" "; // various header and footers
  char *yh="", *yf="";  
  char *ph="", *pf=""; // part
  char *sh="", *sf=""; // shape 
  int precision=0;
  int transform=MS_FALSE; // don't clip and convert to image coordinates

  char *coords=NULL, point[128];  
  
  if(!*line) {
    msSetError(MS_WEBERR, "Invalid line pointer.", "processCoords()");
    return(MS_FAILURE);
  }

  tagStart = findTag(*line, "shpxy");

  // It is OK to have no shpxy tags, just return. 
  if( !tagStart )
      return MS_SUCCESS;

  if(!shape || shape->numlines <= 0) { // I suppose we need to make sure the part has vertices (need shape checker?)
    msSetError(MS_WEBERR, "Null or empty shape.", "processCoords()");
    return(MS_FAILURE);
  }

  while (tagStart) {  
    tagOffset = tagStart - *line;
    
    // check for any tag arguments
    if(getTagArgs("shpxy", tagStart, &tagArgs) != MS_SUCCESS) return(MS_FAILURE);
    if(tagArgs) {
      argValue = msLookupHashTable(tagArgs, "xh");
      if(argValue) xh = argValue;
      argValue = msLookupHashTable(tagArgs, "xf");
      if(argValue) xf = argValue;

      argValue = msLookupHashTable(tagArgs, "yh");
      if(argValue) yh = argValue;
      argValue = msLookupHashTable(tagArgs, "yf");
      if(argValue) yf = argValue;

      argValue = msLookupHashTable(tagArgs, "ph");
      if(argValue) ph = argValue;
      argValue = msLookupHashTable(tagArgs, "pf");
      if(argValue) pf = argValue;

      argValue = msLookupHashTable(tagArgs, "sh");
      if(argValue) sh = argValue;
      argValue = msLookupHashTable(tagArgs, "sf");
      if(argValue) sf = argValue;

      argValue = msLookupHashTable(tagArgs, "precision");
      if(argValue) precision = atoi(argValue);

      argValue = msLookupHashTable(tagArgs, "transform");
      if(argValue) {
	transform = MS_TRUE;       
        precision = 0;
      }
    }

    // build the per point format string
    pointFormatLength = strlen("xh") + strlen("xf") + strlen("yh") + strlen("yf") + 10 + 1;
    pointFormat = (char *) malloc(pointFormatLength);
    snprintf(pointFormat, pointFormatLength, "%s%%.%dlf%s%s%%.%dlf%s", xh, precision, xf, yh, precision, yf); 
    
    // no big deal to convert from file to image coordinates, but what are the image parameters
    if(transform) {
      shapeObj tempShape;

      msInitShape(&tempShape);
      status = msCopyShape(shape, &tempShape);
      if(status != 0) return(MS_FAILURE); // copy failed

      switch(tempShape.type) {
      case(MS_SHAPE_POINT):
        // at this point we only convert the first point of the first shape
	tempShape.line[0].point[0].x = MS_MAP2IMAGE_X(tempShape.line[0].point[0].x, map->extent.minx, map->cellsize);
        tempShape.line[0].point[0].y = MS_MAP2IMAGE_Y(tempShape.line[0].point[0].y, map->extent.maxy, map->cellsize);
	break;
      case(MS_SHAPE_LINE):
	msClipPolylineRect(&tempShape, map->extent);
	break;
      case(MS_SHAPE_POLYGON):
        msClipPolygonRect(&tempShape, map->extent);
        break;
      default:
        // TO DO: need an error message here 
        return(MS_FAILURE);
	break;
      }
      msTransformShapeToPixel(&tempShape, map->extent, map->cellsize);

      // build the coordinate string (from tempShape)
      if(strlen(sh) > 0) coords = strcatalloc(coords, sh);
      for(i=0; i<tempShape.numlines; i++) {      
        if(strlen(ph) > 0) coords = strcatalloc(coords, ph);
        for(j=0; j<tempShape.line[i].numpoints; j++) {
          snprintf(point, 128, pointFormat, tempShape.line[i].point[j].x, tempShape.line[i].point[j].y);
          coords = strcatalloc(coords, point);  
        }
        if(strlen(pf) > 0) coords = strcatalloc(coords, pf);
      }
      if(strlen(sf) > 0) coords = strcatalloc(coords, sf);

      msFreeShape(&tempShape);
    } else {	
      // build the coordinate string (from shape)   
      if(strlen(sh) > 0) coords = strcatalloc(coords, sh);
      for(i=0; i<shape->numlines; i++) {      
        if(strlen(ph) > 0) coords = strcatalloc(coords, ph);
        for(j=0; j<shape->line[i].numpoints; j++) {
          snprintf(point, 128, pointFormat, shape->line[i].point[j].x, shape->line[i].point[j].y);
          coords = strcatalloc(coords, point);  
        }
        if(strlen(pf) > 0) coords = strcatalloc(coords, pf);
      }
      if(strlen(sf) > 0) coords = strcatalloc(coords, sf);
    }

    // find the end of the tag
    tagEnd = strchr(tagStart, ']');
    tagEnd++;

    // build the complete tag so we can do substitution           
    tagLength = tagEnd - tagStart;
    tag = (char *) malloc(tagLength + 1);
    strncpy(tag, tagStart, tagLength);
    tag[tagLength] = '\0';

    // do the replacement
    *line = gsub(*line, tag, coords);

    // clean up
    free(tag); tag = NULL;
    msFreeHashTable(tagArgs); tagArgs=NULL;
    free(pointFormat);
    free(coords);

    if((*line)[tagOffset] != '\0')
      tagStart = findTag(*line+tagOffset+1, "shpxy");
    else
      tagStart = NULL;  
  }

  return(MS_SUCCESS);
}

/*!
 * this function process all metadata
 * in pszInstr. ht mus contain all corresponding
 * metadata value.
 * 
 * this function return a modified pszInstr
*/
int processMetadata(char** pszInstr, hashTableObj ht)
{
//   char *pszNextInstr = pszInstr;
   char *pszEnd, *pszStart;
   char *pszMetadataTag;
   char *pszHashName;
   char *pszHashValue;
   int nLength, nOffset;

   hashTableObj metadataArgs = NULL;

   if (!*pszInstr) {
     msSetError(MS_WEBERR, "Invalid pointer.", "processMetadata()");
     return MS_FAILURE;
   }

   // set position to the begining of metadata tag
   pszStart = findTag(*pszInstr, "metadata");

   while (pszStart) {
      // get metadata args
      if (getTagArgs("metadata", pszStart, &metadataArgs) != MS_SUCCESS)
        return MS_FAILURE;

      pszHashName = msLookupHashTable(metadataArgs, "name");
      pszHashValue = msLookupHashTable(ht, pszHashName);
      
      nOffset = pszStart - *pszInstr;

      if (pszHashName && pszHashValue) {
           // set position to the end of metadata start tag
           pszEnd = strchr(pszStart, ']');
           pszEnd++;

           // build the complete metadata tag ([metadata all_args])
           // to replace it by the corresponding value from ht
           nLength = pszEnd - pszStart;
           pszMetadataTag = (char*)malloc(nLength + 1);
           strncpy(pszMetadataTag, pszStart, nLength);
           pszMetadataTag[nLength] = '\0';

           *pszInstr = gsub(*pszInstr, pszMetadataTag, pszHashValue);

           free(pszMetadataTag);
           pszMetadataTag=NULL;
      }

      msFreeHashTable(metadataArgs);
      metadataArgs=NULL;


      // set position to the begining of the next metadata tag
      if ((*pszInstr)[nOffset] != '\0')
        pszStart = findTag(*pszInstr+nOffset+1, "metadata");
      else
        pszStart = NULL;
   }

   return MS_SUCCESS;
}

/*!
 * this function process all icon tag
 * from pszInstr.
 * 
 * This func return a modified pszInstr.
*/
int processIcon(mapObj *map, int nIdxLayer, int nIdxClass, char** pszInstr, char* pszPrefix)
{
   int nWidth, nHeight, nLen;
   char szImgFname[1024], *pszFullImgFname=NULL, *pszImgTag;
   char szPath[MS_MAXPATHLEN];
   hashTableObj myHashTable=NULL;
   FILE *fIcon;
   
   if (!map || 
       nIdxLayer > map->numlayers || 
       nIdxLayer < 0 ) {
     msSetError(MS_WEBERR, "Invalid pointer.", "processIcon()");
     return MS_FAILURE;
   }

   // find the begining of tag
   pszImgTag = strstr(*pszInstr, "[leg_icon");
   
   while (pszImgTag) {

      if (getTagArgs("leg_icon", pszImgTag, &myHashTable) != MS_SUCCESS)
        return MS_FAILURE;

      // if no specified width or height, set them to map default
      if (!msLookupHashTable(myHashTable, "width") || !msLookupHashTable(myHashTable, "height")) {
         nWidth = map->legend.keysizex;
         nHeight= map->legend.keysizey;
      }
      else {
         nWidth  = atoi(msLookupHashTable(myHashTable, "width"));
         nHeight = atoi(msLookupHashTable(myHashTable, "height"));
      }

      snprintf(szImgFname, 1024, "%s_%d_%d_%d_%d.%s%c", pszPrefix, nIdxLayer, nIdxClass, nWidth, nHeight, MS_IMAGE_EXTENSION(map->outputformat),'\0');

      pszFullImgFname = strdup(msBuildPath3(szPath, map->mappath, 
                                            map->web.imagepath, szImgFname));
      
      // check if icon already exist in cache
      if ((fIcon = fopen(pszFullImgFname, "r+")) != NULL)
      {
         char cTmp[1];
         
         fseek(fIcon, 0, SEEK_SET);
         fread(cTmp, 1, 1, fIcon);
         fseek(fIcon, 0, SEEK_SET);         
         fwrite(cTmp, 1, 1, fIcon);
         fclose(fIcon);
      }
      else
      {
         // Create an image corresponding to the current class
          imageObj *img=NULL;

         if (map->layers[nIdxLayer].numclasses <= 0 || 
             nIdxClass > map->layers[nIdxLayer].numclasses || nIdxClass < 0)
         {
             // Nonexistent class.  Create an empty image
             img = msCreateLegendIcon(map, NULL, NULL, nWidth, nHeight);
         }
         else
         {
            img = msCreateLegendIcon(map, &(map->layers[nIdxLayer]), 
                                     &(map->layers[nIdxLayer].class[nIdxClass]), 
                                     nWidth, nHeight);
         }

         if(!img) {
            if (myHashTable)
              msFreeHashTable(myHashTable);

            msSetError(MS_GDERR, "Error while creating GD image.", "processIcon()");
            return MS_FAILURE;
         }
         
         // save it with a unique file name
         if(msSaveImage(map, img, pszFullImgFname) != MS_SUCCESS) {
            if (myHashTable)
              msFreeHashTable(myHashTable);

            msFree(pszFullImgFname);
            msFreeImage(img);

            msSetError(MS_IOERR, "Error while save GD image to disk (%s).", "processIcon()", pszFullImgFname);
            return MS_FAILURE;
         }
         
         msFreeImage(img);
      }

      msFree(pszFullImgFname);
      pszFullImgFname = NULL;

      nLen = (strchr(pszImgTag, ']') + 1) - pszImgTag;
   
      if (nLen > 0) {
         char *pszTag;

         // rebuid image tag ([leg_class_img all_args])
         // to replace it by the image url
         pszTag = (char*)malloc(nLen + 1);
         strncpy(pszTag, pszImgTag, nLen);
            
         pszTag[nLen] = '\0';

         pszFullImgFname = (char*)malloc(strlen(map->web.imageurl) + strlen(szImgFname) + 1);
         strcpy(pszFullImgFname, map->web.imageurl);
         strcat(pszFullImgFname, szImgFname);

         *pszInstr = gsub(*pszInstr, pszTag, pszFullImgFname);

         msFree(pszFullImgFname);
         pszFullImgFname = NULL;
         msFree(pszTag);

         // find the begining of tag
         pszImgTag = strstr(*pszInstr, "[leg_icon");
      }
      else {
         pszImgTag = NULL;
      }
      
      if (myHashTable)
      {
         msFreeHashTable(myHashTable);
         myHashTable = NULL;
      }
   }

   return MS_SUCCESS;
}

/*!
 * Replace all tags from group template
 * with correct value.
 * 
 * this function return a buffer containing
 * the template with correct values.
 * 
 * buffer must be freed by caller.
*/
int generateGroupTemplate(char* pszGroupTemplate, mapObj *map, char* pszGroupName, char **pszTemp, char* pszPrefix)
{
   hashTableObj myHashTable;
   char pszStatus[3];   
   char *pszClassImg;
   int i, j;

   *pszTemp = NULL;
   
   if (!pszGroupName || !pszGroupTemplate) {
     msSetError(MS_WEBERR, "Invalid pointer.", "generateGroupTemplate()");
     return MS_FAILURE;
   }
   
   /*
    * Work from a copy
    */
   *pszTemp = (char*)malloc(strlen(pszGroupTemplate) + 1);
   strcpy(*pszTemp, pszGroupTemplate);
         
   /*
    * Change group tags
    */
   *pszTemp = gsub(*pszTemp, "[leg_group_name]", pszGroupName);

   
   /*
    * Create a hash table that contain info
    * on current layer
    */
   myHashTable = msCreateHashTable();
   
   /*
    * Check for the first layer
    * that belong to this group.
    * Get his status and check for if.
    */
   for (j=0; j<map->numlayers; j++)
   {
      if (map->layers[map->layerorder[j]].group && strcmp(map->layers[map->layerorder[j]].group, pszGroupName) == 0)
      {
         sprintf(pszStatus, "%d", map->layers[map->layerorder[j]].status);
         msInsertHashTable(myHashTable, "layer_status", pszStatus);
   
         if (processIf(pszTemp, myHashTable, MS_FALSE) != MS_SUCCESS)
           return MS_FAILURE;
         
         if (processIf(pszTemp, map->layers[map->layerorder[j]].metadata, MS_FALSE) != MS_SUCCESS)
           return MS_FAILURE;

         if (processMetadata(pszTemp, map->layers[map->layerorder[j]].metadata) != MS_SUCCESS)
           return MS_FAILURE;         
         
         break;
      }
   }
  
   msFreeHashTable(myHashTable);

   /*
    * Process all metadata tags
    * only web object is accessible
   */
   if (processMetadata(pszTemp, map->web.metadata) != MS_SUCCESS)
     return MS_FAILURE;
   
   /*
    * check for if tag
   */
   if (processIf(pszTemp, map->web.metadata, MS_TRUE) != MS_SUCCESS)
     return MS_FAILURE;
   
   /*
    * Check if leg_icon tag exist
    * if so display the first layer first class icon
    */
   pszClassImg = strstr(*pszTemp, "[leg_icon");
   if (pszClassImg) {
      // find first layer of this group
      for (i=0; i<map->numlayers; i++)
        if (map->layers[map->layerorder[i]].group && strcmp(map->layers[map->layerorder[i]].group, pszGroupName) == 0)
          processIcon(map, map->layerorder[i], 0, pszTemp, pszPrefix);
   }      
      
   return MS_SUCCESS;
}

/*!
 * Replace all tags from layer template
 * with correct value.
 * 
 * this function return a buffer containing
 * the template with correct values.
 * 
 * buffer must be freed by caller.
*/
int generateLayerTemplate(char *pszLayerTemplate, mapObj *map, int nIdxLayer, hashTableObj oLayerArgs, char **pszTemp, char* pszPrefix)
{
   hashTableObj myHashTable;
   char szStatus[10];
   char szType[10];
   
   int nOptFlag=0;
   char *pszOptFlag = NULL;
   char *pszClassImg;

   *pszTemp = NULL;
   
   if (!pszLayerTemplate || 
       !map || 
       nIdxLayer > map->numlayers ||
       nIdxLayer < 0 ) {
     msSetError(MS_WEBERR, "Invalid pointer.", "generateLayerTemplate()");
     return MS_FAILURE;
   }

   if (oLayerArgs)
       pszOptFlag = msLookupHashTable(oLayerArgs, "opt_flag");

   if (pszOptFlag)
     nOptFlag = atoi(pszOptFlag);

   // don't display deleted layers
   if (map->layers[nIdxLayer].status == MS_DELETE)
     return MS_SUCCESS;

   // dont display layer is off.
   // check this if Opt flag is not set
   if((nOptFlag & 2) == 0 && map->layers[nIdxLayer].status == MS_OFF)
     return MS_SUCCESS;

   // dont display layer is query.
   // check this if Opt flag is not set
   if ((nOptFlag & 4) == 0  && map->layers[nIdxLayer].type == MS_LAYER_QUERY)
     return MS_SUCCESS;

   // dont display layer is annotation.
   // check this if Opt flag is not set      
   if ((nOptFlag & 8) == 0 && map->layers[nIdxLayer].type == MS_LAYER_ANNOTATION)
     return MS_SUCCESS;      

   // dont display layer if out of scale.
   // check this if Opt flag is not set            
   if ((nOptFlag & 1) == 0) {
      if(map->scale > 0) {
         if((map->layers[nIdxLayer].maxscale > 0) && (map->scale > map->layers[nIdxLayer].maxscale))
           return MS_SUCCESS;
         if((map->layers[nIdxLayer].minscale > 0) && (map->scale <= map->layers[nIdxLayer].minscale))
           return MS_SUCCESS;
      }
   }

   /*
    * Work from a copy
    */
   *pszTemp = strdup(pszLayerTemplate);

   /*
    * Change layer tags
    */
   *pszTemp = gsub(*pszTemp, "[leg_layer_name]", map->layers[nIdxLayer].name);
   
   /*
    * Create a hash table that contain info
    * on current layer
    */
   myHashTable = msCreateHashTable();
   
   /*
    * for now, only status and type is required by template
    */
   sprintf(szStatus, "%d", map->layers[nIdxLayer].status);
   msInsertHashTable(myHashTable, "layer_status", szStatus);

   sprintf(szType, "%d", map->layers[nIdxLayer].type);
   msInsertHashTable(myHashTable, "layer_type", szType);

   msInsertHashTable(myHashTable, "layer_name", map->layers[nIdxLayer].name);
   msInsertHashTable(myHashTable, "layer_group", map->layers[nIdxLayer].group);
   
   if (processIf(pszTemp, myHashTable, MS_FALSE) != MS_SUCCESS)
      return MS_FAILURE;
   
   if (processIf(pszTemp, map->layers[nIdxLayer].metadata, MS_FALSE) != MS_SUCCESS)
      return MS_FAILURE;
   
   if (processIf(pszTemp, map->web.metadata, MS_TRUE) != MS_SUCCESS)
      return MS_FAILURE;

   msFreeHashTable(myHashTable);
   
   /*
    * Check if leg_icon tag exist
    * if so display the first class icon
    */
   pszClassImg = strstr(*pszTemp, "[leg_icon");
   if (pszClassImg) {
      processIcon(map, nIdxLayer, 0, pszTemp, pszPrefix);
   }      

   /* process all metadata tags
    * only current layer and web object
    * metaddata are accessible
   */
   if (processMetadata(pszTemp, map->layers[nIdxLayer].metadata) != MS_SUCCESS)
      return MS_FAILURE;

   if (processMetadata(pszTemp, map->web.metadata) != MS_SUCCESS)
      return MS_FAILURE;      
   
   return MS_SUCCESS;
}

/*!
 * Replace all tags from class template
 * with correct value.
 * 
 * this function return a buffer containing
 * the template with correct values.
 * 
 * buffer must be freed by caller.
*/
int generateClassTemplate(char* pszClassTemplate, mapObj *map, int nIdxLayer, int nIdxClass, hashTableObj oClassArgs, char **pszTemp, char* pszPrefix)
{
   hashTableObj myHashTable;
   char szStatus[10];
   char szType[10];
   
   char *pszClassImg;
   int nOptFlag=0;
   char *pszOptFlag = NULL;

   *pszTemp = NULL;
   
   if (!pszClassTemplate ||
       !map || 
       nIdxLayer > map->numlayers ||
       nIdxLayer < 0 ||
       nIdxClass > map->layers[nIdxLayer].numclasses ||
       nIdxClass < 0) {
        
     msSetError(MS_WEBERR, "Invalid pointer.", "generateClassTemplate()");
     return MS_FAILURE;
   }

   if (oClassArgs)
     pszOptFlag = msLookupHashTable(oClassArgs, "Opt_flag");

   if (pszOptFlag)
     nOptFlag = atoi(pszOptFlag);
      
   // don't display deleted layers
   if (map->layers[nIdxLayer].status == MS_DELETE)
     return MS_SUCCESS;

   // dont display class if layer is off.
   // check this if Opt flag is not set
   if((nOptFlag & 2) == 0 && map->layers[nIdxLayer].status == MS_OFF)
     return MS_SUCCESS;

   // dont display class if layer is query.
   // check this if Opt flag is not set      
   if ((nOptFlag & 4) == 0 && map->layers[nIdxLayer].type == MS_LAYER_QUERY)
     return MS_SUCCESS;
      
   // dont display class if layer is annotation.
   // check this if Opt flag is not set      
   if ((nOptFlag & 8) == 0 && map->layers[nIdxLayer].type == MS_LAYER_ANNOTATION)
     return MS_SUCCESS;
      
   // dont display layer if out of scale.
   // check this if Opt flag is not set
   if ((nOptFlag & 1) == 0) {
      if(map->scale > 0) {
         if((map->layers[nIdxLayer].maxscale > 0) && (map->scale > map->layers[nIdxLayer].maxscale))
           return MS_SUCCESS;
         if((map->layers[nIdxLayer].minscale > 0) && (map->scale <= map->layers[nIdxLayer].minscale))
           return MS_SUCCESS;
      }
   }
      
   /*
    * Work from a copy
    */
   *pszTemp = (char*)malloc(strlen(pszClassTemplate) + 1);
   strcpy(*pszTemp, pszClassTemplate);
         
   /*
    * Change class tags
    */
   *pszTemp = gsub(*pszTemp, "[leg_class_name]", map->layers[nIdxLayer].class[nIdxClass].name);
   *pszTemp = gsub(*pszTemp, "[leg_class_title]", map->layers[nIdxLayer].class[nIdxClass].title);
   
   /*
    * Create a hash table that contain info
    * on current layer
    */
   myHashTable = msCreateHashTable();
   
   /*
    * for now, only status, type, name and group are  required by template
    */
   sprintf(szStatus, "%d", map->layers[nIdxLayer].status);
   msInsertHashTable(myHashTable, "layer_status", szStatus);

   sprintf(szType, "%d", map->layers[nIdxLayer].type);
   msInsertHashTable(myHashTable, "layer_type", szType);   
   
   msInsertHashTable(myHashTable, "layer_name", map->layers[nIdxLayer].name);
   msInsertHashTable(myHashTable, "layer_group", map->layers[nIdxLayer].group);
   
   if (processIf(pszTemp, myHashTable, MS_FALSE) != MS_SUCCESS)
      return MS_FAILURE;
   
   if (processIf(pszTemp, map->layers[nIdxLayer].metadata, MS_FALSE) != MS_SUCCESS)
      return MS_FAILURE;
   
   if (processIf(pszTemp, map->web.metadata, MS_TRUE) != MS_SUCCESS)
      return MS_FAILURE;

   msFreeHashTable(myHashTable);   
      
   /*
    * Check if leg_icon tag exist
    */
   pszClassImg = strstr(*pszTemp, "[leg_icon");
   if (pszClassImg) {
      processIcon(map, nIdxLayer, nIdxClass, pszTemp, pszPrefix);
   }

   /* process all metadata tags
    * only current layer and web object
    * metaddata are accessible
   */
   if (processMetadata(pszTemp, map->layers[nIdxLayer].metadata) != MS_SUCCESS)
      return MS_FAILURE;
   
   if (processMetadata(pszTemp, map->web.metadata) != MS_SUCCESS)
      return MS_FAILURE;      
   
   return MS_SUCCESS;
}

char *generateLegendTemplate(mapservObj *msObj)
{
   FILE *stream;
   char *file = NULL;
   int length;
   char *pszResult = NULL;
   char *legGroupHtml = NULL;
   char *legLayerHtml = NULL;
   char *legClassHtml = NULL;
   char *legLayerHtmlCopy = NULL;
   char *legClassHtmlCopy = NULL;
   char *legGroupHtmlCopy = NULL;
   
   char *pszPrefix = NULL;
   char *pszMapFname = NULL;
   
   struct stat tmpStat;
   
   char *pszOrderMetadata = NULL;
   char *pszOrder = NULL;
   
   int i,j,k;
   char **papszGroups = NULL;
   int nGroupNames = 0;

   int nLegendOrder = 0;
   char *pszOrderValue;
     
   hashTableObj groupArgs = NULL;
   hashTableObj layerArgs = NULL;
   hashTableObj classArgs = NULL;     

   regex_t re; /* compiled regular expression to be matched */ 

   int  *panCurrentDrawingOrder = NULL;
   char szPath[MS_MAXPATHLEN];

   if(regcomp(&re, MS_TEMPLATE_EXPR, REG_EXTENDED|REG_NOSUB) != 0) {
      msSetError(MS_IOERR, "Error regcomp.", "generateLegendTemplate()");      
      return NULL;
   }

   if(regexec(&re, msObj->Map->legend.template, 0, NULL, 0) != 0) { /* no match */
      msSetError(MS_IOERR, "Invalid template file name.", "generateLegendTemplate()");      
     regfree(&re);
     return NULL;
   }
   regfree(&re);

/* -------------------------------------------------------------------- */
/*      Save the current drawing order. The drawing order is reset      */
/*      at the end of the function.                                     */
/* -------------------------------------------------------------------- */
   if (msObj && msObj->Map && msObj->Map->numlayers > 0)
   {
       panCurrentDrawingOrder = 
           (int *)malloc(sizeof(int)*msObj->Map->numlayers); 
      
       for (i=0; i<msObj->Map->numlayers; i++)
       {
           if (msObj->Map->layerorder)
               panCurrentDrawingOrder[i] = msObj->Map->layerorder[i];
           else
             panCurrentDrawingOrder[i] = i;  
       }
   }

   /*
    * build prefix filename
    * for legend icon creation
   */
   for(i=0;i<msObj->request->NumParams;i++) // find the mapfile parameter first
     if(strcasecmp(msObj->request->ParamNames[i], "map") == 0) break;
  
   if(i == msObj->request->NumParams)
   {
       if ( getenv("MS_MAPFILE"))
           pszMapFname = strcatalloc(pszMapFname, getenv("MS_MAPFILE"));
   }
   else 
   {
      if(getenv(msObj->request->ParamValues[i])) // an environment references the actual file to use
        pszMapFname = strcatalloc(pszMapFname, getenv(msObj->request->ParamValues[i]));
      else
        pszMapFname = strcatalloc(pszMapFname, msObj->request->ParamValues[i]);
   }
   
   if (pszMapFname)
   {
       if (stat(pszMapFname, &tmpStat) != -1)
       {
           int nLen;

           nLen = (msObj->Map->name?strlen(msObj->Map->name):0)  + 50;
           pszPrefix = (char*)malloc((nLen+1) * sizeof(char));
           if (pszPrefix == NULL) {

           }
           snprintf(pszPrefix, nLen, "%s_%ld_%ld", 
                    msObj->Map->name, tmpStat.st_size, tmpStat.st_mtime);
           pszPrefix[nLen] = '\0';
       }
   
       free(pszMapFname);
       pszMapFname = NULL;
   }
   else
   {
/* -------------------------------------------------------------------- */
/*      map file name may not be avaible when the template functions    */
/*      are called from mapscript. Use the time stamp as prefix.        */
/* -------------------------------------------------------------------- */
       char pszTime[20];
       
       snprintf(pszTime, 20, "%ld", (long)time(NULL));      
       pszPrefix = strcatalloc(pszPrefix, pszTime);
   }

       // open template
   if((stream = fopen(msBuildPath(szPath, msObj->Map->mappath, msObj->Map->legend.template), "r")) == NULL) {
      msSetError(MS_IOERR, "Error while opening template file.", "generateLegendTemplate()");
      return NULL;
   } 

   fseek(stream, 0, SEEK_END);
   length = ftell(stream);
   rewind(stream);
   
   file = (char*)malloc(length + 1);

   if (!file) {
     msSetError(MS_IOERR, "Error while allocating memory for template file.", "generateLegendTemplate()");
     return NULL;
   }
   
   /*
    * Read all the template file
    */
   fread(file, 1, length, stream);
   file[length] = '\0';

   /*
    * Seperate groups, layers and class
    */
   getInlineTag("leg_group_html", file, &legGroupHtml);
   getInlineTag("leg_layer_html", file, &legLayerHtml);
   getInlineTag("leg_class_html", file, &legClassHtml);

   /*
    * Retrieve arguments of all three parts
    */
   if (legGroupHtml) 
     if (getTagArgs("leg_group_html", file, &groupArgs) != MS_SUCCESS)
       return NULL;
   
   if (legLayerHtml) 
     if (getTagArgs("leg_layer_html", file, &layerArgs) != MS_SUCCESS)
       return NULL;
   
   if (legClassHtml) 
     if (getTagArgs("leg_class_html", file, &classArgs) != MS_SUCCESS)
       return NULL;

      
   msObj->Map->cellsize = msAdjustExtent(&(msObj->Map->extent), 
                                         msObj->Map->width, 
                                         msObj->Map->height);
   if(msCalculateScale(msObj->Map->extent, msObj->Map->units, 
                       msObj->Map->width, msObj->Map->height, 
                       msObj->Map->resolution, &msObj->Map->scale) != MS_SUCCESS)
     return(NULL);
   
   /********************************************************************/

   /*
    * order layers if order_metadata args is set
    * If not, keep default order
    */
   pszOrderMetadata = msLookupHashTable(layerArgs, "order_metadata");
      
   if (sortLayerByMetadata(msObj->Map, pszOrderMetadata) != MS_SUCCESS)
     goto error;
   
/* -------------------------------------------------------------------- */
/*      if the order tag is set to ascending or descending, the         */
/*      current order will be changed to correspond to that.            */
/* -------------------------------------------------------------------- */
   pszOrder = msLookupHashTable(layerArgs, "order");
   if (pszOrder && ((strcasecmp(pszOrder, "ASCENDING") == 0) ||
                    (strcasecmp(pszOrder, "DESCENDING") == 0)))
   {
       if (sortLayerByOrder(msObj->Map, pszOrder) != MS_SUCCESS)
         goto error;
   }
   
   if (legGroupHtml) {
      // retrieve group names
      papszGroups = msGetAllGroupNames(msObj->Map, &nGroupNames);

      for (i=0; i<nGroupNames; i++) {
         // process group tags
         if (generateGroupTemplate(legGroupHtml, msObj->Map, papszGroups[i], &legGroupHtmlCopy, pszPrefix) != MS_SUCCESS)
         {
            if (pszResult)
              free(pszResult);
            pszResult=NULL;
            goto error;
         }
            
         // concatenate it to final result
         pszResult = strcatalloc(pszResult, legGroupHtmlCopy);

/*         
         if (!pszResult)
         {
            if (pszResult)
              free(pszResult);
            pszResult=NULL;
            goto error;
         }
*/
         
         if (legGroupHtmlCopy)
         {
           free(legGroupHtmlCopy);
           legGroupHtmlCopy = NULL;
         }
         
         // for all layers in group
         if (legLayerHtml) {
           for (j=0; j<msObj->Map->numlayers; j++) {
              /*
               * if order_metadata is set and the order
               * value is less than 0, dont display it
               */
              pszOrderMetadata = msLookupHashTable(layerArgs, "order_metadata");
              if (pszOrderMetadata) {
                 pszOrderValue = msLookupHashTable(msObj->Map->layers[msObj->Map->layerorder[j]].metadata, pszOrderMetadata);
                 if (pszOrderValue) {
                    nLegendOrder = atoi(pszOrderValue);
                    if (nLegendOrder < 0)
                      continue;
                 }
              }

              if (msObj->Map->layers[msObj->Map->layerorder[j]].group && strcmp(msObj->Map->layers[msObj->Map->layerorder[j]].group, papszGroups[i]) == 0) {
                 // process all layer tags
                 if (generateLayerTemplate(legLayerHtml, msObj->Map, msObj->Map->layerorder[j], layerArgs, &legLayerHtmlCopy, pszPrefix) != MS_SUCCESS)
                 {
                    if (pszResult)
                      free(pszResult);
                    pszResult=NULL;
                    goto error;
                 }
              
                  
                 // concatenate to final result
                 pszResult = strcatalloc(pszResult, legLayerHtmlCopy);

                 if (legLayerHtmlCopy)
                 {
                    free(legLayerHtmlCopy);
                    legLayerHtmlCopy = NULL;
                 }
                 
            
                 // for all classes in layer
                 if (legClassHtml) {
                    for (k=0; k<msObj->Map->layers[msObj->Map->layerorder[j]].numclasses; k++) {
                       // process all class tags
                       if (!msObj->Map->layers[msObj->Map->layerorder[j]].class[k].name)
                         continue;

                       if (generateClassTemplate(legClassHtml, msObj->Map, msObj->Map->layerorder[j], k, classArgs, &legClassHtmlCopy, pszPrefix) != MS_SUCCESS)
                       {
                          if (pszResult)
                            free(pszResult);
                          pszResult=NULL;
                          goto error;
                       }
                 
               
                       // concatenate to final result
                       pszResult = strcatalloc(pszResult, legClassHtmlCopy);

                       if (legClassHtmlCopy) {
                         free(legClassHtmlCopy);
                         legClassHtmlCopy = NULL;
                       }
                    }
                 }
              }
           }
         }
         else
         if (legClassHtml){ // no layer template specified but class and group template
           for (j=0; j<msObj->Map->numlayers; j++) {
              /*
               * if order_metadata is set and the order
               * value is less than 0, dont display it
               */
              pszOrderMetadata = msLookupHashTable(layerArgs, "order_metadata");
              if (pszOrderMetadata) {
                 pszOrderValue = msLookupHashTable(msObj->Map->layers[msObj->Map->layerorder[j]].metadata, pszOrderMetadata);
                 if (pszOrderValue) {
                    nLegendOrder = atoi(pszOrderValue);
                    if (nLegendOrder < 0)
                      continue;
                 }
              }

              if (msObj->Map->layers[msObj->Map->layerorder[j]].group && strcmp(msObj->Map->layers[msObj->Map->layerorder[j]].group, papszGroups[i]) == 0) {
                 // for all classes in layer
                 if (legClassHtml) {
                    for (k=0; k<msObj->Map->layers[msObj->Map->layerorder[j]].numclasses; k++) {
                       // process all class tags
                       if (!msObj->Map->layers[msObj->Map->layerorder[j]].class[k].name)
                         continue;

                       if (generateClassTemplate(legClassHtml, msObj->Map, msObj->Map->layerorder[j], k, classArgs, &legClassHtmlCopy, pszPrefix) != MS_SUCCESS)
                       {
                          if (pszResult)
                            free(pszResult);
                          pszResult=NULL;
                          goto error;
                       }
                 
               
                       // concatenate to final result
                       pszResult = strcatalloc(pszResult, legClassHtmlCopy);

                       if (legClassHtmlCopy) {
                         free(legClassHtmlCopy);
                         legClassHtmlCopy = NULL;
                       }
                    }
                 }
              }
           }
         }
      }
   }
   else {
      // if no group template specified
      if (legLayerHtml) {
         for (j=0; j<msObj->Map->numlayers; j++) {
            /*
             * if order_metadata is set and the order
             * value is less than 0, dont display it
             */
            pszOrderMetadata = msLookupHashTable(layerArgs, "order_metadata");
            if (pszOrderMetadata) {
               pszOrderValue = msLookupHashTable(msObj->Map->layers[msObj->Map->layerorder[j]].metadata, pszOrderMetadata);
               if (pszOrderValue) {
                  nLegendOrder = atoi(pszOrderValue);
                  if (nLegendOrder < 0)
                    continue;
               }
               else
                  nLegendOrder=0;
            }

            // process a layer tags
            if (generateLayerTemplate(legLayerHtml, msObj->Map, msObj->Map->layerorder[j], layerArgs, &legLayerHtmlCopy, pszPrefix) != MS_SUCCESS)
            {
               if (pszResult)
                 free(pszResult);
               pszResult=NULL;
               goto error;
            }
              
            // concatenate to final result
            pszResult = strcatalloc(pszResult, legLayerHtmlCopy);

            if (legLayerHtmlCopy) {
               free(legLayerHtmlCopy);
               legLayerHtmlCopy = NULL;
            }
            
            // for all classes in layer
            if (legClassHtml) {
               for (k=0; k<msObj->Map->layers[msObj->Map->layerorder[j]].numclasses; k++) {
                  // process all class tags
                  if (!msObj->Map->layers[msObj->Map->layerorder[j]].class[k].name)
                    continue;

                  if (generateClassTemplate(legClassHtml, msObj->Map, msObj->Map->layerorder[j], k, classArgs, &legClassHtmlCopy, pszPrefix) != MS_SUCCESS)
                  {
                     if (pszResult)
                       free(pszResult);
                     pszResult=NULL;
                     goto error;
                  }
          
               
                  // concatenate to final result
                  pszResult = strcatalloc(pszResult, legClassHtmlCopy);
  
                  if (legClassHtmlCopy) {
                    free(legClassHtmlCopy);
                    legClassHtmlCopy = NULL;
                  }
               }
            }         
         }
      }
      else { // if no group and layer template specified
         if (legClassHtml) {
            for (j=0; j<msObj->Map->numlayers; j++) {
               /*
                * if order_metadata is set and the order
                * value is less than 0, dont display it
                */
               pszOrderMetadata = msLookupHashTable(layerArgs, "order_metadata");
               if (pszOrderMetadata) {
                  pszOrderValue = msLookupHashTable(msObj->Map->layers[msObj->Map->layerorder[j]].metadata, pszOrderMetadata);
                  if (pszOrderValue) {
                     nLegendOrder = atoi(pszOrderValue);
                     if (nLegendOrder < 0)
                       continue;
                  }
               }

               for (k=0; k<msObj->Map->layers[msObj->Map->layerorder[j]].numclasses; k++) {
                  if (!msObj->Map->layers[msObj->Map->layerorder[j]].class[k].name)
                    continue;
                  
                  if (generateClassTemplate(legClassHtml, msObj->Map, msObj->Map->layerorder[j], k, classArgs, &legClassHtmlCopy, pszPrefix) != MS_SUCCESS)
                  {
                     if (pszResult)
                       free(pszResult);
                     pszResult=NULL;
                     goto error;
                  }
      
               
                  pszResult = strcatalloc(pszResult, legClassHtmlCopy);

                  if (legClassHtmlCopy) {
                    free(legClassHtmlCopy);
                    legClassHtmlCopy = NULL;
                  }
               }
            }
         }
      }
   }
   
   /*
    * if we reach this point, that mean no error was generated.
    * So check if template is null and initialize it to <space>.
    */
   if (pszResult == NULL)
   {
      pszResult = strcatalloc(pszResult, " ");
   }
   
   
   /********************************************************************/
      
   error:
      
   if (papszGroups) {
      for (i=0; i<nGroupNames; i++)
        msFree(papszGroups[i]);

      msFree(papszGroups);
   }
   
   msFreeHashTable(groupArgs);
   msFreeHashTable(layerArgs);
   msFreeHashTable(classArgs);
   
   msFree(file);
     
   msFree(legGroupHtmlCopy);
   msFree(legLayerHtmlCopy);
   msFree(legClassHtmlCopy);
      
   msFree(legGroupHtml);
   msFree(legLayerHtml);
   msFree(legClassHtml);
   msFree(pszPrefix);

   fclose(stream);

/* -------------------------------------------------------------------- */
/*      Reset the layerdrawing order.                                   */
/* -------------------------------------------------------------------- */
   if (panCurrentDrawingOrder && msObj->Map->layerorder)
   {
       for (i=0; i<msObj->Map->numlayers; i++)
          msObj->Map->layerorder[i] =  panCurrentDrawingOrder[i];

       free(panCurrentDrawingOrder);
   }
   
   return pszResult;
}

char *processOneToManyJoin(mapservObj* msObj, joinObj *join)
{
  int records=MS_FALSE;
  FILE *stream=NULL;
  char *outbuf; 
  char line[MS_BUFFER_LENGTH], *tmpline;
  char szPath[MS_MAXPATHLEN];

  if((outbuf = strdup("")) == NULL) return(NULL); // empty at first

  msJoinPrepare(join, &(msObj->ResultShape)); // execute the join
  while(msJoinNext(join) == MS_SUCCESS) {
    // First time through, deal with the header (if necessary) and open the main template. We only
    // want to do this if there are joined records.
    if(records == MS_FALSE) { 
      if(join->header != NULL) {
        if((stream = fopen(msBuildPath(szPath, msObj->Map->mappath, join->header), "r")) == NULL) {
          msSetError(MS_IOERR, "Error while opening join header file %s.", "processOneToManyJoin()", join->header);
          return(NULL);
        }

        // echo file to the output buffer, no substitutions
        while(fgets(line, MS_BUFFER_LENGTH, stream) != NULL) outbuf = strcatalloc(outbuf, line);

        fclose(stream);
      }

      if((stream = fopen(msBuildPath(szPath, msObj->Map->mappath, join->template), "r")) == NULL) {
        msSetError(MS_IOERR, "Error while opening join template file %s.", "processOneToManyJoin()", join->template);
        return(NULL);
      }      
      
      records = MS_TRUE;
    }
    
    while(fgets(line, MS_BUFFER_LENGTH, stream) != NULL) { // now on to the end of the template
      if(strchr(line, '[') != NULL) {
        tmpline = processLine(msObj, line, QUERY);
        if(!tmpline) return NULL;
        outbuf = strcatalloc(outbuf, tmpline);
        free(tmpline);
      } else // no subs, just echo
        strcatalloc(outbuf, line);
    }
      
    rewind(stream);
  } // next record

  if(records==MS_TRUE && join->footer) {    
    if((stream = fopen(msBuildPath(szPath, msObj->Map->mappath, join->footer), "r")) == NULL) {
      msSetError(MS_IOERR, "Error while opening join footer file %s.", "processOneToManyJoin()", join->footer);
      return(NULL);
    }

    // echo file to the output buffer, no substitutions
    while(fgets(line, MS_BUFFER_LENGTH, stream) != NULL) outbuf = strcatalloc(outbuf, line);
    
    fclose(stream);
  }

  // clear any data associated with the join
  msFreeCharArray(join->values, join->numitems);
  join->values = NULL;

  return(outbuf);
}

char *processLine(mapservObj* msObj, char* instr, int mode)
{
  int i, j;
#define PROCESSLINE_BUFLEN 5120
  char repstr[PROCESSLINE_BUFLEN], substr[PROCESSLINE_BUFLEN], *outstr; // repstr = replace string, substr = sub string
  struct hashObj *tp=NULL;
  char *encodedstr;
   
#ifdef USE_PROJ
  rectObj llextent;
  pointObj llpoint;
#endif

  outstr = strdup(instr); // work from a copy

  outstr = gsub(outstr, "[version]",  msGetVersion());

  snprintf(repstr, PROCESSLINE_BUFLEN, "%s%s%s.%s", msObj->Map->web.imageurl, msObj->Map->name, msObj->Id, MS_IMAGE_EXTENSION(msObj->Map->outputformat));
  outstr = gsub(outstr, "[img]", repstr);
  snprintf(repstr, PROCESSLINE_BUFLEN, "%s%sref%s.%s", msObj->Map->web.imageurl, msObj->Map->name, msObj->Id, MS_IMAGE_EXTENSION(msObj->Map->outputformat));
  outstr = gsub(outstr, "[ref]", repstr);
  
  if (strstr(outstr, "[legend]")) {
     // if there's a template legend specified, use it
     if (msObj->Map->legend.template) {
        char *legendTemplate;

        legendTemplate = generateLegendTemplate(msObj);
        if (legendTemplate) {
          outstr = gsub(outstr, "[legend]", legendTemplate);
     
           free(legendTemplate);
        }
        else // error already generated by (generateLegendTemplate())
          return NULL;
     }
     else { // if not display gif image with all legend icon
        snprintf(repstr, PROCESSLINE_BUFLEN, "%s%sleg%s.%s", msObj->Map->web.imageurl, msObj->Map->name, msObj->Id, MS_IMAGE_EXTENSION(msObj->Map->outputformat));
        outstr = gsub(outstr, "[legend]", repstr);
     }
  }
   
  snprintf(repstr, PROCESSLINE_BUFLEN, "%s%ssb%s.%s", msObj->Map->web.imageurl, msObj->Map->name, msObj->Id, MS_IMAGE_EXTENSION(msObj->Map->outputformat));
  outstr = gsub(outstr, "[scalebar]", repstr);

  if(msObj->SaveQuery) {
    snprintf(repstr, PROCESSLINE_BUFLEN, "%s%s%s%s", msObj->Map->web.imagepath, msObj->Map->name, msObj->Id, MS_QUERY_EXTENSION);
    outstr = gsub(outstr, "[queryfile]", repstr);
  }
  
  if(msObj->SaveMap) {
    snprintf(repstr, PROCESSLINE_BUFLEN, "%s%s%s.map", msObj->Map->web.imagepath, msObj->Map->name, msObj->Id);
    outstr = gsub(outstr, "[map]", repstr);
  }

  snprintf(repstr, PROCESSLINE_BUFLEN, "%s", getenv("HTTP_HOST")); 
  outstr = gsub(outstr, "[host]", repstr);
  snprintf(repstr, PROCESSLINE_BUFLEN, "%s", getenv("SERVER_PORT"));
  outstr = gsub(outstr, "[port]", repstr);
  
  snprintf(repstr, PROCESSLINE_BUFLEN, "%s", msObj->Id);
  outstr = gsub(outstr, "[id]", repstr);
  
  strcpy(repstr, ""); // Layer list for a "GET" request (obsolete, use [layers_esc] instead)
  for(i=0;i<msObj->NumLayers;i++)    
    snprintf(repstr, PROCESSLINE_BUFLEN, "%s&layer=%s", repstr, msObj->Layers[i]);
  outstr = gsub(outstr, "[get_layers]", repstr);
  
  strcpy(repstr, ""); // Layer list for a "POST" request
  for(i=0;i<msObj->NumLayers;i++)
    snprintf(repstr, PROCESSLINE_BUFLEN, "%s%s ", repstr, msObj->Layers[i]);
  trimBlanks(repstr);
  outstr = gsub(outstr, "[layers]", repstr);

  encodedstr = msEncodeUrl(repstr);
  outstr = gsub(outstr, "[layers_esc]", encodedstr);
  free(encodedstr);

  strcpy(repstr, ""); // list of ALL layers that can be toggled
  for(i=0;i<msObj->Map->numlayers;i++)
    if(msObj->Map->layers[i].status != MS_DEFAULT) snprintf(repstr, PROCESSLINE_BUFLEN, "%s%s ", repstr, msObj->Map->layers[i].name);
  trimBlanks(repstr);
  outstr = gsub(outstr, "[toggle_layers]", repstr);

  encodedstr = msEncodeUrl(repstr);
  outstr = gsub(outstr, "[toggle_layers_esc]", encodedstr);
  free(encodedstr);
  

  for(i=0;i<msObj->Map->numlayers;i++) { // Set form widgets (i.e. checkboxes, radio and select lists), note that default layers don't show up here
    if(isOn(msObj, msObj->Map->layers[i].name, msObj->Map->layers[i].group) == MS_TRUE) {
      if(msObj->Map->layers[i].group) {
	sprintf(substr, "[%s_select]", msObj->Map->layers[i].group);
	outstr = gsub(outstr, substr, "selected");
	sprintf(substr, "[%s_check]", msObj->Map->layers[i].group);
	outstr = gsub(outstr, substr, "checked");
      }
      sprintf(substr, "[%s_select]", msObj->Map->layers[i].name);
      outstr = gsub(outstr, substr, "selected");
      sprintf(substr, "[%s_check]", msObj->Map->layers[i].name);
      outstr = gsub(outstr, substr, "checked");
    } else {
      if(msObj->Map->layers[i].group) {
	sprintf(substr, "[%s_select]", msObj->Map->layers[i].group);
	outstr = gsub(outstr, substr, "");
	sprintf(substr, "[%s_check]", msObj->Map->layers[i].group);
	outstr = gsub(outstr, substr, "");
      }
      sprintf(substr, "[%s_select]", msObj->Map->layers[i].name);
      outstr = gsub(outstr, substr, "");
      sprintf(substr, "[%s_check]", msObj->Map->layers[i].name);
      outstr = gsub(outstr, substr, "");
    }
  }

  for(i=-1;i<=1;i++) { /* make zoom direction persistant */
    if(msObj->ZoomDirection == i) {
      sprintf(substr, "[zoomdir_%d_select]", i);
      outstr = gsub(outstr, substr, "selected");
      sprintf(substr, "[zoomdir_%d_check]", i);
      outstr = gsub(outstr, substr, "checked");
    } else {
      sprintf(substr, "[zoomdir_%d_select]", i);
      outstr = gsub(outstr, substr, "");
      sprintf(substr, "[zoomdir_%d_check]", i);
      outstr = gsub(outstr, substr, "");
    }
  }
  
  for(i=MINZOOM;i<=MAXZOOM;i++) { /* make zoom persistant */
    if(msObj->Zoom == i) {
      sprintf(substr, "[zoom_%d_select]", i);
      outstr = gsub(outstr, substr, "selected");
      sprintf(substr, "[zoom_%d_check]", i);
      outstr = gsub(outstr, substr, "checked");
    } else {
      sprintf(substr, "[zoom_%d_select]", i);
      outstr = gsub(outstr, substr, "");
      sprintf(substr, "[zoom_%d_check]", i);
      outstr = gsub(outstr, substr, "");
    }
  }

  // allow web object metadata access in template
  if(msObj->Map->web.metadata && strstr(outstr, "web_")) {
    for(j=0; j<MS_HASHSIZE; j++) {
      if (msObj->Map->web.metadata[j] != NULL) {
	for(tp=msObj->Map->web.metadata[j]; tp!=NULL; tp=tp->next) {            
	  sprintf(substr, "[web_%s]", tp->key);
	  outstr = gsub(outstr, substr, tp->data);  
	  sprintf(substr, "[web_%s_esc]", tp->key);
       
      encodedstr = msEncodeUrl(tp->data);
	  outstr = gsub(outstr, substr, encodedstr);
      free(encodedstr);
	}
      }
    }
  }

  // allow layer metadata access in template
  for(i=0;i<msObj->Map->numlayers;i++) {
    if(msObj->Map->layers[i].metadata && strstr(outstr, msObj->Map->layers[i].name)) {
      for(j=0; j<MS_HASHSIZE; j++) {
	if (msObj->Map->layers[i].metadata[j] != NULL) {
	  for(tp=msObj->Map->layers[i].metadata[j]; tp!=NULL; tp=tp->next) {
	    sprintf(substr, "[%s_%s]", msObj->Map->layers[i].name, tp->key);
	    if(msObj->Map->layers[i].status == MS_ON)
	      outstr = gsub(outstr, substr, tp->data);  
	    else
	      outstr = gsub(outstr, substr, "");
	    sprintf(substr, "[%s_%s_esc]", msObj->Map->layers[i].name, tp->key);
	    if(msObj->Map->layers[i].status == MS_ON) {
          encodedstr = msEncodeUrl(tp->data);
          outstr = gsub(outstr, substr, encodedstr);
          free(encodedstr);
        }
	    else
	      outstr = gsub(outstr, substr, "");
	  }
	}
      }
    }
  }

  sprintf(repstr, "%f", msObj->MapPnt.x);
  outstr = gsub(outstr, "[mapx]", repstr);
  sprintf(repstr, "%f", msObj->MapPnt.y);
  outstr = gsub(outstr, "[mapy]", repstr);
  
  sprintf(repstr, "%f", msObj->Map->extent.minx); // Individual mapextent elements for spatial query building 
  outstr = gsub(outstr, "[minx]", repstr);
  sprintf(repstr, "%f", msObj->Map->extent.maxx);
  outstr = gsub(outstr, "[maxx]", repstr);
  sprintf(repstr, "%f", msObj->Map->extent.miny);
  outstr = gsub(outstr, "[miny]", repstr);
  sprintf(repstr, "%f", msObj->Map->extent.maxy);
  outstr = gsub(outstr, "[maxy]", repstr);
  sprintf(repstr, "%f %f %f %f", msObj->Map->extent.minx, msObj->Map->extent.miny,  msObj->Map->extent.maxx, msObj->Map->extent.maxy);
  outstr = gsub(outstr, "[mapext]", repstr);
   
  encodedstr =  msEncodeUrl(repstr);
  outstr = gsub(outstr, "[mapext_esc]", encodedstr);
  free(encodedstr);
  
  sprintf(repstr, "%f", (msObj->Map->extent.maxx-msObj->Map->extent.minx)); // useful for creating cachable extents (i.e. 0 0 dx dy) with legends and scalebars
  outstr = gsub(outstr, "[dx]", repstr);
  sprintf(repstr, "%f", (msObj->Map->extent.maxy-msObj->Map->extent.miny));
  outstr = gsub(outstr, "[dy]", repstr);

  sprintf(repstr, "%f", msObj->RawExt.minx); // Individual raw extent elements for spatial query building
  outstr = gsub(outstr, "[rawminx]", repstr);
  sprintf(repstr, "%f", msObj->RawExt.maxx);
  outstr = gsub(outstr, "[rawmaxx]", repstr);
  sprintf(repstr, "%f", msObj->RawExt.miny);
  outstr = gsub(outstr, "[rawminy]", repstr);
  sprintf(repstr, "%f", msObj->RawExt.maxy);
  outstr = gsub(outstr, "[rawmaxy]", repstr);
  sprintf(repstr, "%f %f %f %f", msObj->RawExt.minx, msObj->RawExt.miny,  msObj->RawExt.maxx, msObj->RawExt.maxy);
  outstr = gsub(outstr, "[rawext]", repstr);
  
  encodedstr = msEncodeUrl(repstr);
  outstr = gsub(outstr, "[rawext_esc]", encodedstr);
  free(encodedstr);
    
#ifdef USE_PROJ
  if((strstr(outstr, "lat]") || strstr(outstr, "lon]") || strstr(outstr, "lon_esc]"))
     && msObj->Map->projection.proj != NULL
     && !pj_is_latlong(msObj->Map->projection.proj) ) {
    llextent=msObj->Map->extent;
    llpoint=msObj->MapPnt;
    msProjectRect(&(msObj->Map->projection), &(msObj->Map->latlon), &llextent);
    msProjectPoint(&(msObj->Map->projection), &(msObj->Map->latlon), &llpoint);

    sprintf(repstr, "%f", llpoint.x);
    outstr = gsub(outstr, "[maplon]", repstr);
    sprintf(repstr, "%f", llpoint.y);
    outstr = gsub(outstr, "[maplat]", repstr);
    
    sprintf(repstr, "%f", llextent.minx); /* map extent as lat/lon */
    outstr = gsub(outstr, "[minlon]", repstr);
    sprintf(repstr, "%f", llextent.maxx);
    outstr = gsub(outstr, "[maxlon]", repstr);
    sprintf(repstr, "%f", llextent.miny);
    outstr = gsub(outstr, "[minlat]", repstr);
    sprintf(repstr, "%f", llextent.maxy);
    outstr = gsub(outstr, "[maxlat]", repstr);    
    sprintf(repstr, "%f %f %f %f", llextent.minx, llextent.miny,  llextent.maxx, llextent.maxy);
    outstr = gsub(outstr, "[mapext_latlon]", repstr);
     
    encodedstr = msEncodeUrl(repstr);
    outstr = gsub(outstr, "[mapext_latlon_esc]", encodedstr);
    free(encodedstr);
  }
#endif

  sprintf(repstr, "%d %d", msObj->Map->width, msObj->Map->height);
  outstr = gsub(outstr, "[mapsize]", repstr);
   
  encodedstr = msEncodeUrl(repstr);
  outstr = gsub(outstr, "[mapsize_esc]", encodedstr);
  free(encodedstr);

  sprintf(repstr, "%d", msObj->Map->width);
  outstr = gsub(outstr, "[mapwidth]", repstr);
  sprintf(repstr, "%d", msObj->Map->height);
  outstr = gsub(outstr, "[mapheight]", repstr);
  
  sprintf(repstr, "%f", msObj->Map->scale);
  outstr = gsub(outstr, "[scale]", repstr);
  sprintf(repstr, "%f", msObj->Map->cellsize);
  outstr = gsub(outstr, "[cellsize]", repstr);
  
  sprintf(repstr, "%.1f %.1f", (msObj->Map->width-1)/2.0, (msObj->Map->height-1)/2.0);
  outstr = gsub(outstr, "[center]", repstr);
  sprintf(repstr, "%.1f", (msObj->Map->width-1)/2.0);
  outstr = gsub(outstr, "[center_x]", repstr);
  sprintf(repstr, "%.1f", (msObj->Map->height-1)/2.0);
  outstr = gsub(outstr, "[center_y]", repstr);      

  // These are really for situations with multiple result sets only, but often used in header/footer  
  sprintf(repstr, "%d", msObj->NR); // total number of results
  outstr = gsub(outstr, "[nr]", repstr);  
  sprintf(repstr, "%d", msObj->NL); // total number of layers with results
  outstr = gsub(outstr, "[nl]", repstr);

  if(msObj->ResultLayer) {
    sprintf(repstr, "%d", msObj->NLR); // total number of results within this layer
    outstr = gsub(outstr, "[nlr]", repstr);
    sprintf(repstr, "%d", msObj->RN); // sequential (eg. 1..n) result number within all layers
    outstr = gsub(outstr, "[rn]", repstr);
    sprintf(repstr, "%d", msObj->LRN); // sequential (eg. 1..n) result number within this layer
    outstr = gsub(outstr, "[lrn]", repstr);
    outstr = gsub(outstr, "[cl]", msObj->ResultLayer->name); // current layer name    
    // if(ResultLayer->description) outstr = gsub(outstr, "[cd]", ResultLayer->description); // current layer description
  }

  if(mode == QUERY) { // return shape and/or values	

    // allow layer metadata access in a query template, within the context of a query no layer name is necessary    
    if(msObj->ResultLayer->metadata && strstr(outstr, "[metadata_")) {
      for(i=0; i<MS_HASHSIZE; i++) {
	if (msObj->ResultLayer->metadata[i] != NULL) {
	  for(tp=msObj->ResultLayer->metadata[i]; tp!=NULL; tp=tp->next) {
	    sprintf(substr, "[metadata_%s]", tp->key);
            outstr = gsub(outstr, substr, tp->data);  
	     
	    sprintf(substr, "[metadata_%s_esc]", tp->key);	    
            encodedstr = msEncodeUrl(tp->data);
            outstr = gsub(outstr, substr, encodedstr);
            free(encodedstr);
	  }
        }
      }
    }
    
    sprintf(repstr, "%f %f", (msObj->ResultShape.bounds.maxx + msObj->ResultShape.bounds.minx)/2, (msObj->ResultShape.bounds.maxy + msObj->ResultShape.bounds.miny)/2); 
    outstr = gsub(outstr, "[shpmid]", repstr);
    sprintf(repstr, "%f", (msObj->ResultShape.bounds.maxx + msObj->ResultShape.bounds.minx)/2);
    outstr = gsub(outstr, "[shpmidx]", repstr);
    sprintf(repstr, "%f", (msObj->ResultShape.bounds.maxy + msObj->ResultShape.bounds.miny)/2);
    outstr = gsub(outstr, "[shpmidy]", repstr);
    
    sprintf(repstr, "%f %f %f %f", msObj->ResultShape.bounds.minx, msObj->ResultShape.bounds.miny,  msObj->ResultShape.bounds.maxx, msObj->ResultShape.bounds.maxy);
    outstr = gsub(outstr, "[shpext]", repstr);
     
    encodedstr = msEncodeUrl(repstr);
    outstr = gsub(outstr, "[shpext_esc]", encodedstr);
    free(encodedstr);
     
    sprintf(repstr, "%d", msObj->ResultShape.classindex);
    outstr = gsub(outstr, "[shpclass]", repstr);

    if(processCoords(msObj->Map, &outstr, &msObj->ResultShape) != MS_SUCCESS)
      return(NULL);

    sprintf(repstr, "%f", msObj->ResultShape.bounds.minx);
    outstr = gsub(outstr, "[shpminx]", repstr);
    sprintf(repstr, "%f", msObj->ResultShape.bounds.miny);
    outstr = gsub(outstr, "[shpminy]", repstr);
    sprintf(repstr, "%f", msObj->ResultShape.bounds.maxx);
    outstr = gsub(outstr, "[shpmaxx]", repstr);
    sprintf(repstr, "%f", msObj->ResultShape.bounds.maxy);
    outstr = gsub(outstr, "[shpmaxy]", repstr);
    
    sprintf(repstr, "%ld", msObj->ResultShape.index);
    outstr = gsub(outstr, "[shpidx]", repstr);
    sprintf(repstr, "%d", msObj->ResultShape.tileindex);
    outstr = gsub(outstr, "[tileidx]", repstr);  

    for(i=0;i<msObj->ResultLayer->numitems;i++) {	 

      // by default let's encode attributes for HTML presentation
      sprintf(substr, "[%s]", msObj->ResultLayer->items[i]);
      if(strstr(outstr, substr) != NULL) {
	encodedstr = msEncodeHTMLEntities(msObj->ResultShape.values[i]);
	outstr = gsub(outstr, substr, encodedstr);
        free(encodedstr);
      }

      // of course you might want to embed that data in URLs
      sprintf(substr, "[%s_esc]", msObj->ResultLayer->items[i]);
      if(strstr(outstr, substr) != NULL) {
        encodedstr = msEncodeUrl(msObj->ResultShape.values[i]);
        outstr = gsub(outstr, substr, encodedstr);
        free(encodedstr);
      }

      // or you might want to access the attributes unaltered
      sprintf(substr, "[%s_raw]", msObj->ResultLayer->items[i]);
      if(strstr(outstr, substr) != NULL)
	outstr = gsub(outstr, substr, msObj->ResultShape.values[i]);
    }
    
    //
    // handle joins in this next section
    //
    for(i=0; i<msObj->ResultLayer->numjoins; i++) {
      if(msObj->ResultLayer->joins[i].values) { // join has data
        for(j=0;j<msObj->ResultLayer->joins[i].numitems;j++) {
          // by default let's encode attributes for HTML presentation
          sprintf(substr, "[%s_%s]", msObj->ResultLayer->joins[i].name, msObj->ResultLayer->joins[i].items[j]);        
          if(strstr(outstr, substr) != NULL) {
	    encodedstr = msEncodeHTMLEntities(msObj->ResultLayer->joins[i].values[j]);
	    outstr = gsub(outstr, substr, encodedstr);
            free(encodedstr);
          }

          // of course you might want to embed that data in URLs
          sprintf(substr, "[%s_%s_esc]", msObj->ResultLayer->joins[i].name, msObj->ResultLayer->joins[i].items[j]);
          if(strstr(outstr, substr) != NULL) {
            encodedstr = msEncodeUrl(msObj->ResultLayer->joins[i].values[j]);
            outstr = gsub(outstr, substr, encodedstr);
            free(encodedstr);
          }

          // or you might want to access the attributes unaltered
          sprintf(substr, "[%s_%s_raw]", msObj->ResultLayer->joins[i].name, msObj->ResultLayer->joins[i].items[j]);
          if(strstr(outstr, substr) != NULL)
	    outstr = gsub(outstr, substr, msObj->ResultLayer->joins[i].values[j]);
        }
      } else if(msObj->ResultLayer->joins[i].type ==  MS_JOIN_ONE_TO_MANY){ // one-to-many join
	char *joinTemplate=NULL;

	sprintf(substr, "[join_%s]", msObj->ResultLayer->joins[i].name);        
        if(strstr(outstr, substr) != NULL) {
	  joinTemplate = processOneToManyJoin(msObj, &(msObj->ResultLayer->joins[i]));
          if(joinTemplate) {
            outstr = gsub(outstr, substr, joinTemplate);     
            free(joinTemplate);
          } else
            return NULL;
        }
      }
    } // next join

  } // end query mode specific substitutions

  for(i=0;i<msObj->request->NumParams;i++) {
    sprintf(substr, "[%s]", msObj->request->ParamNames[i]);
    outstr = gsub(outstr, substr, msObj->request->ParamValues[i]);
    sprintf(substr, "[%s_esc]", msObj->request->ParamNames[i]);

    encodedstr = msEncodeUrl(msObj->request->ParamValues[i]);
    outstr = gsub(outstr, substr, encodedstr);
    free(encodedstr);
  }

  return(outstr);
}

#define MS_TEMPLATE_BUFFER 1024 //1k

int msReturnPage(mapservObj* msObj, char* html, int mode, char **papszBuffer)
{
  FILE *stream;
  char line[MS_BUFFER_LENGTH], *tmpline;
  int   nBufferSize = 0;
  int   nCurrentSize = 0;
  int   nExpandBuffer = 0;

  regex_t re; /* compiled regular expression to be matched */ 
  char szPath[MS_MAXPATHLEN];

  if(regcomp(&re, MS_TEMPLATE_EXPR, REG_EXTENDED|REG_NOSUB) != 0) {
    msSetError(MS_REGEXERR, NULL, "msReturnPage()");
    return MS_FAILURE;
  }

  if(regexec(&re, html, 0, NULL, 0) != 0) { /* no match */
    regfree(&re);
    msSetError(MS_WEBERR, "Malformed template name.", "msReturnPage()");
    return MS_FAILURE;
  }
  regfree(&re);

  if((stream = fopen(msBuildPath(szPath, msObj->Map->mappath, html), "r")) == NULL) {
    msSetError(MS_IOERR, html, "msReturnPage()");
    return MS_FAILURE;
  } 

  if (papszBuffer)
  {
      if ((*papszBuffer) == NULL)
      {
          (*papszBuffer) = (char *)malloc(MS_TEMPLATE_BUFFER);
          (*papszBuffer)[0] = '\0';
          nBufferSize = MS_TEMPLATE_BUFFER;
          nCurrentSize = 0;
          nExpandBuffer = 1;
      }
      else
      {
          nCurrentSize = strlen((*papszBuffer));
          nBufferSize = nCurrentSize;

          nExpandBuffer = (nCurrentSize/MS_TEMPLATE_BUFFER) +1;
      }
  }
  while(fgets(line, MS_BUFFER_LENGTH, stream) != NULL) { /* now on to the end of the file */

    if(strchr(line, '[') != NULL) {
      tmpline = processLine(msObj, line, mode);
      if (!tmpline)
         return MS_FAILURE;         
   
      if (papszBuffer)
      {
          if (nBufferSize <= (int)(nCurrentSize + strlen(tmpline) + 1))
          {
              nExpandBuffer = (strlen(tmpline) /  MS_TEMPLATE_BUFFER) + 1;

               nBufferSize = 
                   MS_TEMPLATE_BUFFER*nExpandBuffer + strlen((*papszBuffer));

              (*papszBuffer) = 
                  (char *)realloc((*papszBuffer),sizeof(char)*nBufferSize);
          }
          strcat((*papszBuffer), tmpline);
          nCurrentSize += strlen(tmpline);
         
      }
      else
          printf("%s", tmpline);
      free(tmpline);
    } 
    else
    {
        if (papszBuffer)
        {
            if (nBufferSize <= (int)(nCurrentSize + strlen(line)))
            {
                nExpandBuffer = (strlen(line) /  MS_TEMPLATE_BUFFER) + 1;

                nBufferSize = 
                    MS_TEMPLATE_BUFFER*nExpandBuffer + strlen((*papszBuffer));

                (*papszBuffer) = 
                    (char *)realloc((*papszBuffer),sizeof(char)*nBufferSize);
            }
            strcat((*papszBuffer), line);
            nCurrentSize += strlen(line);
        }
        else 
            printf("%s", line);
    }
    if (!papszBuffer)
        fflush(stdout);
  } // next line

  fclose(stream);

  return MS_SUCCESS;
}

int msReturnURL(mapservObj* msObj, char* url, int mode)
{
  char *tmpurl;

  if(url == NULL) {
    msSetError(MS_WEBERR, "Empty URL.", "msReturnURL()");
    return MS_FAILURE;
  }

  tmpurl = processLine(msObj, url, mode);
 
  if (!tmpurl)
     return MS_FAILURE;
   
  msRedirect(tmpurl);
  free(tmpurl);
   
  return MS_SUCCESS;
}


int msReturnQuery(mapservObj* msObj, char* pszMimeType, char **papszBuffer)
{
  int status;
  int i,j,k;
  char buffer[1024];
  int   nBufferSize =0;
  int   nCurrentSize = 0;
  int   nExpandBuffer = 0;

  char *template;

  layerObj *lp=NULL;

  /* -------------------------------------------------------------------- */
  /*      mime type could be null when the function is called from        */
  /*      mapscript (function msProcessQueryTemplate)                     */
  /* -------------------------------------------------------------------- */

  /* if(!pszMimeType) {
    msSetError(MS_WEBERR, "Mime type not specified.", "msReturnQuery()");
    return MS_FAILURE;
  } */

  if(papszBuffer) {
    (*papszBuffer) = (char *)malloc(MS_TEMPLATE_BUFFER);
    (*papszBuffer)[0] = '\0';
    nBufferSize = MS_TEMPLATE_BUFFER;
    nCurrentSize = 0;
    nExpandBuffer = 1;
  }
  
  msInitShape(&(msObj->ResultShape));

  if((msObj->Mode == ITEMQUERY) || (msObj->Mode == QUERY)) { // may need to handle a URL result set

    for(i=(msObj->Map->numlayers-1); i>=0; i--) {
      lp = &(msObj->Map->layers[i]);

      if(!lp->resultcache) continue;
      if(lp->resultcache->numresults > 0) break;
    }

    if(i >= 0) { // at least if no result found, mapserver will display an empty template.

      if(lp->resultcache->results[0].classindex >= 0 && lp->class[(int)(lp->resultcache->results[0].classindex)].template) 
        template = lp->class[(int)(lp->resultcache->results[0].classindex)].template;
      else 
        template = lp->template;

      if( template == NULL )
      {
          msSetError(MS_WEBERR, "No template for layer %s or it's classes.",
                     "msReturnQuery()", lp->name );
          return MS_FAILURE;
      }

      if(TEMPLATE_TYPE(template) == MS_URL) {
        msObj->ResultLayer = lp;

        status = msLayerOpen(lp);
        if(status != MS_SUCCESS) return status;

        // retrieve all the item names
        status = msLayerGetItems(lp);
        if(status != MS_SUCCESS) return status;

        status = msLayerGetShape(lp, &(msObj->ResultShape), lp->resultcache->results[0].tileindex, lp->resultcache->results[0].shapeindex);
        if(status != MS_SUCCESS) return status;

        if(lp->numjoins > 0) {
	  for(k=0; k<lp->numjoins; k++) { 
	    msJoinConnect(lp, &(lp->joins[k]));
	    msJoinPrepare(&(lp->joins[k]), &(msObj->ResultShape));
	    msJoinNext(&(lp->joins[k])); // fetch the first row
	  }
	}

        if(papszBuffer == NULL) {
          if(msReturnURL(msObj, template, QUERY) != MS_SUCCESS) return MS_FAILURE;
        }

        msFreeShape(&(msObj->ResultShape));
        msLayerClose(lp);
        msObj->ResultLayer = NULL;
          
        return MS_SUCCESS;
      }
    }
  }

  msObj->NR = msObj->NL = 0;
  for(i=0; i<msObj->Map->numlayers; i++) { // compute some totals
    lp = &(msObj->Map->layers[i]);

    if(!lp->resultcache) continue;

    if(lp->resultcache->numresults > 0) { 
      msObj->NL++;
      msObj->NR += lp->resultcache->numresults;
    }
  }

  if(papszBuffer && pszMimeType) {
    sprintf(buffer, "Content-type: %s%c%c\n", pszMimeType, 10, 10);
    // sprintf(buffer, "<!-- %s -->\n",  msGetVersion());     

    if(nBufferSize <= (int)(nCurrentSize + strlen(buffer) + 1)) {
      nExpandBuffer++;
      (*papszBuffer) = (char *)realloc((*papszBuffer), MS_TEMPLATE_BUFFER*nExpandBuffer);
      nBufferSize = MS_TEMPLATE_BUFFER*nExpandBuffer;
    }
    strcat((*papszBuffer), buffer);
    nCurrentSize += strlen(buffer);
  } else if(pszMimeType) {
    printf("Content-type: %s%c%c", pszMimeType, 10, 10); // write MIME header
    // printf("<!-- %s -->\n", msGetVersion());
    fflush(stdout);
  }

  if(msObj->Map->web.header) {
    if(msReturnPage(msObj, msObj->Map->web.header, BROWSE, papszBuffer) != MS_SUCCESS) return MS_FAILURE;
  }

  msObj->RN = 1; // overall result number
  for(i=(msObj->Map->numlayers-1); i>=0; i--) {
    msObj->ResultLayer = lp = &(msObj->Map->layers[i]);

    if(!lp->resultcache) continue;
    if(lp->resultcache->numresults <= 0) continue;

    msObj->NLR = lp->resultcache->numresults; 

    if(lp->header) { 
      if(msReturnPage(msObj, lp->header, BROWSE, papszBuffer) != MS_SUCCESS) return MS_FAILURE;
    }

    // open this layer
    status = msLayerOpen(lp);
    if(status != MS_SUCCESS) return status;

    // retrieve all the item names
    status = msLayerGetItems(lp);
    if(status != MS_SUCCESS) return status;

    // open any necessary JOINs here
    if(lp->numjoins > 0) {
      for(k=0; k<lp->numjoins; k++) {
	status = msJoinConnect(lp, &(lp->joins[k]));
	if(status != MS_SUCCESS) return status;        
      }
    }  

    msObj->LRN = 1; // layer result number
    for(j=0; j<lp->resultcache->numresults; j++) {
      status = msLayerGetShape(lp, &(msObj->ResultShape), lp->resultcache->results[j].tileindex, lp->resultcache->results[j].shapeindex);
      if(status != MS_SUCCESS) return status;

      // prepare any necessary JOINs here (one-to-one only)
      if(lp->numjoins > 0) {
	for(k=0; k<lp->numjoins; k++) {
	  if(lp->joins[k].type == MS_JOIN_ONE_TO_ONE) {
	    msJoinPrepare(&(lp->joins[k]), &(msObj->ResultShape));
	    msJoinNext(&(lp->joins[k])); // fetch the first row
	  }
	}
      }

      if(lp->resultcache->results[j].classindex >= 0 && lp->class[(int)(lp->resultcache->results[j].classindex)].template) 
        template = lp->class[(int)(lp->resultcache->results[j].classindex)].template;
      else 
        template = lp->template;

      if(msReturnPage(msObj, template, QUERY, papszBuffer) != MS_SUCCESS) return MS_FAILURE;

      msFreeShape(&(msObj->ResultShape)); // init too

      msObj->RN++; // increment counters
      msObj->LRN++;
    }

    if(lp->footer) {
      if(msReturnPage(msObj, lp->footer, BROWSE, papszBuffer) != MS_SUCCESS) return MS_FAILURE;
    }

    msLayerClose(lp);
    msObj->ResultLayer = NULL;
  }

  if(msObj->Map->web.footer) 
    return msReturnPage(msObj, msObj->Map->web.footer, BROWSE, papszBuffer);

  return MS_SUCCESS;
}


mapservObj*  msAllocMapServObj()
{
   mapservObj* msObj = malloc(sizeof(mapservObj));
   
   msObj->SaveMap=MS_FALSE;
   msObj->SaveQuery=MS_FALSE; // should the query and/or map be saved 

   msObj->request = msAllocCgiObj();

   msObj->Map=NULL;

   msObj->NumLayers=0; /* number of layers specfied by a user */

   msObj->RawExt.minx=-1;
   msObj->RawExt.miny=-1;
   msObj->RawExt.maxx=-1;
   msObj->RawExt.maxy=-1;

   msObj->fZoom=1;
   msObj->Zoom=1; /* default for browsing */
   
   msObj->ResultLayer=NULL;
   
   msObj->UseShapes=MS_FALSE;

   msObj->MapPnt.x=-1;
   msObj->MapPnt.y=-1;

   msObj->ZoomDirection=0; /* whether zooming in or out, default is pan or 0 */

   msObj->Mode=BROWSE; /* can be BROWSE, QUERY, etc. */
   msObj->Id[0]='\0'; /* big enough for time + pid */
   
   msObj->CoordSource=NONE;
   msObj->Scale=0;
   
   msObj->ImgRows=-1;
   msObj->ImgCols=-1;
   
   msObj->ImgExt.minx=-1;
   msObj->ImgExt.miny=-1;
   msObj->ImgExt.maxx=-1;
   msObj->ImgExt.maxy=-1;
   
   msObj->ImgBox.minx=-1;
   msObj->ImgBox.miny=-1;
   msObj->ImgBox.maxx=-1;
   msObj->ImgBox.maxy=-1;
   
   msObj->RefPnt.x=-1;
   msObj->RefPnt.y=-1;
   msObj->ImgPnt.x=-1;
   msObj->ImgPnt.y=-1;

   msObj->Buffer=0;

   /* 
    ** variables for multiple query results processing 
    */
   msObj->RN=0; /* overall result number */
   msObj->LRN=0; /* result number within a layer */
   msObj->NL=0; /* total number of layers with results */
   msObj->NR=0; /* total number or results */
   msObj->NLR=0; /* number of results in a layer */
   
   return msObj;
}

void msFreeMapServObj(mapservObj* msObj)
{
  int i;

  if(msObj) {
    msFreeMap(msObj->Map);

    msFreeCharArray(msObj->request->ParamNames, msObj->request->NumParams);
    msFreeCharArray(msObj->request->ParamValues, msObj->request->NumParams);

    for(i=0;i<msObj->NumLayers;i++) free(msObj->Layers[i]);

    free(msObj);
  }
}


/*
** Utility function to generate map, legend, scalebar and reference
** images.
** Parameters :
**   - msObj : mapserv object (used to extrcat the map object)
**   - szQuery : query file used my mapserv cgi. Set to NULL if not
**               needed
**   - bReturnOnError : if set to TRUE, the function will return on 
**                      the first error. Else it will try to generate
**                      all the images.
**/
int msGenerateImages(mapservObj *msObj, char *szQuery, int bReturnOnError)
{
    char buffer[1024];
    
    if (msObj)
    {
/* -------------------------------------------------------------------- */
/*      rednder map.                                                    */
/* -------------------------------------------------------------------- */
        if(msObj->Map->status == MS_ON) 
        {
            imageObj    *image = NULL;
            if (szQuery)
                image = msDrawQueryMap(msObj->Map);
            else
                image = msDrawMap(msObj->Map);

            if(image)
            { 
                sprintf(buffer, "%s%s%s.%s", msObj->Map->web.imagepath, 
                        msObj->Map->name, msObj->Id, 
                        MS_IMAGE_EXTENSION(msObj->Map->outputformat));	

                if (msSaveImage(msObj->Map, image, buffer) != MS_SUCCESS &&
                    bReturnOnError)
                {
                    msFreeImage(image);
                    return MS_FALSE;
                }
                msFreeImage(image);
            }
            else if (bReturnOnError)
                return MS_FALSE;
        }

/* -------------------------------------------------------------------- */
/*      render legend.                                                  */
/* -------------------------------------------------------------------- */
        if(msObj->Map->legend.status == MS_ON) 
        {
            imageObj    *image;
            image = msDrawLegend(msObj->Map);
            if(image)
            { 
                sprintf(buffer, "%s%sleg%s.%s", msObj->Map->web.imagepath, 
                        msObj->Map->name, msObj->Id, 
                        MS_IMAGE_EXTENSION(msObj->Map->outputformat));
                
                if (msSaveImage(NULL, image, buffer) != MS_SUCCESS &&
                    bReturnOnError)
                {
                    msFreeImage(image);
                    return MS_FALSE;
                }
                msFreeImage(image);
            }
            else if (bReturnOnError)
              return MS_FALSE;
        }

/* -------------------------------------------------------------------- */
/*      render scalebar.                                                */
/* -------------------------------------------------------------------- */
        if(msObj->Map->scalebar.status == MS_ON) 
        {
            imageObj    *image;
            image = msDrawScalebar(msObj->Map);
            if(image)
            {
                sprintf(buffer, "%s%ssb%s.%s", msObj->Map->web.imagepath, 
                        msObj->Map->name, msObj->Id, 
                        MS_IMAGE_EXTENSION(msObj->Map->outputformat));
                if (msSaveImage(NULL, image, buffer) != MS_SUCCESS &&
                    bReturnOnError)
                {
                    msFreeImage(image);
                    return MS_FALSE;
                }
                msFreeImage(image);
            }
            else if (bReturnOnError)
              return MS_FALSE;
        }
        
/* -------------------------------------------------------------------- */
/*      render refernece.                                               */
/* -------------------------------------------------------------------- */
        if(msObj->Map->reference.status == MS_ON) 
        {
            imageObj    *image;
            image = msDrawReferenceMap(msObj->Map);
            if(image)
            { 
                sprintf(buffer, "%s%sref%s.%s", msObj->Map->web.imagepath, 
                        msObj->Map->name, msObj->Id, 
                        MS_IMAGE_EXTENSION(msObj->Map->outputformat));
                if (msSaveImage(NULL, image, buffer) != MS_SUCCESS &&
                    bReturnOnError)
                {
                    msFreeImage(image);
                    return MS_FALSE;
                }
                msFreeImage(image);
            }
            else if (bReturnOnError)
              return MS_FALSE;
        }
        
    }
    return MS_TRUE;
}



/*
** Utility function to open a template file, process it and 
** and return into a buffer the processed template.
** Uses the template file from the web object.
** return NULL if there is an error.
*/ 
char *msProcessTemplate(mapObj *map, int bGenerateImages, 
                        char **names, char **values, 
                        int numentries)
{
    char    *pszBuffer = NULL;

    if (map)
    {
/* -------------------------------------------------------------------- */
/*      initialize object and set values.                               */
/* -------------------------------------------------------------------- */
        mapservObj  *msObj  = NULL;
        msObj = msAllocMapServObj();

        msObj->Map = map;
        msObj->Mode = BROWSE;
        sprintf(msObj->Id, "%ld",(long)time(NULL)); 

        if (names && values && numentries > 0)
        {
            msObj->request->ParamNames = names;
            msObj->request->ParamValues = values;
            msObj->request->NumParams = numentries;    
        }
/* -------------------------------------------------------------------- */
/*      ISSUE/TODO : some of the name/values should be extracted and    */
/*      processed (ex imgext, layers, ...) as it is done in function    */
/*      loadform.                                                       */
/*                                                                      */
/* -------------------------------------------------------------------- */
        if (bGenerateImages)
            msGenerateImages(msObj, NULL, MS_FALSE);
/* -------------------------------------------------------------------- */
/*      process the template.                                           */
/*                                                                      */
/*      TODO : use webminscale/maxscale depending on the scale.         */
/* -------------------------------------------------------------------- */
        if (msReturnPage(msObj, msObj->Map->web.template, 
                         BROWSE, &pszBuffer) == MS_SUCCESS)
        {
            msFree(pszBuffer);
            pszBuffer = NULL;
        }

        // Don't free the map and names and values arrays since they were
        // passed by ref
        msObj->Map = NULL;
        msObj->request->ParamNames = msObj->request->ParamValues = NULL;
        msObj->request->NumParams = 0;
        msFreeMapServObj(msObj);
    }

    return pszBuffer;
}
        


/************************************************************************/
/*                char *msProcessLegendTemplate(mapObj *map,            */
/*                                    char **names, char **values,      */
/*                                    int numentries)                   */
/*                                                                      */
/*      Utility method to process the legend template.                   */
/************************************************************************/
char *msProcessLegendTemplate(mapObj *map,
                              char **names, char **values, 
                              int numentries)
{
    char    *pszOutBuf = NULL;

    if (map && map->legend.template)
    {
/* -------------------------------------------------------------------- */
/*      initialize object and set values.                               */
/* -------------------------------------------------------------------- */
        mapservObj  *msObj  = NULL;
        msObj = msAllocMapServObj();

        msObj->Map = map;
        msObj->Mode = BROWSE;
        sprintf(msObj->Id, "%ld",(long)time(NULL)); 

        if (names && values && numentries > 0)
        {
            msObj->request->ParamNames = names;
            msObj->request->ParamValues = values;
            msObj->request->NumParams = numentries;    
        }

        pszOutBuf = generateLegendTemplate(msObj);

        // Don't free the map and names and values arrays since they were
        // passed by ref
        msObj->Map = NULL;
        msObj->request->ParamNames = msObj->request->ParamValues = NULL;
        msObj->request->NumParams = 0;
        msFreeMapServObj(msObj);
    }

    return pszOutBuf;
}


/************************************************************************/
/*                char *msProcessQueryTemplate(mapObj *map,             */
/*                                   char **names, char **values,       */
/*                                   int numentries)                    */
/*                                                                      */
/*      Utility function that process a template file(s) used in the    */
/*      query and retrun the processed template(s) in a bufffer.        */
/************************************************************************/
char *msProcessQueryTemplate(mapObj *map, int bGenerateImages, 
                             char **names, char **values, 
                             int numentries)
{
    char                *pszBuffer = NULL;

    if (map)
    {
/* -------------------------------------------------------------------- */
/*      initialize object and set values.                               */
/* -------------------------------------------------------------------- */
        mapservObj      *msObj  = NULL;
        msObj = msAllocMapServObj();

        msObj->Map = map;
        msObj->Mode = QUERY;
        sprintf(msObj->Id, "%ld",(long)time(NULL)); 

        if (names && values && numentries > 0)
        {
            msObj->request->ParamNames = names;
            msObj->request->ParamValues = values;
            msObj->request->NumParams = numentries;    
        }
        if (bGenerateImages)
          msGenerateImages(msObj, NULL, MS_FALSE);

        msReturnQuery(msObj, NULL, &pszBuffer );

        // Don't free the map and names and values arrays since they were
        // passed by ref
        msObj->Map = NULL;
        msObj->request->ParamNames = msObj->request->ParamValues = NULL;
        msObj->request->NumParams = 0;
        msFreeMapServObj(msObj);
    }

    return pszBuffer;
}
