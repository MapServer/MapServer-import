/* ===========================================================================
   $Id$
 
   Project:  MapServer
   Purpose:  SWIG interface file for mapscript classObj extensions
   Author:   Steve Lime 
             Sean Gillies, sgillies@frii.com
             
   ===========================================================================
   Copyright (c) 1996-2001 Regents of the University of Minnesota.
   
   Permission is hereby granted, free of charge, to any person obtaining a
   copy of this software and associated documentation files (the "Software"),
   to deal in the Software without restriction, including without limitation
   the rights to use, copy, modify, merge, publish, distribute, sublicense,
   and/or sell copies of the Software, and to permit persons to whom the
   Software is furnished to do so, subject to the following conditions:
 
   The above copyright notice and this permission notice shall be included
   in all copies or substantial portions of the Software.
 
   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS
   OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL
   THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
   DEALINGS IN THE SOFTWARE.
   ===========================================================================
*/

%extend classObj {

    classObj(layerObj *layer) 
    {
        if(layer->numclasses == MS_MAXCLASSES) // no room
            return NULL;

        if(initClass(&(layer->class[layer->numclasses])) == -1)
            return NULL;
        layer->class[layer->numclasses].type = layer->type;

        layer->numclasses++;

        return &(layer->class[layer->numclasses-1]);
    }

    ~classObj() 
    {
        return; // do nothing, map deconstrutor takes care of it all
    }

    int setExpression(char *expression) 
    {
      if (!expression || strlen(expression) == 0) {
          freeExpression(&self->expression);
          return MS_SUCCESS;
      }
      else return loadExpressionString(&self->expression, expression);
  }

  %newobject getExpressionString;
  char *getExpressionString() {
    char exprstring[256];
    switch(self->expression.type) {
    case(MS_REGEX):
      snprintf(exprstring, 255, "/%s/", self->expression.string);
      return strdup(exprstring);
    case(MS_STRING):
      snprintf(exprstring, 255, "\"%s\"", self->expression.string);
      return strdup(exprstring);
    case(MS_EXPRESSION):
      snprintf(exprstring, 255, "(%s)", self->expression.string);
      return strdup(exprstring);
    }
    return NULL;
  }

  // Should be deprecated!  Completely bogus layer argument.  SG.
  int setText(layerObj *layer, char *text) {
    return loadExpressionString(&self->text, text);
  }

//  char *getMetaData(char *name) {
//    return(msLookupHashTable(self->metadata, name));
//  }
  char *getMetaData(char *name) {
    char *value = NULL;
    if (!name) {
      msSetError(MS_HASHERR, "NULL key", "getMetaData");
    }
     
    value = (char *) msLookupHashTable(&(self->metadata), name);
    if (!value) {
      msSetError(MS_HASHERR, "Key %s does not exist", "getMetaData", name);
      return NULL;
    }
    return value;
  }

  int setMetaData(char *name, char *value) {
    //if (!self->metadata)
    //    self->metadata = msCreateHashTable();
    if (msInsertHashTable(&(self->metadata), name, value) == NULL)
        return MS_FAILURE;
    return MS_SUCCESS;
  }

  char *getFirstMetaDataKey() {
    return (char *) msFirstKeyFromHashTable(&(self->metadata));
  }
 
  char *getNextMetaDataKey(char *lastkey) {
    return (char *) msNextKeyFromHashTable(&(self->metadata), lastkey);
  }
  
  int drawLegendIcon(mapObj *map, layerObj *layer, int width, int height, imageObj *dstImage, int dstX, int dstY) {
    return msDrawLegendIcon(map, layer, self, width, height, dstImage->img.gd, dstX, dstY);
  }
 
  %newobject createLegendIcon;
  imageObj *createLegendIcon(mapObj *map, layerObj *layer, int width, int height) {
    return msCreateLegendIcon(map, layer, self, width, height);
  } 

    // See Bugzilla issue 548 for more details about the *Style methods

    styleObj *getStyle(int i) {
        if (i >= 0 && i < self->numstyles)	
            return &(self->styles[i]);
        else {
            msSetError(MS_CHILDERR, "Invalid index: %d", "getStyle()", i);
            return NULL;
        }
    }

    int insertStyle(styleObj *style, int index=-1) {
        return msInsertStyle(self, style, index);
    }

    %newobject removeStyle;
    styleObj *removeStyle(int index) {
        return (styleObj *) msRemoveStyle(self, index);
    }

    int moveStyleUp(int index) {
        return msMoveStyleUp(self, index);
    }

    int moveStyleDown(int index) {
       return msMoveStyleDown(self, index);
    }
}
