/******************************************************************************
 *  filename: mappdf.c
 *  created : Thu Oct  4 09:58:19 2001
 *  @author :  <jwall@webpeak.com> , <jspielberg@webpeak.com>
 *  3.7 support: <zak-ms@aiya.dhs.org>
 * 
 *
 * [$Author$ $Date$]
 * [$Revision$]
 *
 * An api for PDF format output using the pdflib library
 *      http://www.pdflib.com
 *
 ******************************************************************************/
#ifdef USE_PDF

#include <assert.h>
#if !defined(_WIN32)
#include <zlib.h>
#endif
#include "map.h"

/* -------------------------------------------------------------------- */
/*      prototypes.                                                     */
/* -------------------------------------------------------------------- */
/*see map.h*/

/************************************************************************/
/*                        PDF *initializeDocument                       */
/*                                                                      */
/*              Internal function to create a PDF type                  */
/************************************************************************/
PDF *initializeDocument()
{
    /* First we need to make the PDF */
    PDF *pdf = PDF_new();
    PDF_open_file (pdf,"");/*This creates the file in-memory, not on disk */
    PDF_set_info  (pdf, "Creator", "UMN MapServer");
    PDF_set_info  (pdf, "Author", "Implementation for MapServer 3.7 - DM Solutions Group, based on original work by Market Insite Group");
    PDF_set_info  (pdf, "Title", "DM Solutions Group and Market Insite PDF Map");
    return pdf;
}

/************************************************************************/
/*int msLoadFontSetPDF                                                  */
/*                                                                      */
/* load fonts from file                                                 */
/************************************************************************/
int msLoadFontSetPDF(fontSetObj *fontset, PDF *pdf)
{

    FILE *stream;
    char buffer[MS_BUFFER_LENGTH];
    char alias[64], file1[MS_PATH_LENGTH], file2[MS_PATH_LENGTH];
    char *path=NULL, *fullPath, szPath[MS_MAXPATHLEN];
    int i;

    if(fontset == NULL) return(0);
    if(fontset->filename == NULL) return(0);
    
    stream = 
      fopen(msBuildPath(szPath, fontset->map->mappath, fontset->filename), "r");
    
    
    if(!stream)
    {
        msSetError(MS_IOERR, "Error opening fontset %s.", "msLoadFontSetPDF()",
                   fontset->filename);
        return(-1);
    }

    i = 0;
    path = getPath(fontset->filename);

    while(fgets(buffer, MS_BUFFER_LENGTH, stream))
    { /* while there's something to load */
        char *fontParam;

        if(buffer[0] == '#' ||
           buffer[0] == '\n' ||
           buffer[0] == '\r' ||
           buffer[0] == ' ')
            continue; /* skip comments and blank lines */

        fullPath = NULL;
        sscanf(buffer,"%s %s", alias,  file1);

        fullPath = file1;

#if defined(_WIN32) && !defined(__CYGWIN__)
        if(strlen(file1) <= 1 || (file1[0] != '\\' && file1[1] != ':'))
        { /* not a full path */
            sprintf(file2, "%s%s", path, file1);
            fullPath = msBuildPath(szPath, fontset->map->mappath, file2);
        }
#else
       if(file1[0] != '/')
        { /* not full path */
            sprintf(file2, "%s%s", path, file1);
            fullPath = msBuildPath(szPath, fontset->map->mappath, file2);
        }
#endif
 
        /*ok we have the alias and the full name*/
        fontParam = (char *)malloc(sizeof(char)*(strlen(fullPath)+strlen(alias)+3));
        sprintf(fontParam,"%s==%s",alias,fullPath);
        PDF_set_parameter(pdf, "FontOutline", fontParam);
        free(fontParam);
        i++;
    }

    fclose(stream); /* close the file */

    if( path )
        free(path);

    return(0);
}

/************************************************************************/
/*                        imageObj *msImageCreatePDF                    */
/*                                                                      */
/*      Utility function to create an image object of PDF type          */
/************************************************************************/
imageObj *msImageCreatePDF(int width, int height, outputFormatObj *format,
                           char *imagepath, char *imageurl, mapObj *map)
{
    imageObj    *oImage = NULL;
    PDF *pdf = NULL;

    assert( strcasecmp(format->driver,"PDF") == 0 );

    oImage = (imageObj *)calloc(1,sizeof(imageObj));

    oImage->format = format;
    format->refcount++;

    oImage->width = width;
    oImage->height = height;
    oImage->imagepath = NULL;
    oImage->imageurl = NULL;

    if (imagepath)
    {
        oImage->imagepath = strdup(imagepath);
    }
    if (imageurl)
    {
        oImage->imageurl = strdup(imageurl);
    }

    oImage->img.pdf = (PDFObj *)malloc(sizeof(PDFObj));
    oImage->img.pdf->pdf = NULL;
    oImage->img.pdf->pdf = initializeDocument();
    oImage->img.pdf->map = map;
    if(!oImage->img.pdf->pdf)
    {
        msSetError(MS_GDERR, "Unable to initialize pdfPage.", "msDrawMap()");
        return(NULL);
    }

    pdf = oImage->img.pdf->pdf;
    /*  load fonts and set the pdf ready to be drawn into*/
    msLoadFontSetPDF((&(map->fontset)), pdf);
    PDF_begin_page(pdf, width, height);

    /*pdf has it's origin in the bottom left so we need to flip the coordinate*/
    /*system to fit with the rest of mapserver.*/
    PDF_translate(pdf,0,map->height);
    PDF_scale(pdf, 1,-1);

    /*render text with both a fill and a stroke*/
    PDF_set_value(pdf,"textrendering",2);

    return oImage;
}

/************************************************************************/
/* void drawPolylinePDF                                                 */
/*                                                                      */
/* internal function to do line drawing in the pdf                      */
/************************************************************************/
void drawPolylinePDF(PDF *pdf, shapeObj *p, colorObj  *c, double width)
{
    int i, j;

    if (width)
    {
        PDF_setlinejoin(pdf,1);
        PDF_setlinewidth(pdf,(float)width);
    }

    if (c)
    {
        PDF_setrgbcolor(pdf,(float)c->red/255,
                            (float)c->green/255,
                            (float)c->blue/255);
    }
    for (i = 0; i < p->numlines; i++)
    {
        if (p->line[i].numpoints)
        {
            PDF_moveto(pdf,(float)p->line[i].point[0].x,
               (float)p->line[i].point[0].y);
        }
        for(j=1; j<p->line[i].numpoints; j++)
        {
            PDF_lineto(pdf,(float)p->line[i].point[j].x,
               (float)p->line[i].point[j].y);
        }
    }
    PDF_stroke(pdf);
//    PDF_setlinejoin(pdf,0);
    PDF_setlinewidth(pdf,1);

}

/************************************************************************/
/*  void msDrawLineSymbolPDF                                            */
/*                                                                      */
/*  Draw a line symbol of the specified size and color                  */
/************************************************************************/
void msDrawLineSymbolPDF(symbolSetObj *symbolset, imageObj *image, shapeObj *p,
                         styleObj *style, double scalefactor)
{
    int size;
    PDF *pdf;

    size = MS_NINT(style->size*scalefactor);
    pdf = image->img.pdf->pdf;

    if(p->numlines <= 0)
        return;

  /* no such symbol, 0 is OK */
    if(style->symbol > symbolset->numsymbols || style->symbol < 0)
        return;

    if(!(MS_VALID_COLOR(style->color))) /* invalid color */
        return;

    if(size < 1) /* size too small */
        return;

    drawPolylinePDF(pdf, p, &(style->color), size);
    return;
}

/************************************************************************/
/*  void msFilledPolygonPDF                                             */
/*                                                                      */
/*  creates a filled polygon in the pdf from a shape                    */
/*  Note: not part of external api, despite name                        */
/************************************************************************/
void msFilledPolygonPDF(PDF *pdf, shapeObj *p, colorObj  *c)
{
    int i, j;
    if (c){
        PDF_setrgbcolor(pdf,(float)c->red/255,(float)c->green/255,(float)c->blue/255);
    }
    for (i = 0; i < p->numlines; i++){
        if (p->line[i].numpoints){
            PDF_moveto(pdf,p->line[i].point[0].x, p->line[i].point[0].y);
        }
        for(j=1; j<p->line[i].numpoints; j++){
            PDF_lineto(pdf,p->line[i].point[j].x, p->line[i].point[j].y);
        }
    }
    PDF_closepath_fill_stroke(pdf);

}

/************************************************************************/
/*  void billboardPDF                                                   */
/*                                                                      */
/*  creates a filled polygon in the pdf as a background                 */
/************************************************************************/
void billboardPDF(PDF *pdf, shapeObj *shape, labelObj *label)
{
  int i;
  shapeObj temp;

  msInitShape(&temp);
  msAddLine(&temp, &shape->line[0]);

  if(label->backgroundshadowcolor.pen >= 0) {
    for(i=0; i<temp.line[0].numpoints; i++) {
      temp.line[0].point[i].x += label->backgroundshadowsizex;
      temp.line[0].point[i].y += label->backgroundshadowsizey;
    }
    msFilledPolygonPDF(pdf, &temp, &label->backgroundshadowcolor);
    for(i=0; i<temp.line[0].numpoints; i++) {
      temp.line[0].point[i].x -= label->backgroundshadowsizex;
      temp.line[0].point[i].y -= label->backgroundshadowsizey;
    }
  }

  msFilledPolygonPDF(pdf, &temp, &label->backgroundcolor);

  msFreeShape(&temp);
}

/************************************************************************/
/*  void msDrawLabelPDF                                                 */
/*                                                                      */
/*  draws a single label at the specified position                      */
/************************************************************************/
int msDrawLabelPDF(imageObj *image, pointObj labelPnt, char *string,
                   labelObj *label, fontSetObj *fontset, double scalefactor)
{
    if(!string)
        return(0); /* not an error, just don't want to do anything */

    if(strlen(string) == 0)
        return(0); /* not an error, just don't want to do anything */

    if(label->position != MS_XY) {
        pointObj p;
        rectObj r;

        if(msGetLabelSize(string, label, &r, fontset) == -1) return(-1);
        p = get_metrics(&labelPnt, label->position, r,
                                   label->offsetx,
                                   label->offsety,
                                   label->angle,
                                   0, NULL);
        msDrawTextPDF(image, p, string,
                 label, fontset, scalefactor);
    } else {
        labelPnt.x += label->offsetx;
        labelPnt.y += label->offsety;
        msDrawTextPDF(image,labelPnt, string,
                 label, fontset, scalefactor);
    }

    return(0);

}

/************************************************************************/
/*  int msDrawLabelCachePDF                                             */
/*                                                                      */
/*  draws a set of labels                                               */
/************************************************************************/
int msDrawLabelCachePDF(imageObj *image, mapObj *map)
{
    pointObj p;
    int i, j, l;
    rectObj r;
    labelCacheMemberObj *cachePtr=NULL;
    layerObj *layerPtr=NULL;
    labelObj *labelPtr=NULL;

    int draw_marker;
    int marker_width, marker_height;
    int marker_offset_x, marker_offset_y;
    rectObj marker_rect;

    for(l=map->labelcache.numlabels-1; l>=0; l--)
    {
        /* point to right spot in cache */
        cachePtr = &(map->labelcache.labels[l]);

        /* set a couple of other pointers, avoids nasty references */
        layerPtr = &(map->layers[cachePtr->layerindex]);
        //classPtr = &(cachePtr->class);
        labelPtr = &(cachePtr->label);

        if(!cachePtr->string)
            continue; /* not an error, just don't want to do anything */

        if(strlen(cachePtr->string) == 0)
            continue; /* not an error, just don't want to do anything */

        if(msGetLabelSize(cachePtr->string, labelPtr, &r, &(map->fontset)) == -1)
            return(-1);

        if(labelPtr->autominfeaturesize && ((r.maxx-r.minx) > cachePtr->featuresize))
            continue; /* label too large relative to the feature */

        draw_marker = marker_offset_x = marker_offset_y = 0; /* assume no marker */
        if(layerPtr->type == MS_LAYER_ANNOTATION || layerPtr->type == MS_LAYER_POINT)
        { /* there *is* a marker */

            msGetMarkerSize(&map->symbolset, &cachePtr->styles, cachePtr->numstyles,
                            &marker_width, &marker_height);
            marker_offset_x = MS_NINT(marker_width/2.0);
            marker_offset_y = MS_NINT(marker_height/2.0);

            marker_rect.minx = MS_NINT(cachePtr->point.x - .5 * marker_width);
            marker_rect.miny = MS_NINT(cachePtr->point.y - .5 * marker_height);
            marker_rect.maxx = marker_rect.minx + (marker_width-1);
            marker_rect.maxy = marker_rect.miny + (marker_height-1);

            /* actually draw the marker */
            if(layerPtr->type == MS_LAYER_ANNOTATION) draw_marker = 1;
        }

        if(labelPtr->position == MS_AUTO) {

            if(layerPtr->type == MS_LAYER_LINE) {
                int position = MS_UC;
            
                /* Two angles or two positions, depending on angle. Steep angles */
                /* will use the angle approach, otherwise we'll rotate between*/
                /* UC and LC. */
                for(j=0; j<2; j++)
                {
                    msFreeShape(cachePtr->poly);
                    /* assume label *can* be drawn */
                    cachePtr->status = MS_TRUE;

                    if(j == 1)
                    {
                        if(fabs(cos(labelPtr->angle)) < LINE_VERT_THRESHOLD)
                            labelPtr->angle += 180.0;
                        else
                            position = MS_LC;
                    }

                    p = get_metrics(&(cachePtr->point),
                                     position,
                                     r,
                                     (marker_offset_x + labelPtr->offsetx),
                                     (marker_offset_y + labelPtr->offsety),
                                     labelPtr->angle,
                                     labelPtr->buffer,
                                     cachePtr->poly);

                    /*save marker bounding polygon*/
                    if(draw_marker)
                        msRectToPolygon(marker_rect, cachePtr->poly);

                    /*check against image first*/
                    if(!labelPtr->partials)
                    {
                        if(labelInImage(map->width,
                                        map->width,
                                        cachePtr->poly,
                                        labelPtr->buffer) == MS_FALSE)
                        {
                            cachePtr->status = MS_FALSE;
                            /*go to next angle*/
                            continue;
                        }
                    }

                    /* compare against points already drawn*/
                    for(i=0; i<map->labelcache.nummarkers; i++)
                    {
                        /* labels can overlap their own marker*/
                        if(l != map->labelcache.markers[i].id)
                        {
                            /* see if polys intersect */
                            if(intersectLabelPolygons(map->labelcache.markers[i].poly,
                                                      cachePtr->poly) == MS_TRUE)
                            {
                                cachePtr->status = MS_FALSE;
                                break;
                            }
                        }
                    }

                    /*go to next angle*/
                    if(!cachePtr->status)
                        continue;

                    /* compare against rendered labels*/
                    for(i=l+1; i<map->labelcache.numlabels; i++)
                    {
                        /* compare bounding polygons and check for duplicates */
                        if(map->labelcache.labels[i].status == MS_TRUE)
                        {
                            /* check if label is a duplicate */
                            if((labelPtr->mindistance != -1) &&
                                (cachePtr->classindex == map->labelcache.labels[i].classindex) &&
                                (strcmp(cachePtr->string,map->labelcache.labels[i].string) == 0) &&
                                (dist(cachePtr->point, map->labelcache.labels[i].point) <= labelPtr->mindistance))
                            {
                                cachePtr->status = MS_FALSE;
                                break;
                            }

                            /* see if polys intersect */
                            if(intersectLabelPolygons(map->labelcache.labels[i].poly,
                                                      cachePtr->poly) == MS_TRUE)
                            {
                                cachePtr->status = MS_FALSE;
                                break;
                            }
                        }
                    }

                    /*found a suitable place for this label*/
                    if(cachePtr->status)
                        break;

                }  /*next angle*/

            }
            else
            {
                /* loop through the outer label positions */
                for(j=0; j<=7; j++)
                {
                    msFreeShape(cachePtr->poly);
                    /* assume label *can* be drawn */
                    cachePtr->status = MS_TRUE;

                    p = get_metrics(&(cachePtr->point),
                                    j,
                                    r,
                                    (marker_offset_x + labelPtr->offsetx),
                                    (marker_offset_y + labelPtr->offsety),
                                    labelPtr->angle,
                                    labelPtr->buffer,
                                    cachePtr->poly);

                    /* save marker bounding polygon*/
                    if(draw_marker)
                        msRectToPolygon(marker_rect, cachePtr->poly);

                    /*check against image first*/
                    if(!labelPtr->partials)
                    {
                        if(labelInImage(map->width,
                                        map->height,
                                        cachePtr->poly,
                                        labelPtr->buffer) == MS_FALSE)
                        {
                            cachePtr->status = MS_FALSE;
                            /*next position*/
                            continue;
                        }
                    }

                    /* compare against points already drawn*/
                    for(i=0; i<map->labelcache.nummarkers; i++)
                    {
                        /* labels can overlap their own marker*/
                        if(l != map->labelcache.markers[i].id)
                        {
                            /* test if polys intersect */
                            if(intersectLabelPolygons(map->labelcache.markers[i].poly,
                                                      cachePtr->poly) == MS_TRUE)
                            {
                                cachePtr->status = MS_FALSE;
                                break;
                            }
                        }
                    }

                    if(!cachePtr->status)
                        continue; /*go to next position*/

                    /* compare against rendered labels*/
                    for(i=l+1; i<map->labelcache.numlabels; i++)
                    {
                        /* compare bounding polygons and check for duplicates */
                        if(map->labelcache.labels[i].status == MS_TRUE)
                        {

                            /* check if label is a duplicate */
                            if((labelPtr->mindistance != -1) &&
                               (cachePtr->classindex == map->labelcache.labels[i].classindex) &&
                               (strcmp(cachePtr->string,map->labelcache.labels[i].string) == 0) &&
                               (dist(cachePtr->point, map->labelcache.labels[i].point) <= labelPtr->mindistance))
                            {
                                cachePtr->status = MS_FALSE;
                                break;
                            }

                            /* polys intersect? */
                            if(intersectLabelPolygons(map->labelcache.labels[i].poly,
                                                      cachePtr->poly) == MS_TRUE)
                            {
                                cachePtr->status = MS_FALSE;
                                break;
                            }
                        }
                    }

                    /* found a suitable place for this label*/
                    if(cachePtr->status)
                        break;
                } /*next position*/
            }

            /* draw in spite of collisions based on last position, need a *best* position */
            if(labelPtr->force) cachePtr->status = MS_TRUE;
        }
        else
        {
            /* assume label *can* be drawn */
            cachePtr->status = MS_TRUE;

            /*don't need the marker_offset*/
            if(labelPtr->position == MS_CC)
            {
                p = get_metrics(&(cachePtr->point),
                                labelPtr->position,
                                r,
                                labelPtr->offsetx,
                                labelPtr->offsety,
                                labelPtr->angle,
                                labelPtr->buffer,
                                cachePtr->poly);
            }
            else
            {
                p = get_metrics(&(cachePtr->point),
                                labelPtr->position,
                                r,
                                (marker_offset_x + labelPtr->offsetx),
                                (marker_offset_y + labelPtr->offsety),
                                labelPtr->angle,
                                labelPtr->buffer,
                                cachePtr->poly);
             }

            /* save marker bounding polygon, part of overlap tests */
            if(draw_marker)
                msRectToPolygon(marker_rect, cachePtr->poly);

            if(!labelPtr->force)
            { /* no need to check anything else*/

                if(!labelPtr->partials)
                {
                    if(labelInImage(map->width,
                                    map->height,
                                    cachePtr->poly,
                                    labelPtr->buffer) == MS_FALSE)
                        cachePtr->status = MS_FALSE;
                }

                if(!cachePtr->status)
                    continue; /*goto next label*/

                /*compare against points already drawn*/
                for(i=0; i<map->labelcache.nummarkers; i++)
                {
                    /* labels can overlap their own marker*/
                    if(l != map->labelcache.markers[i].id)
                    {
                        /* check if polys intersect */
                        if(intersectLabelPolygons(map->labelcache.markers[i].poly,
                                                  cachePtr->poly) == MS_TRUE)
                        {
                            cachePtr->status = MS_FALSE;
                            break;
                        }
                    }
                }

                if(!cachePtr->status)
                    continue; /*goto next label*/

                /* compare against rendered label*/
                for(i=l+1; i<map->labelcache.numlabels; i++)
                {
                    /* compare bounding polygons and check for duplicates */
                    if(map->labelcache.labels[i].status == MS_TRUE)
                    {
                        /* check if label is a duplicate */
                        if((labelPtr->mindistance != -1) &&
                           (cachePtr->classindex == map->labelcache.labels[i].classindex) &&
                           (strcmp(cachePtr->string, map->labelcache.labels[i].string) == 0) &&
                           (dist(cachePtr->point, map->labelcache.labels[i].point)
                                                        <= labelPtr->mindistance))
                        {
                            cachePtr->status = MS_FALSE;
                            break;
                        }

                        if(intersectLabelPolygons(map->labelcache.labels[i].poly,
                                                  cachePtr->poly) == MS_TRUE)
                        {
                            cachePtr->status = MS_FALSE;
                            break;
                        }
                    }
                }
            }
        } /* end position if-then-else */


        /* next label */
        if(!cachePtr->status)
            continue;

        /* need to draw a marker */
        if(layerPtr->type == MS_LAYER_ANNOTATION && cachePtr->numstyles > 0)
        {
            for(i=0; i<cachePtr->numstyles; i++)
            {
              msDrawMarkerSymbolPDF(&map->symbolset, image, &(cachePtr->point),
                                    &(cachePtr->styles[i]), layerPtr->scalefactor);
            }
        }

        /*handle a filled label background*/
        //TODO
        //if(labelPtr->backgroundcolor >= 0)
        //    billboardPDF(img, cachePtr->poly, labelPtr);

        msDrawTextPDF(image, p, cachePtr->string,
                      labelPtr, &(map->fontset), layerPtr->scalefactor);

    } /* next in cache */

    return(0);
}
/************************************************************************/
/*  void msDrawShadeSymbolPDF                                           */
/*                                                                      */
/*  Draw a shade symbol of the specified size and color                 */
/************************************************************************/
void msDrawShadeSymbolPDF(symbolSetObj *symbolset, imageObj *image,
                          shapeObj *p, styleObj *style, double scalefactor)
{
    int size;
    PDF *pdf;

    size = MS_NINT(style->size*scalefactor);
    pdf = image->img.pdf->pdf;

    if(p->numlines <= 0)
        return;
    /* no such symbol, 0 is OK */
    if(style->symbol > symbolset->numsymbols || style->symbol < 0)
      return;

    if(size < 1) /* size too small */
        return;

    if(MS_VALID_COLOR(style->color))
        msFilledPolygonPDF(pdf, p, &(style->color));

    if(MS_VALID_COLOR(style->outlinecolor))
        drawPolylinePDF(pdf, p, &(style->outlinecolor), size);
    return;
}


/************************************************************************/
/*  void msDrawMarkerSymbolPDF                                          */
/*                                                                      */
/*  Draw a single marker symbol of the specified size and color         */
/************************************************************************/
void msDrawMarkerSymbolPDF(symbolSetObj *symbolset, imageObj *image,
                           pointObj *p, styleObj *style, double scalefactor)
{
    symbolObj *symbol;
    PDF *pdf;
    int offset_x, offset_y, x, y;
    int j,font_id;
    char symbolBuffer[2];
    int size;
    double scale = 1.0;

    pdf = image->img.pdf->pdf;

    /* set the colors */
    // if no outline color, make the stroke and fill the same
    if (!(MS_VALID_COLOR(style->outlinecolor))) style->outlinecolor=style->color;

    PDF_setrgbcolor_stroke(pdf,(float)(style->outlinecolor.red/255),
                                (float)(style->outlinecolor.green/255),
                                (float)(style->outlinecolor.blue/255));
    PDF_setrgbcolor_fill(pdf,(float)(style->color.red/255),
                                (float)(style->color.green/255),
                                (float)(style->color.blue/255));

    /*  set up the symbol scale and type */
    symbol = &(symbolset->symbol[style->symbol]);
    size = MS_NINT(style->size*scalefactor);
    size = MS_MAX(size, style->minsize);
    size = MS_MIN(size, style->maxsize);

    /* no such symbol, 0 is OK */
    if(style->symbol > symbolset->numsymbols || style->symbol < 0)
        return;
    if(size < 1) /* size too small */
        return;

/* -------------------------------------------------------------------- */
/*      Render the diffrent type of symbols.                            */
/* -------------------------------------------------------------------- */
    switch(symbol->type)
    {
/* -------------------------------------------------------------------- */
/*      Symbol : true type.                                             */
/* -------------------------------------------------------------------- */
        case(MS_SYMBOL_TRUETYPE):

/*            font = msLookupHashTable(symbolset->fontset->fonts, symbol->font);*/
/*            if(!font) return;*/
/*                //plot using pdf*/
            sprintf(symbolBuffer,"%c",(char)*symbol->character);
/**/
/*            if (font != NULL){*/
/*                    // we have a match.. set the fonthandle*/
/*                font_id = atoi(font);*/
/*            }*/
/*            else {*/
                    // there was no match so insert a key value pair into the table
                    // this is so that only one font is searched per file
/*                char buffer[5];*/

                font_id = PDF_findfont(pdf, symbol->font ,"winansi",1);
/*                sprintf(buffer, "%d",font_id);*/
/*                msInsertHashTable(symbolset->fontset->fonts, symbol->font, buffer);*/
/*            }*/


            PDF_setfont(pdf,font_id,size+2);
            x = p->x - (int)(.5*PDF_stringwidth(pdf,symbolBuffer,font_id,size));
            y = p->y;
            PDF_setlinewidth(pdf,.15);
            PDF_scale(pdf,1,-1);
            PDF_show_xy(pdf,symbolBuffer,x,-y);
            PDF_scale(pdf,1,-1);

            break;
/* -------------------------------------------------------------------- */
/*      Symbol : pixmap.                                                */
/* -------------------------------------------------------------------- */
        case(MS_SYMBOL_PIXMAP):
        {
            int length;
            char *data;
            int result;
            float imageScale = 1.0;

/*                FILE *pngOut;
            char tempFile[32];
            tempFile[0]=0;

            sprintf(tempFile,"/tmp/%d.png",getpid());
            msSetError(MS_MISCERR, tempFile, "drawPng()");
            pngOut = fopen(tempFile,"wb");
            gdImagePng(symbol->img,pngOut);
            style->colorlose(pngOut);
            result = PDF_open_image_file(pdf,"png",tempFile,"",0);
*/
            if (size>10 && symbol->img->sx > size)
            {
                imageScale = (float)((float)size/(float)symbol->img->sx);
            }

            length = 0;
            data = gdImageJpegPtr(symbol->img, &length, 95);
            result = PDF_open_image(pdf, "jpeg", "memory",
                                    data,
                                    (long)length,
                                    symbol->img->sx,
                                    symbol->img->sy,
                                    3, 8, NULL);
            gdFree(data);

            PDF_scale(pdf,1,-1);
            PDF_place_image(pdf,result,p->x-symbol->img->sx/2*imageScale,
                            -p->y-symbol->img->sy/2*imageScale,imageScale);
            PDF_scale(pdf,1,-1);

            PDF_close_image(pdf,result);
        

        }
        break;
/* -------------------------------------------------------------------- */
/*      symbol : Ellipse                                                */
/* -------------------------------------------------------------------- */
        case(MS_SYMBOL_ELLIPSE):
                // ok, this is going to be just a circle

            scale = size/symbol->sizey;
            x = MS_NINT(symbol->sizex*scale);
            y = MS_NINT(symbol->sizey*scale);

            PDF_circle(pdf, p->x, p->y, (x)/2);

            if(symbol->filled)
                PDF_fill_stroke(pdf);
            else
                PDF_stroke(pdf);

            break;
/* -------------------------------------------------------------------- */
/*      symbol : Vector.                                                */
/* -------------------------------------------------------------------- */
        case(MS_SYMBOL_VECTOR):

            scale = size/symbol->sizey;
            //set the joins to be mitered - better for small shapes
            PDF_setlinejoin(pdf, 0);

            offset_x = MS_NINT(p->x - scale*.5*symbol->sizex);
            offset_y = MS_NINT(p->y - scale*.5*symbol->sizey);

            PDF_moveto(pdf,
                       MS_NINT(scale*symbol->points[0].x + offset_x),
                       MS_NINT((scale*symbol->points[0].y + offset_y)));
            for(j=0;j < symbol->numpoints;j++)
            {
                if (MS_NINT(symbol->points[j].x >= 0) &&
                    MS_NINT(symbol->points[j].y) >= 0)
                {
                    if (MS_NINT(symbol->points[j-1].x < 0) &&
                        MS_NINT(symbol->points[j-1].y < 0))
                    {
                        PDF_moveto(pdf,
                                   MS_NINT(scale*symbol->points[j].x + offset_x),
                                   MS_NINT((scale*symbol->points[j].y + offset_y)));
                    }
                    else
                    {
                        PDF_lineto(pdf,
                                   MS_NINT(scale*symbol->points[j].x + offset_x),
                                   MS_NINT((scale*symbol->points[j].y + offset_y)));
                    }
                }
            }

            if(symbol->filled)
            { /* if filled */
                PDF_closepath_fill_stroke(pdf);
            }
            else
            { /* NOT filled */
                PDF_stroke(pdf);
            }
            //set the joins back to rounded
            PDF_setlinejoin(pdf, 1);
        
            break;
        default:
            break;
    } /* end switch statement */

    return;
}

/************************************************************************/
/*  int msDrawRasterLayerPDF                                            */
/*                                                                      */
/*  adds a raster image to the pdf.                                     */
/************************************************************************/
int msDrawRasterLayerPDF(mapObj *map, layerObj *layer, imageObj *image)
{
    outputFormatObj *format = NULL;
    imageObj    *image_tmp = NULL;
    PDF *pdf = NULL;
    char *jpeg = NULL;
    int nLength = 0, nResult = 0;

    assert( strcasecmp(map->outputformat->driver,"PDF") == 0 );
    pdf = image->img.pdf->pdf;

/* -------------------------------------------------------------------- */
/*      create a temporary GD image and render in it.                   */
/* -------------------------------------------------------------------- */
/* --------------------------------------------------------------------- */
/*  Idea is to render the image into image_tmp using the ms GD api,      */
/*  use gd to convert it to a png. PDFlib can then place the png into the*/
/*  output pdf. Done as jpeg for now - change.                            */
/* --------------------------------------------------------------------- */
    format = msCreateDefaultOutputFormat( NULL, "GD/PC256" );
    if( format == NULL )
        return -1;

    image_tmp = msImageCreate( image->width, image->height, format,
                                      NULL, NULL );

    if( image_tmp == NULL )
      return -1;
  
    if (msDrawRasterLayerLow(map, layer, image_tmp) != -1)
    {
        /*kludge: this should really be a raw image or png. jpeg is not good*/
        /*but pdflib doesn't support in mem opening of png.*/
        jpeg = gdImageJpegPtr(image_tmp->img.gd, &nLength, 95);
        nResult = PDF_open_image(pdf, "jpeg", "memory",
                                jpeg, (long)nLength,
                                map->width, map->height,
                                3, 8, NULL);
        gdFree(jpeg);
    
        PDF_save(pdf); /* save the original coordinate system */
        PDF_scale(pdf, 1, -1); /* flip the coordinates, and therefore the image */
        PDF_place_image(pdf,nResult, 0, -(map->height), 1.0);
        PDF_restore(pdf); /* restore the original coordinate system */
 
        PDF_close_image(pdf,nResult);
        msFreeImage( image_tmp );

    }
    else
    {
        msSetError(MS_MISCERR,
                  "couldn't covert a raster layer to jpeg",
                  "drawjpeg()");
        msFreeImage( image_tmp );
        return -1;
    }
    
    return 0;
}


/************************************************************************/
/*  int msDrawVectorLayerAsRasterPDF                                    */
/*                                                                      */
/*  draw vectors to image and add it to the PDF                         */
/************************************************************************/
int msDrawVectorLayerAsRasterPDF(mapObj *map, layerObj *layer, imageObj*image)
{
    return 0;
}

/************************************************************************/
/*  void msTransformShapePDF                                            */
/*                                                                      */
/*  Transform geographic coordinates to output coordinates.             */
/*                                                                      */
/************************************************************************/
void msTransformShapePDF(shapeObj *shape, rectObj extent, double cellsize)
{
    int i,j;

    if(shape->numlines == 0) return;

    if(shape->type == MS_SHAPE_LINE || shape->type == MS_SHAPE_POLYGON)
    {
        for(i=0; i<shape->numlines; i++)
        {
            for(j=0; j < shape->line[i].numpoints; j++ )
            {
                shape->line[i].point[j].x =
                    (shape->line[i].point[j].x - extent.minx)/cellsize;
                shape->line[i].point[j].y =
                    (extent.maxy - shape->line[i].point[j].y)/cellsize;
            }
        }  
        return;
    }
}

/************************************************************************/
/*  void msSaveImagePDF                                                 */
/*                                                                      */
/*  writes the image's pdf out to disk or sends it to stdout             */
/************************************************************************/
int msSaveImagePDF(imageObj *image, char *filename)
{
    if (image && MS_DRIVER_PDF(image->format))
    {
        FILE *stream;
        long size;
        const char *pdfBuffer;
    
        /*finish the page and put the entire pdf into a buffer*/
        PDF_end_page(image->img.pdf->pdf);
        PDF_close(image->img.pdf->pdf);
        pdfBuffer = PDF_get_buffer(image->img.pdf->pdf, &size);
        if(filename != NULL && strlen(filename) > 0)
        {
            stream = fopen(filename, "wb");
            if(!stream)
            {
                msSetError(MS_IOERR, "(%s)", "msSaveImagePDF()", filename);
                return(MS_FAILURE);
            }
        }
        else
        { /* use stdout */
            #ifdef _WIN32
            /* Change stdout mode to binary on win32 platforms*/
          if(0)//_setmode( _fileno(stdout), _O_BINARY) == -1)
            {
                msSetError(MS_IOERR, "Unable to change stdout to binary mode.", "msSaveImagePDF()");
                return(MS_FAILURE);
            }
            #endif
            stream = stdout;
        }
  
      /*-----------------------------------------------
      /send the active buffer to disk
      /-----------------------------------------------*/
  
      fwrite(pdfBuffer, sizeof(char), size, stream);
      if(filename != NULL && strlen(filename) > 0)
         fclose(stream);
      //free(pdfBuffer);

      return(MS_SUCCESS);
    }
    msSetError(MS_MISCERR, "Incorrect driver passed as pdf: %s.",
                     "msSaveImagePDF()", image->format );
    return MS_FAILURE;
}

/************************************************************************/
/*  void msFreeImagePDF                                                 */
/*                                                                      */
/*  Free PDF object structure                                           */
/************************************************************************/
void msFreeImagePDF(imageObj *image)
{
    if (image && MS_DRIVER_PDF(image->format) )
    {
        PDF_delete(image->img.pdf->pdf);
        image->img.pdf->pdf = NULL;
    }
}

/************************************************************************/
/*  int msDrawTextPDF                                                   */
/*                                                                      */
/*  creates a text element in the pdf                                   */
/************************************************************************/
int msDrawTextPDF(imageObj *image, pointObj labelPnt, char *string,
                 labelObj *label, fontSetObj *fontset, double scalefactor)
{
    int x, y, x1, y1;
    int font = 0;
    int size;
    float phi = label->angle;
    colorObj  sColor;
    char *wrappedString;
    char *fontKey;
    PDF *pdf;
/* -------------------------------------------------------------------- */
/*      if not PDF, return.                                             */
/* -------------------------------------------------------------------- */
    if (image == NULL || !MS_DRIVER_PDF(image->format))
        return 0;
    
/* -------------------------------------------------------------------- */
/*      validate arguments.                                             */
/* -------------------------------------------------------------------- */
    if(!string || strlen(string) == 0 || !label || !fontset)
        return(0); /* not an error, just don't want to do anything */

    if(strlen(string) == 0)
        return(0); /* not an error, just don't want to do anything */

    x = MS_NINT(labelPnt.x);
    y = MS_NINT(labelPnt.y);

    size = label->size*scalefactor;

    if(!fontset)
    {
        msSetError(MS_TTFERR, "No fontset defined.", "msDrawTextPDF()");
        return(-1);
    }

    if(!label->font)
    {
        msSetError(MS_TTFERR, "No font defined.", "msDrawTextPDF()");
        return(-1);
    }

    font = msLookupHashTable(fontset->fonts, label->font);

    if(!font)
    {
        msSetError(MS_TTFERR, "Requested font (%s) not found.", "msDrawTextPDF()",
                   label->font);
        return(-1);
    }

    pdf = image->img.pdf->pdf;

/* -------------------------------------------------------------------- */
/* Do color initialization stuff                                        */
/* -------------------------------------------------------------------- */
    sColor.red = 0;
    sColor.green = 0;
    sColor.blue = 0;

    if (MS_VALID_COLOR(label->color))
    {
        sColor.red = label->color.red;
        sColor.green = label->color.green;
        sColor.blue = label->color.blue;
    }
    else if (MS_VALID_COLOR(label->outlinecolor))
    {
        sColor.red = label->outlinecolor.red;
        sColor.green = label->outlinecolor.green;
        sColor.blue = label->outlinecolor.blue;
    }
    else if (MS_VALID_COLOR(label->shadowcolor))
    {
        sColor.red = label->shadowcolor.red;
        sColor.green = label->shadowcolor.green;
        sColor.blue = label->shadowcolor.blue;
    }
    else
    {
        msSetError(MS_TTFERR, "Invalid color", "draw_textPDF()");
    return(-1);
    }

    if(!string)
        return(0); /* not an error, just don't want to do anything */

    if(strlen(string) == 0)
        return(0); /* not an error, just don't want to do anything */

    x = MS_NINT(labelPnt.x);
    y = MS_NINT(labelPnt.y);
    x1 = x; y1 = y;

    PDF_setrgbcolor_stroke(pdf,(float)sColor.red/255,
                               (float)sColor.green/255,
                               (float)sColor.blue/255);
    PDF_setrgbcolor_fill(pdf,(float)sColor.red/255,
                             (float)sColor.green/255,
                             (float)sColor.blue/255);
    PDF_setlinewidth(pdf,.3);

/*set up font handling*/
    fontKey = label->font;

    font = PDF_findfont(pdf, fontKey, "winansi",1);
    PDF_setfont(pdf,font,label->sizescaled+2);

    if (phi!=0){
        /*PDF_save(pdf);*/
        PDF_translate(pdf, x, y);
        PDF_rotate(pdf, -phi);
        x = y = 0;
    }

    PDF_scale(pdf,1,-1);
    if ((wrappedString = strchr(string,'\r')) == NULL)
    {
        PDF_show_xy(pdf,string,x,-y);
    }
    else{
        char *headPtr;
        headPtr = string;
            // break the string into pieces separated by \r\n
        while(wrappedString){
            char *piece;
            int length = wrappedString - headPtr;
            piece = malloc(length+1);
            memset(piece, 0, length+1);
            strncpy(piece, headPtr, length);

            if (headPtr == string){
                PDF_show_xy(pdf,piece,x,-y);
            }
            else {
                PDF_continue_text(pdf,piece);
            }
            free(piece);
            headPtr = wrappedString+2;
            wrappedString = strchr(headPtr,'\r');
        }
        PDF_continue_text(pdf,headPtr);
    }
    PDF_scale(pdf,1,-1);
    if (phi!=0){
        PDF_rotate(pdf, phi);
        PDF_translate(pdf, -x1, -y1);
//        PDF_restore(pdf);
    }
    PDF_setlinewidth(pdf,1);
    return 0;
}

/************************************************************************/
/*  void msDrawStartShapePDF                                            */
/*                                                                      */
/*  setup to start placing shapes in the pdf                            */
/************************************************************************/
void msDrawStartShapePDF(mapObj *map, layerObj *layer, imageObj *image,
                         shapeObj *shape)
{
    return;
}

/************************************************************************/
/*  void msImageStartLayerPDF                                           */
/*                                                                      */
/*  set up to start drawing a layer                                     */
/************************************************************************/
void msImageStartLayerPDF(mapObj *map, layerObj *layer, imageObj *image)
{
    return;
}

/************************************************************************/
/*  int msEmbedScalebarPDF                                              */
/*                                                                      */
/*  draw a scalebar into the pdf.                                       */
/************************************************************************/
int msEmbedScalebarPDF(mapObj *map, imageObj *image)
{
    /*TODO*/
    return(0);
}
#endif
