#include <assert.h>
#include "map.h"
#include "mapresample.h"
#include "mapthread.h"

extern int msyyparse();
extern int msyylex();
extern char *msyytext;

extern int msyyresult; // result of parsing, true/false
extern int msyystate;
extern char *msyystring;

#ifdef USE_EGIS
#include <errLog.h>
#include <imgLib.h>
#include <sys/time.h>
#endif

#ifdef USE_TIFF
#include <tiffio.h>
#include <tiff.h>
#endif

#ifdef USE_GDAL
#include "gdal.h"
#include "cpl_string.h"
#endif

#ifdef USE_EPPL
#include "epplib.h"
#endif

#ifdef USE_JPEG
#include "jpeglib.h"
#endif


#define MAXCOLORS 256
#define BUFLEN 1024
#define HDRLEN 8

#define	CVT(x) ((x) >> 8) /* converts to 8-bit color value */

#define NUMGRAYS 16

// FIX: need WBMP sig
unsigned char PNGsig[8] = {137, 80, 78, 71, 13, 10, 26, 10}; // 89 50 4E 47 0D 0A 1A 0A hex
unsigned char JPEGsig[3] = {255, 216, 255}; // FF D8 FF hex

#ifdef USE_EGIS
#define rasterDebug 0
struct timeval stTime, endTime;
double diffTime;
#endif

/*
** Function to evaluate a color (RGB+pen) against a class expression.
*/
int msGetClass(layerObj *layer, colorObj *color)
{
  int i;
  char *tmpstr1=NULL;
  char tmpstr2[12]; // holds either a single color index or something like 'rrr ggg bbb'
  
  if((layer->numclasses == 1) && !(layer->class[0].expression.string)) /* no need to do lookup */
    return(0);

  if(!color) return(-1);

  for(i=0; i<layer->numclasses; i++) {
    if (layer->class[i].expression.string == NULL) /* Empty expression - always matches */
      return(i);
    switch(layer->class[i].expression.type) {
    case(MS_STRING):
      sprintf(tmpstr2, "%d %d %d", color->red, color->green, color->blue);
      if(strcmp(layer->class[i].expression.string, tmpstr2) == 0) return(i); // matched
      sprintf(tmpstr2, "%d", color->pen);
      if(strcmp(layer->class[i].expression.string, tmpstr2) == 0) return(i); // matched
      break;
    case(MS_REGEX):
      if(!layer->class[i].expression.compiled) {
	if(regcomp(&(layer->class[i].expression.regex), layer->class[i].expression.string, REG_EXTENDED|REG_NOSUB) != 0) { // compile the expression 
	  msSetError(MS_REGEXERR, "Invalid regular expression.", "msGetClass()");
	  return(-1);
	}
	layer->class[i].expression.compiled = MS_TRUE;
      }

      sprintf(tmpstr2, "%d %d %d", color->red, color->green, color->blue);
      if(regexec(&(layer->class[i].expression.regex), tmpstr2, 0, NULL, 0) == 0) return(i); // got a match
      sprintf(tmpstr2, "%d", color->pen);
      if(regexec(&(layer->class[i].expression.regex), tmpstr2, 0, NULL, 0) == 0) return(i); // got a match
      break;
    case(MS_EXPRESSION):
      tmpstr1 = strdup(layer->class[i].expression.string);

      sprintf(tmpstr2, "%d", color->red);
      tmpstr1 = gsub(tmpstr1, "[red]", tmpstr2);
      sprintf(tmpstr2, "%d", color->green);
      tmpstr1 = gsub(tmpstr1, "[green]", tmpstr2);
      sprintf(tmpstr2, "%d", color->blue);
      tmpstr1 = gsub(tmpstr1, "[blue]", tmpstr2);

      sprintf(tmpstr2, "%d", color->pen);
      tmpstr1 = gsub(tmpstr1, "[pixel]", tmpstr2);

      msyystate = 4; msyystring = tmpstr1;
      if(msyyparse() != 0) return(-1); // error parsing the expression

      free(tmpstr1);

      if(msyyresult) return(i); // got a match	
    }
  }

  return(-1); /* not found */
}

/*
** Function to add a color to an existing color map.  It first looks for
** an exact match, then tries to add it to the end of the existing color map,
** and if all else fails it finds the closest color.
*/
int msAddColorGD(mapObj *map, gdImagePtr img, int r, int g, int b)
{
  int c; 
  int ct = -1;
  int op = -1;
  long rd, gd, bd, dist;
  long mindist = 3*255*255;  /* init to max poss dist */
  
  /*
  ** We want to avoid using a color that matches a transparent background
  ** color exactly.  If this is the case, we will permute the value slightly.
  ** When perterbing greyscale images we try to keep them greyscale, otherwise
  ** we just perterb the red component.
  */
  if( map->outputformat && map->outputformat->transparent 
      && map->imagecolor.red == r 
      && map->imagecolor.green == g 
      && map->imagecolor.blue == b )
  {
      if( r == 0 && g == 0 && b == 0 )
      {
          r = g = b = 1;
      }
      else if( r == g && r == b )
      {
          r = g = b = r-1;
      }
      else if( r == 0 )
      {
          r = 1;
      }
      else
      {
          r = r-1;
      }
  }

  /* 
  ** Find the nearest color in the color table.  If we get an exact match
  ** return it right away.
  */
  for (c = 0; c < img->colorsTotal; c++) {

    if (img->open[c]) {
      op = c; /* Save open slot */
      continue; /* Color not in use */
    }
    
    /* don't try to use the transparent color */
    if (map->outputformat && map->outputformat->transparent 
        && img->red  [c] == map->imagecolor.red
        && img->green[c] == map->imagecolor.green
        && img->blue [c] == map->imagecolor.blue )
        continue;

    rd = (long)(img->red  [c] - r);
    gd = (long)(img->green[c] - g);
    bd = (long)(img->blue [c] - b);
/* -------------------------------------------------------------------- */
/*      special case for grey colors (r=g=b). we will try to find       */
/*      either the nearest grey or a color that is almost grey.         */
/* -------------------------------------------------------------------- */
    if (r == g && r == b)
    {
        if (img->red == img->green && img->red ==  img->blue)
          dist = rd;
        else
          dist = rd * rd + gd * gd + bd * bd;
    }
    else
      dist = rd * rd + gd * gd + bd * bd;
    if (dist < mindist) {
      if (dist == 0) {
	return c; /* Return exact match color */
      }
      mindist = dist;
      ct = c;
    }
  }       

  /* no exact match.  We now know closest, but first try to allocate exact */
  if (op == -1) {
    op = img->colorsTotal;
    if (op == gdMaxColors) { /* No room for more colors */
      return ct; /* Return closest available color */
    }
    img->colorsTotal++;
  }

  img->red  [op] = r;
  img->green[op] = g;
  img->blue [op] = b;
  img->open [op] = 0;

  return op; /* Return newly allocated color */  
}

/*
** Function to read georeferencing information for an image from an
** ESRI world file.
*/
static int readWorldFile(char *filename, double *ulx, double *uly, double *cx, double *cy) {
  FILE *stream;
  char *wld_filename;
  int i=0;
  char buffer[BUFLEN];

  wld_filename = strdup(filename);

  strcpy(strrchr(wld_filename, '.'), ".wld");
  stream = fopen(wld_filename, "r");
  if(!stream) {
    strcpy(strrchr(wld_filename, '.'), ".tfw");
    stream = fopen(wld_filename, "r");
    if(!stream) {
      strcpy(strrchr(wld_filename, '.'), ".jgw");
      stream = fopen(wld_filename, "r");
      if(!stream) {
        strcpy(strrchr(wld_filename, '.'), ".gfw");
        stream = fopen(wld_filename, "r");
        if(!stream) {	
	  msSetError(MS_IOERR, "Unable to open world file for reading.", "readWorldFile()");
	  free(wld_filename);
	  return(-1);
        }
      }
    }
  }

  while(fgets(buffer, BUFLEN, stream)) {    
    switch(i) {
    case 0:
      *cx = atof(buffer);
      break;
    case 3:
      *cy = MS_ABS(atof(buffer));
      break;
    case 4:
      *ulx = atof(buffer);
      break;
    case 5:
      *uly = atof(buffer);
      break;
    default:
      break;
    }

    i++;
  }
    
  fclose(stream);
  free(wld_filename);

  return(0);
}

/* read georeferencing info from geoTIFF header, if it exists */
#ifdef USE_TIFF 
static int readGEOTiff(TIFF *tif, double *ulx, double *uly, double *cx, double *cy)
{
  short entries;
  int i,fpos,swap,tiepos,cellpos;
  double tie[6],cell[6];
  TIFFDirEntry tdir;
  FILE *f;
  
  swap=TIFFIsByteSwapped(tif);
  fpos=TIFFCurrentDirOffset(tif);
  f=fopen((char*)TIFFFileName(tif),"rb");
  if (f==NULL) return(-1);
  fseek(f,fpos,0);
  fread(&entries,2,1,f);
  if (swap) TIFFSwabShort(&entries);
  tiepos=0; cellpos=0;
  for (i=0; i<entries; i++) {
    fread(&tdir,sizeof(tdir),1,f);
    if (swap) TIFFSwabShort(&tdir.tdir_tag);
    if (tdir.tdir_tag==0x8482) {  /* geoTIFF tie point */
      tiepos=tdir.tdir_offset;
      if (swap) TIFFSwabLong((long *)&tiepos);
      }
    if (tdir.tdir_tag==0x830e) {  /* geoTIFF cell size */
      cellpos=tdir.tdir_offset;
      if (swap) TIFFSwabLong((long *)&cellpos);
      }
    }
  if (tiepos==0 || cellpos==0) {
    fclose(f);
    return(-1);    
  }
  fseek(f,tiepos,0);
  fread(tie,sizeof(double),6,f);
  if (swap) TIFFSwabArrayOfDouble(tie,6);
  fseek(f,cellpos,0);
  fread(cell,sizeof(double),3,f);
  if (swap) TIFFSwabArrayOfDouble(cell,3);
  *cx=fabs(cell[0]);  *cy=fabs(cell[1]);
  *ulx=tie[3]-(tie[0]*cell[0]);
  *uly=tie[4]+(tie[1]*cell[1]);
  fclose(f);
  return(0);
}
#endif  
  
static int drawTIFF(mapObj *map, layerObj *layer, gdImagePtr img, char *filename) 
{
#ifdef USE_TIFF
  int i,j; /* loop counters */

  double x,y;
  TIFF *tif=NULL; 
  unsigned char *buf; 
  long w, h;
  short type, nbits;
  unsigned short compression;
  unsigned short *red, *green, *blue;
  int cmap[MAXCOLORS];

  colorObj pixel;

  double startx, starty; /* this is where we start out reading */
  int st,strip;  /* current strip */
  int xi,yi,startj,endj,boffset,vv;

  double ulx, uly; /* upper left-hand coordinates */
  double skipx,skipy; /* skip factors (x and y) */  
  double cx,cy; /* cell sizes (x and y) */
  long rowsPerStrip;    

  char szPath[MS_MAXPATHLEN];

  for(i=0; i<MAXCOLORS; i++) cmap[i] = -1; // initialize the colormap to all transparent

  TIFFSetWarningHandler(NULL); // can these be directed to the mapserver error functions?
  TIFFSetErrorHandler(NULL);

  tif = TIFFOpen(msBuildPath3(szPath, map->mappath, map->shapepath, filename), "rb");
  if(!tif) {
    msSetError(MS_IMGERR, "Error loading TIFF image.", "drawTIFF()");
    return(-1);
  }
  
  if(readGEOTiff(tif, &ulx, &uly, &cx, &cy ) != 0) {
    if(readWorldFile(msBuildPath3(szPath,map->mappath,map->shapepath,filename),
                     &ulx, &uly, &cx, &cy) != 0) {
      TIFFClose(tif);
      return(-1);
    }   
  }

  skipx = map->cellsize/cx;
  skipy = map->cellsize/cy;
  startx = (map->extent.minx - ulx)/cx;
  starty = (uly - map->extent.maxy)/cy;

  TIFFGetField(tif, TIFFTAG_IMAGEWIDTH, &w);
  TIFFGetField(tif, TIFFTAG_IMAGELENGTH, &h);

  TIFFGetField(tif, TIFFTAG_BITSPERSAMPLE, &nbits);
  if(nbits != 8 && nbits != 4 && nbits != 1) {
    msSetError(MS_IMGERR, "Only 1, 4, and 8-bit images are supported.", "drawTIFF()");
    TIFFClose(tif);
    return(-1); 
  }

  TIFFGetField(tif, TIFFTAG_ROWSPERSTRIP, &rowsPerStrip);
  TIFFGetField(tif, TIFFTAG_COMPRESSION, &compression);

  TIFFGetField(tif, TIFFTAG_PHOTOMETRIC, &type); /* check image type */
  switch(type) {  
  case(PHOTOMETRIC_PALETTE):    
    TIFFGetField(tif, TIFFTAG_COLORMAP, &red, &green, &blue);
    if(layer->numclasses > 0) {
      int c;

      for(i=0; i<MAXCOLORS; i++) {

	pixel.red = CVT(red[i]);
	pixel.green = CVT(green[i]);
	pixel.blue = CVT(blue[i]);
	pixel.pen = i;

	if(!MS_COMPARE_COLORS(pixel, layer->offsite)) {	  
	  c = msGetClass(layer, &pixel);
	  
	  if(c == -1) /* doesn't belong to any class, so handle like offsite */
	    cmap[i] = -1;
	  else {
	    if(MS_VALID_COLOR(layer->class[c].styles[0].color)) 
	      cmap[i] = msAddColorGD(map,img, layer->class[c].styles[0].color.red, layer->class[c].styles[0].color.green, layer->class[c].styles[0].color.blue); // use class color
	    else if(MS_TRANSPARENT_COLOR(layer->class[c].styles[0].color)) 
	      cmap[i] = -1; // make transparent
	    else
              cmap[i] = msAddColorGD(map,img, pixel.red, pixel.green, pixel.blue); // use raster color
	  }
	} 
      }
    } else {
      for(i=0; i<MAXCOLORS; i++) {

	pixel.red = CVT(red[i]);
	pixel.green = CVT(green[i]);
	pixel.blue = CVT(blue[i]);
	pixel.pen = i;

	if(!MS_COMPARE_COLORS(pixel, layer->offsite))
	  cmap[i] = msAddColorGD(map,img, pixel.red, pixel.green, pixel.blue); // use raster color        
      }
    }
    break;
  case PHOTOMETRIC_MINISBLACK: /* classes are NOT honored for non-colormapped data */
    if (nbits==1) {
      for (i=0; i<2; i++) {
	pixel.red = pixel.green = pixel.blue = pixel.pen = i; // offsite would be specified as 0 or 1

	if(!MS_COMPARE_COLORS(pixel, layer->offsite))
          cmap[i]=msAddColorGD(map,img, i*255,i*255,i*255); // use raster color, stretched to use entire grayscale range
      }      
    } else { 
      if (nbits==4) {	
	for (i=0; i<16; i++) {
	  pixel.red = pixel.green = pixel.blue = pixel.pen = i; // offsite would be specified in range 0 to 15

	  if(!MS_COMPARE_COLORS(pixel, layer->offsite))
	    cmap[i] = msAddColorGD(map,img, i*17, i*17, i*17); // use raster color, stretched to use entire grayscale range	  
	}
      } else { /* 8-bit */
	for (i=0; i<256; i++) {
	  pixel.red = pixel.green = pixel.blue = pixel.pen = i; // offsite would be specified in range 0 to 255

	  if(!MS_COMPARE_COLORS(pixel, layer->offsite))	    
	    cmap[i] = msAddColorGD(map,img, (i>>4)*17, (i>>4)*17, (i>>4)*17); // use raster color
	}
      }
    }
    break;
  case PHOTOMETRIC_MINISWHITE: /* classes are NOT honored for non-colormapped data */
    if (nbits==1) {
      for (i=0; i<2; i++) {
	pixel.red = pixel.green = pixel.blue = pixel.pen = i; // offsite would be specified as 0 or 1

	if(!MS_COMPARE_COLORS(pixel, layer->offsite))
	  cmap[i]=msAddColorGD(map,img, i*255,i*255,i*255); // use raster color, stretched to use entire grayscale range
      }      
    }
    else {
      msSetError(MS_IMGERR,"Can't do inverted grayscale images","drawTIFF()");
      TIFFClose(tif);
      return(-1);
    }
    break;
  default:
    msSetError(MS_IMGERR, "Only colormapped and grayscale images are supported.", "drawTIFF()");
    TIFFClose(tif);
    return(-1);
  }

  buf = (unsigned char *)_TIFFmalloc(TIFFStripSize(tif)); /* allocate strip buffer */
  
  /* 
  ** some set-up;  the startx calculation is problematical analytically so we
  ** find it iteratively 
  */
  x=startx;
  for (j=0; j<img->sx && MS_NINT(x)<0; j++) x+=skipx;
  startx=x; startj=j;
  for (j=startj; j<img->sx && MS_NINT(x)<w; j++) x+=skipx;
  endj=j;
  y=starty;
  strip=-1;
  for(i=0; i<img->sy; i++) { /* for each row */
    yi=MS_NINT(y);
    if((yi >= 0) && (yi < h)) {
      st=TIFFComputeStrip(tif,yi,0);
      if (st!=strip) {
        TIFFReadEncodedStrip(tif, st, buf, TIFFStripSize(tif));
        strip=st;
      }  
      x = startx;

      switch (nbits) {
      case 8:
        boffset=(yi % rowsPerStrip) * w;
        for(j=startj; j<endj; j++) {    
	  xi=MS_NINT(x);
	  vv=buf[xi+boffset];  
	  
	  if (cmap[vv] != -1) 
	    img->pixels[i][j] = cmap[vv];
	  
	  x+=skipx;
        }
        break;
      case 4:
        boffset=(yi % rowsPerStrip) * ((w+1) >> 1);
        for(j=startj; j<endj; j++) {
          xi=MS_NINT(x);
          vv=(buf[(xi >> 1) + boffset] >> (4*((yi+1) & 1))) & 15;

	  if (cmap[vv] != -1) 
	    img->pixels[i][j] = cmap[vv];

	  x+=skipx;
	}  
        break;  
      case 1:
        boffset=(yi % rowsPerStrip) * ((w+7) >> 3);
        for(j=startj; j<endj; j++) {
          xi=MS_NINT(x);    
          vv=(buf[(xi >> 3) + boffset] >> (7-(xi & 7))) & 1;         

	  if (cmap[vv] != -1) 
	    img->pixels[i][j] = cmap[vv];

	  x+=skipx;
	}  
        break; 
      }   
    }
    y+=skipy;  
  }
  _TIFFfree(buf);

  TIFFClose(tif);
  return(0);
#else
   msSetError(MS_IMGERR, "TIFF support is not available.", "drawTIFF()");
   return(-1);
#endif
} 

static int drawPNG(mapObj *map, layerObj *layer, gdImagePtr img, char *filename) 
{
#ifdef USE_GD_PNG
  int i,j; /* loop counters */
  double x,y;
  int cmap[MAXCOLORS];
  double w, h;

  FILE *pngStream;
  gdImagePtr png;

  int vv;

  colorObj pixel;

  double startx, starty; /* this is where we start out reading */

  double ulx, uly; /* upper left-hand coordinates */
  double skipx,skipy; /* skip factors (x and y) */  
  double cx,cy; /* cell sizes (x and y) */
  char szPath[MS_MAXPATHLEN];

  for(i=0; i<MAXCOLORS; i++) cmap[i] = -1; // initialize the colormap to all transparent

  pngStream = fopen(msBuildPath3(szPath, map->mappath, map->shapepath, filename), "rb");
  if(!pngStream) {
    msSetError(MS_IOERR, "Error open image file.", "drawPNG()");
    return(-1);
  }

  png = gdImageCreateFromPng(pngStream);
  fclose(pngStream);

  if(!png) {
    msSetError(MS_IMGERR, "Error loading PNG file.", "drawPNG()");
    return(-1);
  }

  w = gdImageSX(png) - .5; /* to avoid rounding problems */
  h = gdImageSY(png) - .5;

  if(layer->transform) {
    if(readWorldFile(msBuildPath3(szPath, map->mappath,map->shapepath,filename), 
                     &ulx, &uly, &cx, &cy) != 0)
      return(-1);

    skipx = map->cellsize/cx;
    skipy = map->cellsize/cy;
    startx = (map->extent.minx - ulx)/cx;
    starty = (uly - map->extent.maxy)/cy;
  } else {
    skipx = skipy = 1;
    startx = starty = 0;    
  }

  if(layer->numclasses > 0) {
    int c;

    for(i=0; i<gdImageColorsTotal(png); i++) {

      pixel.red = gdImageRed(png,i);
      pixel.green = gdImageGreen(png,i);
      pixel.blue = gdImageBlue(png,i);
      pixel.pen = i; 

      if(!MS_COMPARE_COLORS(pixel, layer->offsite) && i != gdImageGetTransparent(png)) {	
	c = msGetClass(layer, &pixel);

	if(c == -1) /* doesn't belong to any class, so handle like offsite */
	  cmap[i] = -1;
	else {
          if(MS_VALID_COLOR(layer->class[c].styles[0].color)) 
	    cmap[i] = msAddColorGD(map,img, layer->class[c].styles[0].color.red, layer->class[c].styles[0].color.green, layer->class[c].styles[0].color.blue); // use class color
	  else if(MS_TRANSPARENT_COLOR(layer->class[c].styles[0].color)) 
	    cmap[i] = -1; // make transparent
	  else
            cmap[i] = msAddColorGD(map,img, pixel.red, pixel.green, pixel.blue); // use raster color	  
	}
      }
    }
  } else {
    for(i=0; i<gdImageColorsTotal(png); i++) {

      pixel.red = gdImageRed(png,i);
      pixel.green = gdImageGreen(png,i);
      pixel.blue = gdImageBlue(png,i);
      pixel.pen = i;

      if(!MS_COMPARE_COLORS(pixel, layer->offsite) && i != gdImageGetTransparent(png)) 
	cmap[i] = msAddColorGD(map,img, pixel.red, pixel.green, pixel.blue);
    }
  }

  y=starty;
  for(i=0; i<img->sy; i++) { /* for each row */
    if((y >= -0.5) && (y < h)) {
      x = startx;
      for(j=0; j<img->sx; j++) {
	if((x >= -0.5) && (x < w)) {
	  vv = png->pixels[(y == -0.5)?0:MS_NINT(y)][(x == -0.5)?0:MS_NINT(x)];	  
	  if(cmap[vv] != -1)
	    img->pixels[i][j] = cmap[vv];
	}
	x+=skipx;
      }
    }
    y+=skipy;  
  }

  gdImageDestroy(png);
  return(0);
#else
  msSetError(MS_IMGERR, "PNG support is not available.", "drawPNG()");
  return(-1);
#endif
}

static int drawGIF(mapObj *map, layerObj *layer, gdImagePtr img, char *filename) 
{
#ifdef USE_GD_GIF
  int i,j; /* loop counters */
  double x,y;
  int cmap[MAXCOLORS];
  double w, h;

  FILE *gifStream;
  gdImagePtr gif;

  int vv;
 
  colorObj pixel;

  double startx, starty; /* this is where we start out reading */

  double ulx, uly; /* upper left-hand coordinates */
  double skipx,skipy; /* skip factors (x and y) */  
  double cx,cy; /* cell sizes (x and y) */
  char szPath[MS_MAXPATHLEN];

  for(i=0; i<MAXCOLORS; i++) cmap[i] = -1; // initialize the colormap to all transparent

  gifStream = fopen(msBuildPath3(szPath, map->mappath, map->shapepath, filename), "rb");
  if(!gifStream) {
    msSetError(MS_IOERR, "Error open image file.", "drawGIF()");
    return(-1);
  }

  gif = gdImageCreateFromGif(gifStream);
  fclose(gifStream);

  if(!gif) {
    msSetError(MS_IMGERR, "Error loading GIF file.", "drawGIF()");
    return(-1);
  }

  w = gdImageSX(gif) - .5; /* to avoid rounding problems */
  h = gdImageSY(gif) - .5;

  if(layer->transform) {
    if(readWorldFile(msBuildPath3(szPath,map->mappath,map->shapepath,filename),
                     &ulx, &uly, &cx, &cy) != 0)
      return(-1);

    skipx = map->cellsize/cx;
    skipy = map->cellsize/cy;
    startx = (map->extent.minx - ulx)/cx;
    starty = (uly - map->extent.maxy)/cy;
  } else {
    skipx = skipy = 1;
    startx = starty = 0;    
  }

  if(layer->numclasses > 0) {
    int c;

    for(i=0; i<gdImageColorsTotal(gif); i++) {

      pixel.red = gdImageRed(gif,i);
      pixel.green = gdImageGreen(gif,i);
      pixel.blue = gdImageBlue(gif,i);	
      pixel.pen = i;

      if(!MS_COMPARE_COLORS(pixel, layer->offsite) && i != gdImageGetTransparent(gif)) {	
	c = msGetClass(layer, &pixel);

        if(c == -1) /* doesn't belong to any class, so handle like offsite */
	  cmap[i] = -1;
	else {
          if(MS_VALID_COLOR(layer->class[c].styles[0].color)) 
	    cmap[i] = msAddColorGD(map,img, layer->class[c].styles[0].color.red, layer->class[c].styles[0].color.green, layer->class[c].styles[0].color.blue); // use class color
	  else if(MS_TRANSPARENT_COLOR(layer->class[c].styles[0].color)) 
	    cmap[i] = -1; // make transparent
	  else
            cmap[i] = msAddColorGD(map,img, pixel.red, pixel.green, pixel.blue); // use raster color	  
	}	
      }
    }
  } else {
    for(i=0; i<gdImageColorsTotal(gif); i++) {

      pixel.red = gdImageRed(gif,i);
      pixel.green = gdImageGreen(gif,i);
      pixel.blue = gdImageBlue(gif,i);
      pixel.pen = i;

      if(!MS_COMPARE_COLORS(pixel, layer->offsite) && i != gdImageGetTransparent(gif)) 
	cmap[i] = msAddColorGD(map,img, pixel.red, pixel.green, pixel.blue);      
    }    
  }

  y=starty;
  for(i=0; i<img->sy; i++) { /* for each row */
    if((y >= -0.5) && (y < h)) {
      x = startx;
      for(j=0; j<img->sx; j++) {
	if((x >= -0.5) && (x < w)) {
	  vv = gif->pixels[(y == -0.5)?0:MS_NINT(y)][(x == -0.5)?0:MS_NINT(x)];	  
	  if(cmap[vv] != -1)
	    img->pixels[i][j] = cmap[vv];
	}
	x+=skipx;
      }
    }
    y+=skipy;  
  }

  gdImageDestroy(gif);
  return(0);
#else
  msSetError(MS_IMGERR, "GIF support is not available.", "drawGIF()");
  return(-1);
#endif
}


static int drawJPEG(mapObj *map, layerObj *layer, gdImagePtr img, char *filename) 
{
#ifdef USE_JPEG
  int i,j,k; /* loop counters */  
  int cmap[MAXCOLORS];
  double w, h;

  unsigned char vv;
  JSAMPARRAY buffer;

  double startx, starty; /* this is where we start out reading */
  double skipx,skipy; /* skip factors (x and y) */ 
  double x,y;

  double ulx, uly; /* upper left-hand coordinates */  
  double cx,cy; /* cell sizes (x and y) */

  colorObj pixel;

  FILE *jpegStream;

  struct jpeg_decompress_struct cinfo;
  struct jpeg_error_mgr jerr;

  char szPath[MS_MAXPATHLEN];

  cinfo.err = jpeg_std_error(&jerr);
  jpeg_create_decompress(&cinfo);

  jpegStream = fopen(msBuildPath3(szPath, map->mappath, map->shapepath, filename), "rb");
  if(!jpegStream) {
    msSetError(MS_IOERR, "Error open image file.", "drawJPEG()");
    return(-1);
  }
  jpeg_stdio_src(&cinfo, jpegStream);

  jpeg_read_header(&cinfo, TRUE);

  if(cinfo.jpeg_color_space != JCS_GRAYSCALE) {
    jpeg_destroy_decompress(&cinfo);
    fclose(jpegStream);
    msSetError(MS_IOERR, "Only grayscale JPEG images are supported.", "drawJPEG()");
    return(-1);
  }

  // set up the color map
  for (i=0; i<MAXCOLORS; i++) {
    pixel.red = pixel.green = pixel.blue = pixel.pen = i;

    cmap[i] = -1; // initialize to transparent
    if(!MS_COMPARE_COLORS(pixel, layer->offsite))      
      cmap[i] = msAddColorGD(map,img, (i>>4)*17,(i>>4)*17,(i>>4)*17);
  }

  if(readWorldFile(msBuildPath3(szPath, map->mappath, map->shapepath,filename),
                   &ulx, &uly, &cx, &cy) != 0)
    return(-1);
  
  skipx = map->cellsize/cx;
  skipy = map->cellsize/cy;

  // muck with scaling
  if(MS_MIN(skipx, skipy) >= 8)
    cinfo.scale_denom = 8;
  else
    if(MS_MIN(skipx, skipy) >= 4)
      cinfo.scale_denom = 4;
    else
      if(MS_MIN(skipx, skipy) >= 2)
	cinfo.scale_denom = 2;

  skipx = skipx/cinfo.scale_denom;
  skipy = skipy/cinfo.scale_denom;
  startx = (map->extent.minx - ulx)/(cinfo.scale_denom*cx);
  starty = (uly - map->extent.maxy)/(cinfo.scale_denom*cy);

  // initialize the decompressor, this sets output sizes etc...
  jpeg_start_decompress(&cinfo);

  w = cinfo.output_width - .5; /* to avoid rounding problems */
  h = cinfo.output_height - .5;

  // one pixel high buffer as wide as the image, goes away when done with the image
  buffer = (*cinfo.mem->alloc_sarray) ((j_common_ptr) &cinfo, JPOOL_IMAGE, cinfo.output_width, 1);

  // skip any unneeded scanlines *yuck*
  for(i=0; i<starty-1; i++)
    jpeg_read_scanlines(&cinfo, buffer, 1);

  y=starty;

  for(i=0; i<img->sy; i++) { /* for each row */
    if((y > -0.5) && (y < cinfo.output_height)) {
      
      jpeg_read_scanlines(&cinfo, buffer, 1);
      
      x = startx;
      for(j=0; j<img->sx; j++) {
	if((x >= -0.5) && (x < cinfo.output_width)) {
	  vv = buffer[0][(x == -0.5)?0:MS_NINT(x)];
	  if(cmap[vv] != -1)
	    img->pixels[i][j] = cmap[vv];
	}
	x+=skipx;
	if(x>=cinfo.output_width) // next x is out of the image, so quit
	  break;
      }
    }
    
    y+=skipy;

    if(y>=cinfo.output_height) // next y is out of the image, so quit
      break;

    for(k=cinfo.output_scanline; k<y-1; k++)
      jpeg_read_scanlines(&cinfo, buffer, 1);
  } 

  jpeg_destroy((j_common_ptr) &cinfo);
  fclose(jpegStream);

  return(0);
#else
  msSetError(MS_IMGERR, "JPEG support is not available.", "drawJPEG()");
  return(-1);
#endif
}

typedef struct erdhead {
  char hdword[6];
  short pack,bands;
  char res1[6];
  long cols,rows,col1,row1;
  char res2[56];
  short maptyp,nclass;
  char res3[14];
  short utyp;
  float area,xl,yt,xcell,ycell;
} erdhead;

static int drawERD(mapObj *map, layerObj *layer, gdImagePtr img, char *filename) 
{
#ifdef USE_EPPL
  int i,j,rowsz,reverse;
  char trec[128],tname[128];
  unsigned char gc[256],rc[256],bc[256],*pb;
  int startj,endj,rr,yi,vv;
  double startx,starty,skipx,skipy,x,y;
  int cmap[MAXCOLORS];
  FILE *erd,*trl;
  erdhead hd;
  char szPath[MS_MAXPATHLEN];
  colorObj pixel;

  {union {long i;char c[4];} u; u.i=1; reverse=(u.c[0]==0);}

  for(i=0; i<MAXCOLORS; i++) cmap[i] = -1; // initialize the colormap to all transparent

  erd=fopen(msBuildPath3(szPath, map->mappath, map->shapepath, filename),"rb");
  if (erd==NULL) {  
    msSetError(MS_IMGERR, "Error loading ERDAS image.", "drawERD()");
    return(-1);
  }
  fread(&hd,128,1,erd);
  /* need byte swapper here */
  if (reverse) {
    swap2(&hd.pack,2);
    swap4(&hd.cols,4);
    swap2(&hd.maptyp,2);
    swap2(&hd.utyp,1);
    swap4((long *)&hd.area,5);
  }  
  if (!strncmp(hd.hdword,"HEADER",6)) {   /*old format,convert to new*/
    memcpy(hd.hdword,"HEAD74",6);
    hd.cols=(long)MS_NINT((float)hd.cols);
    hd.rows=(long)MS_NINT((float)hd.rows);
    hd.col1=(long)MS_NINT((float)hd.col1);
    hd.row1=(long)MS_NINT((float)hd.row1);
  }
  if (strncmp(hd.hdword,"HEAD74",6) || hd.pack > 1 || hd.bands!=1) {
    msSetError(MS_IMGERR,"Bad header or unsupported header options.","drawERD()");
    fclose(erd);
    return -1;
  }
  strcpy(tname,filename);
  strcpy(strrchr(tname,'.'),".trl");
  trl=fopen(msBuildPath(szPath, map->mappath, tname),"rb");
  if (trl!=NULL) {  /**** check for trailer file*/
    fread(trec,128,1,trl);
    if (!strncmp(trec,"TRAILER",7)) memcpy(trec,"TRAIL74",7);
    if (!strncmp(trec,"TRAIL74",7)) {
      fread(gc,256,1,trl);
      fread(rc,256,1,trl);
      fread(bc,256,1,trl);

      if(layer->numclasses > 0) {	
	int c;

	for(i=0; i<hd.nclass; i++) {

  	  pixel.red = rc[i];
	  pixel.green = gc[i];
	  pixel.blue = bc[i];
          pixel.pen = i;

	  if(!MS_COMPARE_COLORS(pixel, layer->offsite)) {	    
	    c = msGetClass(layer, &pixel);
	    
	    if(c == -1) /* doesn't belong to any class, so handle like offsite */
	      cmap[i] = -1;
	    else {
	      if(MS_VALID_COLOR(layer->class[c].styles[0].color)) 
	        cmap[i] = msAddColorGD(map,img, layer->class[c].styles[0].color.red, layer->class[c].styles[0].color.green, layer->class[c].styles[0].color.blue); // use class color
	      else if(MS_TRANSPARENT_COLOR(layer->class[c].styles[0].color)) 
	        cmap[i] = -1; // make transparent
	      else
                cmap[i] = msAddColorGD(map,img, pixel.red, pixel.green, pixel.blue); // use raster color
	    }
	  }
	}
      } else {
	for(i=0; i<hd.nclass; i++) {
	  pixel.red = rc[i];
  	  pixel.green = gc[i];
	  pixel.blue = bc[i];
	  pixel.pen = i;

	  if(!MS_COMPARE_COLORS(pixel, layer->offsite))	   
  	    cmap[i] = msAddColorGD(map,img, pixel.red, pixel.green, pixel.blue); // use raster color
	}
      }
    }
    fclose(trl);
  } else {
    for (i=0; i<hd.nclass; i++) {  /* no trailer file, make gray, classes are not honored */

      pixel.red = pixel.green = pixel.blue = pixel.pen = i;

      if(!MS_COMPARE_COLORS(pixel, layer->offsite)) {
        j=((i*16)/hd.nclass)*17; 
	cmap[i] = msAddColorGD(map,img, j, j, j); // use raster color, streched over the 256 color range
      }
    } 
  }

  skipx=map->cellsize/hd.xcell;
  skipy=map->cellsize/hd.ycell;
  startx=(map->extent.minx-hd.xl)/hd.xcell;
  starty=(hd.yt-map->extent.maxy)/hd.ycell;
  pb=(unsigned char *)malloc(hd.cols);
  x=startx;
  for (j=0; j<img->sx && MS_NINT(x)<0; j++) x+=skipx;
  startx=x; startj=j;
  for (j=startj; j<img->sx && MS_NINT(x)<hd.cols; j++) x+=skipx;
  endj=j;
  rr=-1;
  y=starty;  
  if (hd.pack==0) rowsz=hd.cols;
   else rowsz=(hd.cols+1)/2;
  for (i=0; i<img->sy; i++) {
    yi=MS_NINT(y);
    if (yi>=0 && yi<hd.rows) {
      if (yi!=rr) {
        fseek(erd,128+rr*rowsz,0);
        fread(pb,rowsz,1,erd);
        rr=yi;
      }  
      x=startx;
      for (j=startj; j<endj; j++) {
        if (hd.pack==0) vv=pb[(int)MS_NINT(x)];
        else {
          vv=(int)MS_NINT(x);
          if (vv & 1) vv=(pb[vv >> 1]) >> 4;
          else vv=(pb[vv >> 1]) & 15;
        }  
        
	if(cmap[vv] != -1)
	  img->pixels[i][j] = cmap[vv];

       x+=skipx;
      }
    }
    y+=skipy;
  }
  free(pb);
  fclose(erd);
  return 0;
#else
   msSetError(MS_IMGERR, "ERDAS support is not available.", "drawERD()");
   return(-1);
#endif
}
  
static int drawEPP(mapObj *map, layerObj *layer, gdImagePtr img, char *filename) 
{
#ifdef USE_EPPL
  int ncol,nrow,yi,rr,i,j,startj,endj,vv;
  double cx,cy,skipx,skipy,x,y,startx,starty;
  int cmap[MAXCOLORS];
  char szPath[MS_MAXPATHLEN];
  eppfile epp;
  TRGB color;
  clrfile clr;

  colorObj pixel;

  for(i=0; i<MAXCOLORS; i++) cmap[i] = -1; // initialize the colormap to all transparent

  strcpy(epp.filname,msBuildPath3(szPath, map->mappath, map->shapepath,
                                  filename));
  if (!eppreset(&epp)) return -1;
  
  ncol=epp.lc-epp.fc+1;
  nrow=epp.lr-epp.fr+1;
  cx=(epp.lcx-epp.fcx)/ncol;
  cy=(epp.fry-epp.lry)/nrow;
  skipx=map->cellsize/cx;
  skipy=map->cellsize/cy;
  startx=(map->extent.minx-epp.fcx)/cx;
  starty=(epp.fry-map->extent.maxy)/cy;
  
  if (epp.kind!=8) {
    msSetError(MS_IMGERR,"Only 8 bit EPPL files supported.","drawEPP()");
    eppclose(&epp);
    return -3;
  }
  
  /* set up colors here */
  strcpy(clr.filname,msBuildPath3(szPath, map->mappath, map->shapepath,
                                  filename));
  if (!clrreset(&clr)) { /* use gray from min to max if no color file, classes not honored for greyscale */
    for (i=epp.minval; i<=epp.maxval; i++) {

      pixel.red = pixel.green = pixel.blue = pixel.pen = i;

      if(!MS_COMPARE_COLORS(pixel, layer->offsite)) {
	j=(((i-epp.minval)*16) / (epp.maxval-epp.minval+1))*17; 
	cmap[i]=msAddColorGD(map,img,j,j,j);
      }
    }
  } else {
    if(layer->numclasses > 0) {
      int c;
      
      for (i=epp.minval; i<=epp.maxval; i++) {

	pixel.red = color.red;
	pixel.green = color.green;
	pixel.blue = color.blue;
	pixel.pen = i;

	if(!MS_COMPARE_COLORS(pixel, layer->offsite)) {	  
	  c = msGetClass(layer, &pixel);
	  
	  if(c == -1) 
	    cmap[i] = -1;
	  else {
	    if(MS_VALID_COLOR(layer->class[c].styles[0].color)) 
	      cmap[i] = msAddColorGD(map,img, layer->class[c].styles[0].color.red, layer->class[c].styles[0].color.green, layer->class[c].styles[0].color.blue); // use class color
	    else if(MS_TRANSPARENT_COLOR(layer->class[c].styles[0].color)) 
	      cmap[i] = -1; // make transparent
	    else {              
	      clrget(&clr,i,&color);
	      cmap[i] = msAddColorGD(map,img, color.red, color.green, color.blue); // use raster color
	    }
	  }
	}
      }
    } else {
      for (i=epp.minval; i<=epp.maxval; i++) {
	pixel.red = color.red;
	pixel.green = color.green;
	pixel.blue = color.blue;
	pixel.pen = i;

	if(!MS_COMPARE_COLORS(pixel, layer->offsite)) {
	  clrget(&clr,i,&color);
	  cmap[i] = msAddColorGD(map,img, color.red, color.green, color.blue);
	}
      }
    }
    clrclose(&clr);
  }
  
  /* loop setup */
  x=startx;
  for (j=0; j<img->sx && MS_NINT(x)<0; j++) x+=skipx;
  startx=x; startj=j;
  for (j=startj; j<img->sx && MS_NINT(x)<ncol; j++) x+=skipx;
  endj=j;
  rr=-1;
  y=starty;  
  for (i=0; i<img->sy; i++) {
    yi=MS_NINT(y);
    if (yi>=0 && yi<nrow) {
      if (yi>rr+1) if (!position(&epp,yi+epp.fr)) return -2;
      if (yi>rr) if (!get_row(&epp)) return -2;
      rr=yi;
      x=startx;
      for (j=startj; j<endj; j++) {
        vv=epp.rptr[(int)MS_NINT(x)+1];

#ifndef USE_GD_1_2
	if(cmap[vv] != -1) 
	  img->pixels[i][j] = cmap[vv];
#else
	if(cmap[vv] != -1)
	  img->pixels[j][i] = cmap[vv];
#endif

        x+=skipx;
      }
    }
    y+=skipy;
  }
  eppclose(&epp);
  return 0;
#else
  msSetError(MS_IMGERR, "EPPL7 support is not available.", "drawEPP()");
  return(-1);
#endif  
}

#ifdef USE_EGIS
static int drawGEN(mapObj *map, layerObj *layer, gdImagePtr img, char *filename) 
{
  	int i,j; 		/* loop counters */
  	double x,y;
  	int cmap[MAXCOLORS];
  	int w, h;

  	int vv;
  	double startx, starty; 	/* this is where we start out reading */

  	double ulx, uly; 	/* upper left-hand coordinates */
  	double skipx,skipy; 	/* skip factors (x and y) */  
  	double cx,cy; 		/* cell sizes (x and y) */

	char hName[256];
	stRawImg stImgInfo;
	char errLogMsg[80];
	int status;
	int length;
	int maxPixels;
	int bSize;
	int nBands = 1;
	int bNos[1];
	int tmp = 1;

	unsigned char *tImg;

	// Initialize image header parameters

	errLogMsg[0] = '\0';
  	sprintf(errLogMsg, "From GEN: %s\n", filename); 
	writeErrLog(errLogMsg);
	
	// It is assumed that filename extension is .img and .hdr for header
	// Remove .img from filename 

	length = strlen(filename);
	strncpy(hName, filename, length-4);
	hName[length-4] = '\0';

	errLogMsg[0] = '\0';
  	sprintf(errLogMsg, "From GEN: %s, %s\n", filename, hName); 
  	writeErrLog(errLogMsg);

	// Initialize timer just before opening the image
        gettimeofday(&stTime, 0);

        if ( (status = initImgInfo(hName, &stImgInfo) ) != 1 )
        {
		writeErrLog("In drawGEN - initImgInfo failed\n");
                return -1;
        }

  	// stImgInfo.Bands = 1; 
  	w = stImgInfo.Pixels; // = 1321; 
  	h = stImgInfo.Lines; // = 964;

	ulx = stImgInfo.ulx; // = 115400.0;
	uly = stImgInfo.uly; // = 5547400.0;

	cx = stImgInfo.pwidth; // = 1000.0;
	cy = stImgInfo.pheight; // = 1000.0; 

	if (rasterDebug)
	{
	errLogMsg[0] = '\0';
  	sprintf(errLogMsg, "From GEN: %f %f %f %f\n",  ulx, uly, cx, cy); 
  	writeErrLog(errLogMsg);
	}

  	skipx = map->cellsize/cx;
  	skipy = map->cellsize/cy;
  	startx = (map->extent.minx - ulx)/cx;
  	starty = (int) (uly - map->extent.maxy)/cy;

	if (rasterDebug)
	{
  	errLogMsg[0] = '\0';
  	sprintf(errLogMsg, "skipx %f, skipy %f, startx %d, starty %d, w%d h%d\n",  
			skipx, skipy, startx, starty, w, h); 
	writeErrLog(errLogMsg);
	}

	// Read image and fill in the img structure

	maxPixels = img->sx * (skipx +1);
	if (maxPixels >=  stImgInfo.Pixels) maxPixels = stImgInfo.Pixels; 

	bSize = w * skipx + 1; 
	if (bSize < maxPixels) bSize = maxPixels + 1;

	tImg = malloc( bSize * sizeof(char));
	if (tImg == NULL)
	{
  		errLogMsg[0] = '\0';
  		sprintf(errLogMsg, "Error allocating mem to hold a line\n");  
		writeErrLog(errLogMsg);
		return -1;
	}

	bNos[0] = 1;
  	y = starty;

	// Add code to do color mapping - For the time its b&w 

    	for(i = 0; i < 255; i++) 
	{
      		if(i != layer->offsite)
		{
			j = (i * 16) / 255 * 17;
			cmap[i] = msAddColorGD(map, img, j, j, j); 
		}
		else
			cmap[i] = -1;
	}

	if (tmp == 0)
	{
		writeErrLog("In drawGEN - not doing anything\n");
		return (0);
	}

	// for each row 
  	for(i = 0; i < img->sy; i++) 
	{ 
		/*
		errLogMsg[0] = '\0';
  		sprintf(errLogMsg, "Line %d - Y = %g\n",  i, y); 
  		writeErrLog(errLogMsg);
		*/

    	   if((y >= 0) && (y < h)) 
	   {
      		x = startx;

		// Read a line here

		/*
		if((x >= 0) && (x < w)) 
		{
		*/
			
		status = imgReadLine(&stImgInfo, (int)y, (int)x, 
					maxPixels, nBands, bNos, tImg); 

		/*
  			errLogMsg[0] = '\0';
  			sprintf(errLogMsg, "reading line %d pix %d mx %d\n",
					 (int)y, (int)x, maxPixels);  
			writeErrLog(errLogMsg);
		}
		*/

		if (status != 1)
		{

  			errLogMsg[0] = '\0';
  			sprintf(errLogMsg, "Err reading line %d pix %d mx %d\n",
					 (int)y, (int)x, maxPixels);  
			writeErrLog(errLogMsg);
			// return -1;
		}

      		for(j = 0; j < img->sx; j++) 
		{
			if((x >= 0) && (x < w)) 
			{
				vv = (int) tImg[(int) (j * skipx)];
	  			if(cmap[vv] != -1)
	    				img->pixels[j][i] =  cmap[vv]; 
			}
			x += skipx;
      		}

		/*
		errLogMsg[0] = '\0';
  		sprintf(errLogMsg, "j = %d - x = %g\n", j, x); 
  		writeErrLog(errLogMsg);
		*/
    	   }
           y+=skipy;  
  	}

	// Stop timer and get total time
        gettimeofday(&endTime, 0);

        diffTime = endTime.tv_sec - stTime.tv_sec;
        diffTime = diffTime + (endTime.tv_usec - stTime.tv_usec) / 1e6;
 
			errLogMsg[0] = '\0';
      	sprintf(errLogMsg, "\ndrawGen Took %f Secs for L %d, P %d\n", 
							diffTime, img->sy, maxPixels); 

  	writeErrLog(errLogMsg);

	errLogMsg[0] = '\0';
  	sprintf(errLogMsg, "Image is generated\n"); 
  	writeErrLog(errLogMsg);

	return (0);
}
#endif

int msDrawRasterLayerLow(mapObj *map, layerObj *layer, imageObj *image) {

  /*
  ** Check for various file types and act appropriately.
  */
  int status;
  FILE *f;  
  char dd[8];
  char *filename=NULL;

  int t;
  int tileitemindex=-1;
  shapefileObj tilefile;
  char tilename[MS_PATH_LENGTH];
  int numtiles=1; /* always at least one tile */
  int force_gdal;
  char szPath[MS_MAXPATHLEN];
  char cwd[MS_MAXPATHLEN];

  rectObj searchrect;
  gdImagePtr img;

#ifdef USE_EGIS
  char *ext; // OV -egis- temp variable
#endif

  if( layer->debug > 0 || map->debug > 1 )
      msDebug( "msDrawRasterLayerLow(%s): entering.\n", layer->name );

  if(!layer->data && !layer->tileindex)
  {
      msDebug( "msDrawRasterLayerLow(%s): "
               "layer data and tileindex NULL ... doing nothing.", 
               layer->name );
      return(0);
  }

  if((layer->status != MS_ON) && (layer->status != MS_DEFAULT))
  {
      if( layer->debug > 0 )
          msDebug( "msDrawRasterLayerLow(%s): "
                   "not status ON or DEFAULT, doing nothing.",
                   layer->name );
      return(0);
  }

  if(map->scale > 0) {
      if((layer->maxscale > 0) && (map->scale > layer->maxscale))
      {
          if( layer->debug > 0 )
              msDebug( "msDrawRasterLayerLow(%s): "
                       "skipping, map scale %.2g > MAXSCALE=%g\n",
                       layer->name, map->scale, layer->maxscale );
          return(0);
      }
      if((layer->minscale > 0) && (map->scale <= layer->minscale))
      {
          if( layer->debug > 0 )
              msDebug( "msDrawRasterLayerLow(%s): "
                       "skipping, map scale %.2g < MINSCALE=%g\n",
                       layer->name, map->scale, layer->minscale );
          return(0);
      }
  }

  force_gdal = MS_FALSE;
  if( MS_RENDERER_GD(image->format) )
      img = image->img.gd;
  else
  {
      img = NULL;
      force_gdal = MS_TRUE;
  }

  // Only GDAL supports 24bit GD output.
#if GD2_VERS > 1
  if( gdImageTrueColor( img ) )
  {
#ifndef USE_GDAL
      msSetError(MS_MISCERR, "Attempt to render raster layer to IMAGEMODE RGB or RGBA but\nwithout GDAL available.  24bit output requires GDAL.", "msDrawRasterLayer()" );
      return -1;
#else
      force_gdal = MS_TRUE;
#endif
  }
#endif /* def GD2_VERS */

  // Only GDAL support image warping.
  if(layer->transform && 
     msProjectionsDiffer(&(map->projection), &(layer->projection)))
  {
#ifndef USE_GDAL
      msSetError(MS_MISCERR, "Attempt to render raster layer to IMAGEMODE RGB or RGBA but\nwithout GDAL available.  24bit output requires GDAL.", "msDrawRasterLayer()" );
      return -1;
#else
      force_gdal = MS_TRUE;
#endif
  }

  // This force use of GDAL if available.  This is usually but not always a
  // good idea.  Remove this line for local builds if necessary.
#ifdef USE_GDAL 
  force_gdal = MS_TRUE;
#endif

  if(map->shapepath)
      msBuildPath(cwd, map->mappath, map->shapepath);
  else
      msBuildPath(cwd, map->mappath, "");

  if(layer->tileindex) { /* we have in index file */
    if(msSHPOpenFile(&tilefile, "rb", msBuildPath(szPath, cwd, map->shapepath), layer->tileindex) == -1) return(-1);    
    if((tileitemindex = msDBFGetItemIndex(tilefile.hDBF, layer->tileitem)) == -1) return(-1);
    searchrect = map->extent;
#ifdef USE_PROJ
    if((map->projection.numargs > 0) && (layer->projection.numargs > 0))
      msProjectRect(&map->projection, &layer->projection, &searchrect); // project the searchrect to source coords
#endif
    status = msSHPWhichShapes(&tilefile, searchrect);
    if(status != MS_SUCCESS) 
      numtiles = 0; // could be MS_DONE or MS_FAILURE
    else
      numtiles = tilefile.numshapes;
  }

  for(t=0;t<numtiles;t++) { /* for each tile, always at least 1 tile */

    if(layer->tileindex) {
      if(!msGetBit(tilefile.status,t)) continue; /* on to next tile */
      if(layer->data == NULL) /* assume whole filename is in attribute field */
	filename = (char*)msDBFReadStringAttribute(tilefile.hDBF, t, tileitemindex);
      else {  
	sprintf(tilename,"%s/%s", msDBFReadStringAttribute(tilefile.hDBF, t, tileitemindex) , layer->data);
	filename = tilename;
      }
    } else {
      filename = layer->data;
    }

    if(strlen(filename) == 0) continue;

    f = fopen(msBuildPath(szPath, cwd, filename),"rb");
    if (!f) {
      memset( dd, 0, 8 );
    }
    else
    {
        fread(dd,8,1,f); // read some bytes to try and identify the file
        fclose(f);
    }

    if ((memcmp(dd,"II*\0",4)==0 || memcmp(dd,"MM\0*",4)==0) && !force_gdal) {
        status = drawTIFF(map, layer, img, filename);
        if(status == -1) {
            return(-1);
        }
        continue;
    }

    if (memcmp(dd,"GIF8",4)==0 && !force_gdal ) {
        status = drawGIF(map, layer, img, filename);
        if(status == -1) {
            return(-1);
        }
        continue;
    }

    if (memcmp(dd,PNGsig,8)==0 && !force_gdal) {
        status = drawPNG(map, layer, img, filename);
        if(status == -1) {
            return(-1);
        }
        continue;
    }

    if (memcmp(dd,JPEGsig,3)==0 && !force_gdal) 
    {
        status = drawJPEG(map, layer, img, filename);
        if(status == -1) {
            return(-1);
        }
        continue;
    }

    if (memcmp(dd,"HEAD",4)==0) {
      if(layer->transform && msProjectionsDiffer(&(map->projection), &(layer->projection))) {
        msSetError(MS_MISCERR, "Raster reprojection supported only with the GDAL library, but it does not support Erdas 7.x files.", "msDrawRasterLayer( ERD )");
        return(-1);
      }
      status = drawERD(map, layer, img, filename);
      if(status == -1) {
	return(-1);
      }
      continue;
    }
    
#ifdef USE_EGIS
    // OV - egis- Call Generic format function here
    // Note : modify this to find elegent way of deciding its generic
    // May be put any flag?
    
    ext = strstr(filename, ".img");
    if (strcmp(ext, ".img") == 0)
      {
      if(layer->transform && msProjectionsDiffer(&(map->projection, &(layer->projection))) {
          msSetError(MS_MISCERR, "Raster reprojection supported only with the GDAL library.", "msDrawRasterLayer( EGIS )");
          return(-1);
        }
	status = drawGEN(map, layer, img, filename);
	
	//ext = NULL;
	return(status);
      }
#endif

#ifdef USE_GDAL
    {
        GDALDatasetH  hDS;

        msGDALInitialize();

        msAcquireLock( TLOCK_GDAL );
        hDS = GDALOpen( msTryBuildPath(szPath, cwd, filename), GA_ReadOnly );
        if( hDS != NULL )
        {
            double	adfGeoTransform[6];

            if (layer->projection.numargs > 0 && 
                EQUAL(layer->projection.args[0], "auto"))
            {
                const char *pszWKT;

                pszWKT = GDALGetProjectionRef( hDS );

                if( pszWKT != NULL && strlen(pszWKT) > 0 )
                {
                    if (msOGCWKT2ProjectionObj(pszWKT,
                                     &(layer->projection)) != MS_SUCCESS)
                    {
                        char	szLongMsg[MESSAGELENGTH*2];
                        errorObj *ms_error = msGetErrorObj();

                        sprintf( szLongMsg, 
                                 "%s\n"
                                 "PROJECTION AUTO cannot be used for this "
                                 "GDAL raster (`%s').",
                                 ms_error->message, filename);
                        szLongMsg[MESSAGELENGTH-1] = '\0';

                        msSetError(MS_OGRERR, "%s","msDrawRasterLayer()",
                                   szLongMsg);

                        msReleaseLock( TLOCK_GDAL );
                        return(MS_FAILURE);
                    }
                }
            }

            adfGeoTransform[0] = 0.0;
            adfGeoTransform[1] = 1.0;
            adfGeoTransform[2] = 0.0;
            adfGeoTransform[3] = 0.0;
            adfGeoTransform[4] = 0.0;
            adfGeoTransform[5] = 1.0;

            if (GDALGetGeoTransform( hDS, adfGeoTransform ) != CE_None)
                GDALReadWorldFile(msBuildPath(szPath, cwd, filename),
                                  "wld", adfGeoTransform);

            /* 
            ** We want to resample if the source image is rotated, or if
            ** the projections differ.  However, due to limitations in 
            ** msResampleGDALToMap() we can only resample rotated images
            ** if they also have fully defined projections.
            */
#ifdef USE_PROJ
            if( ((adfGeoTransform[2] != 0.0 || adfGeoTransform[4] != 0.0)
                 && layer->transform
                 && map->projection.proj != NULL 
                 && layer->projection.proj != NULL)
                || msProjectionsDiffer( &(map->projection), 
                                        &(layer->projection) ) )
            {
                status = msResampleGDALToMap( map, layer, image, hDS );
            }
            else
#endif
            {
                status = msDrawRasterLayerGDAL(map, layer, image, hDS );
            }

            if( status == -1 )
            {
                GDALClose( hDS );
                msReleaseLock( TLOCK_GDAL );
                return -1;
            }

            GDALClose( hDS );
            msReleaseLock( TLOCK_GDAL );
            continue;
        }
        else
        {
            msReleaseLock( TLOCK_GDAL );
        }
    }
#endif

    /* If GDAL doesn't recognise it, and it wasn't successfully opened 
    ** Generate an error.
    */
    if( !f ) {
      msSetError(MS_IOERR, "(%s)", "msDrawRaster()", filename);

#ifndef IGNORE_MISSING_DATA
      if( layer->debug || map->debug )
          msDebug( "Unable to open file %s for layer %s ... fatal error.\n", 
                   filename, layer->name );

      return(-1);
#else
      if( layer->debug || map->debug )
          msDebug( "Unable to open file %s for layer %s ... ignoring this missing data.\n", 
                   filename, layer->name );

      continue; // skip it, next tile
#endif
    }

    /* put others which may require checks here */  
    
    /* No easy check for EPPL so put here */      
    status=drawEPP(map, layer, img, filename);
    if(status != 0) {
      if (status == -2) msSetError(MS_IMGERR, "Error reading EPPL file; probably corrupt.", "msDrawEPP()");
      if (status == -1) msSetError(MS_IMGERR, "Unrecognized or unsupported image format", "msDrawRaster()");
      return(-1);
    }
    continue;
  } // next tile

  if(layer->tileindex) /* tiling clean-up */
    msSHPCloseFile(&tilefile);    

  return 0;
  
}

//TODO : this will msDrawReferenceMapGD
imageObj *msDrawReferenceMap(mapObj *map) {
  double cellsize;
  int c=-1, oc=-1;
  int x1,y1,x2,y2;
  char szPath[MS_MAXPATHLEN];

  imageObj   *image = NULL;
  gdImagePtr img=NULL;

  image = msImageLoadGD( msBuildPath(szPath, map->mappath, 
                                     map->reference.image) );
  if( image == NULL )
      return NULL;

  if (map->web.imagepath)
      image->imagepath = strdup(map->web.imagepath);
  if (map->web.imageurl)
      image->imageurl = strdup(map->web.imageurl);

  img = image->img.gd;
  
  // make sure the extent given in mapfile fits the image
  cellsize = msAdjustExtent(&(map->reference.extent), 
                            image->width, image->height);

  // allocate some colors
  if(map->reference.outlinecolor.red != -1 && map->reference.outlinecolor.green != -1 && map->reference.outlinecolor.blue != -1)
    oc = gdImageColorAllocate(img, map->reference.outlinecolor.red, map->reference.outlinecolor.green, map->reference.outlinecolor.blue);
  if(map->reference.color.red != -1 && map->reference.color.green != -1 && map->reference.color.blue != -1)
    c = gdImageColorAllocate(img, map->reference.color.red, map->reference.color.green, map->reference.color.blue); 

  // convert map extent to reference image coordinates
  x1 = MS_MAP2IMAGE_X(map->extent.minx,  map->reference.extent.minx, cellsize);
  x2 = MS_MAP2IMAGE_X(map->extent.maxx,  map->reference.extent.minx, cellsize);  
  y1 = MS_MAP2IMAGE_Y(map->extent.maxy,  map->reference.extent.maxy, cellsize);
  y2 = MS_MAP2IMAGE_Y(map->extent.miny,  map->reference.extent.maxy, cellsize);

  // if extent are smaller than minbox size
  // draw that extent on the reference image
  if( (abs(x2 - x1) > map->reference.minboxsize) || 
          (abs(y2 - y1) > map->reference.minboxsize) )
  {
      if( map->reference.maxboxsize == 0 || 
              ((abs(x2 - x1) < map->reference.maxboxsize) && 
                  (abs(y2 - y1) < map->reference.maxboxsize)) )
      {
          if(c != -1)
              gdImageFilledRectangle(img,x1,y1,x2,y2,c);
          if(oc != -1)
              gdImageRectangle(img,x1,y1,x2,y2,oc);
      }
  
  }
  else // else draw the marker symbol
  {
      if( map->reference.maxboxsize == 0 || 
              ((abs(x2 - x1) < map->reference.maxboxsize) && 
                  (abs(y2 - y1) < map->reference.maxboxsize)) )
      {
	  styleObj style;

          style.color = map->reference.color;
          style.outlinecolor = map->reference.outlinecolor;
          style.size = map->reference.markersize;

          //if the marker symbol is specify draw this symbol else draw a cross
          if(map->reference.marker != 0)
          {
              pointObj *point = NULL;

              point = malloc(sizeof(pointObj));
              point->x = (double)(x1 + x2)/2;
              point->y = (double)(y1 + y2)/2;

	      style.symbol = map->reference.marker;

              msDrawMarkerSymbol(&map->symbolset, image, point, &style, 1.0);
              free(point);
          }
          else if(map->reference.markername != NULL)
          {              
              pointObj *point = NULL;

              point = malloc(sizeof(pointObj));
              point->x = (double)(x1 + x2)/2;
              point->y = (double)(y1 + y2)/2;

	      style.symbol = msGetSymbolIndex(&map->symbolset,  map->reference.markername);

              msDrawMarkerSymbol(&map->symbolset, image, point, &style, 1.0);
              free(point);
          }
          else
          {
              int x21, y21;
              //determine the center point
              x21 = MS_NINT((x1 + x2)/2);
              y21 = MS_NINT((y1 + y2)/2);

              //get the color
              if(c == -1)
                  c = oc;

              //draw a cross
              if(c != -1)
              {
                  gdImageLine(img, x21-8, y21, x21-3, y21, c);
                  gdImageLine(img, x21, y21-8, x21, y21-3, c);
                  gdImageLine(img, x21, y21+3, x21, y21+8, c);
                  gdImageLine(img, x21+3, y21, x21+8, y21, c);
              }
          }
      }
  }

  return(image);
}
