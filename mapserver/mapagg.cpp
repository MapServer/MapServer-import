/******************************************************************************
 * $id: mapagg.cpp 7919 2008-09-22 21:24:18z sdlime $
 *
 * Project:  MapServer
 * Purpose:  AGG rendering and other AGG related functions.
 * Author:   Steve Lime and the MapServer team.
 *
 ******************************************************************************
 * Copyright (c) 1996-2007 Regents of the University of Minnesota.
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
 *****************************************************************************/

#ifdef USE_AGG

#include "mapserver.h"
#include "mapthread.h"


#ifdef _WIN32
#include <fcntl.h>
#include <io.h>
#endif

#include "agg_basics.h"
#include "agg_rendering_buffer.h"
#include "agg_rasterizer_scanline_aa.h"
#include "agg_rasterizer_outline_aa.h"
#include "agg_rasterizer_outline.h"

#include "agg_conv_stroke.h"
#include "agg_conv_dash.h"
#include "agg_conv_curve.h"
#include "agg_conv_contour.h"

#include "agg_scanline_p.h"
#include "agg_path_storage.h"

#include "agg_renderer_base.h"
#include "agg_renderer_scanline.h"
#include "agg_renderer_primitives.h"
#include "agg_renderer_outline_aa.h"
#include "agg_renderer_outline_image.h"

#include "agg_pixfmt_rgb.h"
#include "agg_pixfmt_rgba.h"

#include "agg_arc.h"
#include "agg_ellipse.h"

#include "agg_pattern_filters_rgba.h"

#include "agg_bounding_rect.h"
#include "agg_span_allocator.h"
#include "agg_image_accessors.h"
#include "agg_span_pattern_rgba.h"
#include "agg_span_interpolator_linear.h"
#include "agg_span_image_filter_rgba.h"
#include "agg_span_image_filter_rgb.h"

#include "agg_trans_affine.h"
#include "agg_scanline_boolean_algebra.h"
#include "agg_scanline_storage_aa.h"
#include "math.h"
#include "mapagg.h"

#include <ft2build.h>
#include "agg_font_freetype.h"
#include "agg_font_cache_manager.h"

#include "agg_glyph_raster_bin.h"
#include "agg_renderer_raster_text.h"
#include "agg_embedded_raster_fonts.h"

#define LINESPACE 1.33 //space beween text lines... from GD
#define _EPSILON 0.00001 //used for double equality testing


#ifdef CPL_MSB
typedef agg::order_argb gd_color_order;
#else
typedef agg::order_bgra gd_color_order;
#endif

typedef agg::blender_rgba_pre<agg::rgba8, gd_color_order> blender_pre; 
typedef agg::pixfmt_alpha_blend_rgba<blender_pre, agg::rendering_buffer, agg::pixel32_type> GDpixfmt;
typedef agg::pixfmt_alpha_blend_rgba<blender_pre,mapserv_row_ptr_cache<int>,int> pixelFormat;

static agg::rgba8 AGG_NO_COLOR = agg::rgba8(0,0,0,0);



typedef agg::rgba8 color_type;
typedef agg::font_engine_freetype_int16 font_engine_type;
typedef agg::font_cache_manager<font_engine_type> font_manager_type;
typedef agg::conv_curve<font_manager_type::path_adaptor_type> font_curve_type;

typedef agg::glyph_raster_bin<color_type> glyph_gen;

typedef agg::renderer_base<pixelFormat> renderer_base;

typedef agg::renderer_scanline_aa_solid<renderer_base> renderer_aa;
typedef agg::renderer_outline_aa<renderer_base> renderer_oaa;
typedef agg::renderer_primitives<renderer_base> renderer_prim;
typedef agg::renderer_scanline_bin_solid<renderer_base> renderer_bin;
typedef agg::rasterizer_outline_aa<renderer_oaa> rasterizer_outline_aa;
typedef agg::rasterizer_outline <renderer_prim> rasterizer_outline;
typedef agg::rasterizer_scanline_aa<> rasterizer_scanline;

///apply line styling functions. applies the line joining and capping
///parameters from the symbolobj to the given stroke
///@param stroke the stroke to which we apply the styling
///@param symbol the symbolobj which may contain the styling info
template<class VertexSource>
static void strokeFromSymbol(VertexSource &stroke, symbolObj *symbol) {
    switch(symbol->linejoin) {
    case MS_CJC_ROUND:
        stroke.line_join(agg::round_join);
        break;
    case MS_CJC_MITER:
        stroke.line_join(agg::miter_join);
        break;
    case MS_CJC_BEVEL:
        stroke.line_join(agg::bevel_join);
        break;
    }
    switch(symbol->linecap) {
    case MS_CJC_BUTT:
        stroke.line_cap(agg::butt_cap);
        break;
    case MS_CJC_ROUND:
        stroke.line_cap(agg::round_cap);
        break;
    case MS_CJC_SQUARE:
        stroke.line_cap(agg::square_cap);
        break;
    }
}
///
///returns a rendering buffer containing the argb pixel values of the gd image.
///the function expects an image with a "gd style" alpha channel, i.e. 
///127...0 actually mapping to 0...255
///NOTE: it is your responsability to free the rendering buffer's memory 
///with a call to delete[](rendering_buffer.buf())
///

static agg::rendering_buffer gdImg2AGGRB_BGRA(gdImagePtr img) {
    int width=img->sx;
    int height=img->sy;
    agg::int8u*           im_data;
    agg::rendering_buffer im_data_rbuf;
    im_data = new agg::int8u[width * height * 4];
    im_data_rbuf.attach(im_data, width,height, width*4);
    for(int row=0;row<height;row++) {
        unsigned int* rowptr=(unsigned int*)im_data_rbuf.row_ptr(row);
        for(int col=0;col<width;col++){
            int gdpix = gdImageGetTrueColorPixel(img,col,row);
            //extract the alpha value from the pixel
            int gdpixalpha = ((gdpix) & 0x7F000000) >> 24;

            if(gdpixalpha==127) {//treat the fully transparent case
                rowptr[col]=0;
            }
            else if(gdpixalpha==0) {//treat the fully opaque case
                rowptr[col]=((gdpix)&0x00FFFFFF)|(255<<24);
            }
            else {
                int alpha=255-(gdpixalpha<<1);
                rowptr[col]=((gdpix)&0x00FFFFFF)|(alpha<<24);
            }      
        }
    }
    return im_data_rbuf;
}

inline agg::rgba8 getAGGColor(colorObj* c, int opacity) {
    if(c && MS_VALID_COLOR(*c)) {
        return agg::rgba8_pre(c->red,c->green,c->blue,MS_NINT(opacity*2.55));
    } else {
        return agg::rgba8(0,0,0,0);
    }
}




///
///returns a GDpixfmt containing thepixel values of the gd image.
///the function expects an image with a "gd style" alpha channel, i.e. 
///127...0 actually mapping to 0...255
///the pixel values are actually cached in the symbolObj for future reuse
///the actual buffer is freed when freeing the symbolObj with a call to
///msFreeSymbolCacheAGG
static GDpixfmt loadSymbolPixmap(symbolObj *sym) {
    GDpixfmt pixf;
    if(sym->renderer_cache) {
        pixf.attach(*((agg::rendering_buffer*)sym->renderer_cache));
    }
    else {
        agg::rendering_buffer *im_data_rbuf = new agg::rendering_buffer;
        *im_data_rbuf = gdImg2AGGRB_BGRA(sym->img);
        sym->renderer_cache=(void*)(im_data_rbuf);
        pixf.attach(*im_data_rbuf);
        pixf.premultiply();
    }
    return pixf;
}

/* 
 * selection from the list of raster fonts provided with agg
 * that best corresponds to the ones provided with GD. This 
 * selection was done visually, first by looking at charcter 
 * size, then resemblance. The chosen fonts are more or less
 * monospaced as this is what is assumed when calculating label 
 * sizes
 */
const agg::int8u* rasterfonts[]= { 
        agg::gse5x7, /*gd tiny. gse5x7 is a bit less high than gd tiny*/
        agg::gse7x11, /*gd small*/
        agg::gse7x11_bold, /*gd medium*/
        agg::gse7x15, /*gd large*/
        agg::gse8x16_bold /*gd huge*/
};

typedef struct {
    int width;
    int height;
} font_size_struct;

const font_size_struct rasterfont_sizes[] = {
        {5,7},
        {7,11},
        {7,11},
        {7,15}, //the width here is an approximation. (not a fixed width font)
        {8,16}
};

///base rendering class for AGG.
///creates the AGG structures used later for rendering.
///the allocation of these structures does take some time and memory, so
///this object should be cached and not created each time a shape has to be drawn
class AGGMapserverRenderer {
public:
    AGGMapserverRenderer(mapserv_row_ptr_cache<int>  *ptr) :
        pRowCache(ptr),
        thePixelFormat(*pRowCache),
        ren_base(thePixelFormat),
        ren_aa(ren_base),
        ren_prim(ren_base),
        ren_bin(ren_base),
        ras_oa(ren_prim),
        m_fman(m_feng)
        {
            
        }
    
    ~AGGMapserverRenderer() {
        delete pRowCache;
    }
    ///clear the whole image.
    ///@param color the fully opaque background color to use  
    void clear(agg::rgba8 &color) {
        ren_base.clear(color);
    }
    
    ///shortcut function to render an ellipse, optinally filled and/or outlined
    ///@param x,y the center of the ellipse
    ///@param w,h the width and height of the ellipse, aligned with the image principal axes
    ///@param color the fill color of the ellipse, or NULL for no fill
    ///@param outlinecolor the color of the outline, or NULL for no outline
    ///@param outlinewidth the width of the optional outline
    void renderEllipse(double x, double y, double w, double h, double angle, agg::rgba8 &color,
            agg::rgba8 &outlinecolor, double outlinewidth=1) {
        agg::path_storage path;
        agg::ellipse ellipse(x,y,w/2.,h/2.0);
        path.concat_path(ellipse);
        if( (fabs(angle)>_EPSILON) || (fabs(MS_2PI-angle)>_EPSILON)) {
            agg::trans_affine mtx;
            mtx *= agg::trans_affine_translation(-x,-y);
            /*agg angles are antitrigonometric*/
            mtx *= agg::trans_affine_rotation(-angle);
            mtx *= agg::trans_affine_translation(x,y);
            path.transform(mtx);
        }
        renderPathSolid(path,color,outlinecolor,outlinewidth);      
    }
    
    ///render a polyline, optionally dashed
    ///@param p the path_storage containing the vertexes of the polyline
    ///@param c the color of the line
    ///@param width the width of the polyline
    ///@param dashstylelength optional length of the dashing parameters.
    ///     set to 0 for no dashes
    ///@param dashstyle array containing the dashing parameters. it's length must be
    ///     greater or eauql to dashstylelength
    ///@param lc the style of the line caps, defaults to round caps
    ///@param lj the style of the line joins, defaults to round joins
    template<class VertexSource>
    void renderPolyline(VertexSource &p,agg::rgba8 &color, 
            double width,int dashstylelength, int *dashstyle,
            enum agg::line_cap_e lc=agg::round_cap,
            enum agg::line_join_e lj=agg::round_join) {
        ras_aa.reset();
        ras_aa.filling_rule(agg::fill_non_zero);
        ren_aa.color(color);

        if (dashstylelength <= 0) {
            agg::conv_stroke<VertexSource> stroke(p);  
            stroke.width(width);
            stroke.line_cap(lc);
            stroke.line_join(lj);
            ras_aa.add_path(stroke);
        } else {
            agg::conv_dash<VertexSource> dash(p);
            agg::conv_stroke<agg::conv_dash<VertexSource> > stroke_dash(dash);  
            for (int i=0; i<dashstylelength; i+=2) {
                if (i < dashstylelength-1)
                    dash.add_dash(dashstyle[i], dashstyle[i+1]);
            }
            stroke_dash.width(width);
            stroke_dash.line_cap(lc);
            stroke_dash.line_join(lj);                        
            ras_aa.add_path(stroke_dash);
        }
        agg::render_scanlines(ras_aa, sl_line, ren_aa);
    }
    
    ///brush a polyline with a vector symbol. draws the vector symbol in a temporary
    ///image that will be used as a brush for rendering the polyline. this function
    ///doesn't do any actual rendering, it only creates the brush and forwards to the
    ///brush rendering function.
    ///@param shape the polyline to brush
    ///@param symbol the shape of the vector symbol used for brushing,
    ///     can be a stroke or a simple path 
    ///@param tilewidth,tileheight size of the brush to be created
    ///@param color the color the vector symbol should be drawn with
    ///@param backgroundcolor optional background color of the tile, or
    ///     NULL to render the symbol on a transparent background
    template<class VertexSource1, class VertexSource2>
    void renderPolylineVectorSymbol(VertexSource1 &shape, VertexSource2 &symbol,
            int tilewidth, int tileheight, 
            agg::rgba8 &color, agg::rgba8 &backgroundcolor) {
        ras_aa.reset();
        ras_aa.filling_rule(agg::fill_non_zero);
        typedef agg::wrap_mode_repeat wrap_type;
        typedef agg::image_accessor_wrap<GDpixfmt,wrap_type,wrap_type> img_source_type;
        typedef agg::span_pattern_rgba<img_source_type> span_gen_type;
        agg::int8u*           m_pattern;
        agg::rendering_buffer m_pattern_rbuf;
        m_pattern = new agg::int8u[tilewidth * tileheight * 4];
        m_pattern_rbuf.attach(m_pattern, tilewidth,tileheight, tilewidth*4);

        GDpixfmt pixf(m_pattern_rbuf);
        agg::renderer_base<GDpixfmt> rb(pixf);
        agg::renderer_scanline_aa_solid<agg::renderer_base<GDpixfmt> > rs(rb);

        rb.clear(backgroundcolor);
        rs.color(color);
        ras_aa.add_path(symbol);
        agg::render_scanlines(ras_aa, sl_line, rs);
        renderPathPixmapBGRA(shape,pixf);
        delete[](m_pattern);
    }
    
    ///brush a line.
    ///@param line the line to brush
    ///@param pattern a pixmap to use as a brush. this pattern must be in a 
    ///     premultiplied state, i.e. each color has been divided by its alpha (mapped to 0..1).
    ///     images produced by the AGG renderers are already premultiplied, but images
    ///     read from an another source (i.e the GD pixmaps) should be explicitely
    ///     premultiplied before calling
    template<class VertexSource>
    void renderPathPixmapBGRA(VertexSource &line, GDpixfmt &pattern) {
        agg::pattern_filter_bilinear_rgba8 fltr;
        typedef agg::line_image_pattern<agg::pattern_filter_bilinear_rgba8> pattern_type;
        typedef agg::renderer_outline_image<renderer_base, pattern_type> renderer_img_type;
        typedef agg::rasterizer_outline_aa<renderer_img_type, agg::line_coord_sat> rasterizer_img_type;
        pattern_type patt(fltr);  
        
        patt.create(pattern);
        renderer_img_type ren_img(ren_base, patt);
        rasterizer_img_type ras_img(ren_img);
        ras_img.add_path(line);
    }

    ///render a shape represented by an agg::path_storage
    ///@param path the path containing the geometry to render
    ///@param color fill color or null for no fill
    ///@param outlinecolor outline color or null for no outline
    ///@param outlinewidth width of outline
    ///@param lc capping used for the optional outline, defaults to round caps
    ///@param lj joins used for the optional outline, defaults to round joins
    template<class VertexSource>
    void renderPathSolid(VertexSource &path, agg::rgba8 &color,
            agg::rgba8 &outlinecolor, double outlinewidth,
            enum agg::line_cap_e lc=agg::round_cap,
            enum agg::line_join_e lj=agg::round_join) {
        ras_aa.reset();
        if(color.a) {
            //use this to preserve holes in the geometry
            //this is needed when drawing fills
            ras_aa.filling_rule(agg::fill_even_odd);
            ras_aa.add_path ( path );
            ren_aa.color(color);
            agg::render_scanlines ( ras_aa, sl_poly, ren_aa );
        }
        if(outlinecolor.a && outlinewidth > 0) {
            ras_aa.reset();
            ras_aa.filling_rule(agg::fill_non_zero); 
            ren_aa.color(outlinecolor);
            agg::conv_stroke<VertexSource> stroke(path);
            stroke.width(outlinewidth);
            stroke.line_cap(lc);
            stroke.line_join(lj);
            ras_aa.add_path(stroke);
            agg::render_scanlines ( ras_aa, sl_line, ren_aa );
        }
    }

    ///render a fill pattern clipped by a shape
    ///this has only been tested when pattern is a stroke, and clipper a path.
    ///used for hatches. note that the pattern is not repeated or tiled
    ///@param pattern the pattern to use as the fill
    ///@param clipper the polygon to use as a clipper. only the pixels inside
    ///     this clipper will be affected by the pattern
    ///@param color the color used to render the pattern
    template<class VertexSource1, class VertexSource2>
    void renderPathSolidClipped(VertexSource1 &pattern, VertexSource2 &clipper,
            agg::rgba8 &color)
    {
        agg::rasterizer_scanline_aa<> ras1,ras2;
        agg::scanline_storage_aa8 storage;
        agg::scanline_storage_aa8 storage1;
        agg::scanline_storage_aa8 storage2;
        agg::scanline_p8 sl1,sl2;
        ras1.filling_rule(agg::fill_non_zero);
        ras1.add_path(pattern);                    
        agg::render_scanlines(ras1, sl_line, storage1);
        ras2.filling_rule(agg::fill_even_odd);
        ras2.add_path(clipper);
        agg::render_scanlines(ras2,sl_poly,storage2);
        agg::sbool_combine_shapes_aa(agg::sbool_and, storage1, storage2, sl1, sl2, sl_line, storage);
        ren_aa.color(color);
        agg::render_scanlines ( storage, sl_line, ren_aa );
    }
    
    ///tile a shape with a vector symbol. this function
    ///doesn't do any actual rendering, it only creates the tile and forwards to the
    ///tiling rendering function.
    ///@param shape the polygon to tile
    ///@param tile the shape of the vector symbol used as a tile,
    ///     can be a stroke or a simple path 
    ///@param tilewidth,tileheight size of the tile to be created
    ///@param color the color the vector symbol should be drawn with
    ///@param backgroundcolor optional background color of the tile, or
    ///     NULL to render the symbol on a transparent background
    ///TODO: add the outlinecolor
    template<class VertexSource1, class VertexSource2>
    void renderPathTiled(VertexSource1 &shape, VertexSource2 &tile,
            int tilewidth, int tileheight, agg::rgba8 &color, agg::rgba8 &backgroundcolor) 
    {
        ras_aa.reset();
        ras_aa.filling_rule(agg::fill_non_zero);
        agg::int8u*           m_pattern;
        agg::rendering_buffer m_pattern_rbuf;
        m_pattern = new agg::int8u[tilewidth * tileheight * 4];
        m_pattern_rbuf.attach(m_pattern, tilewidth,tileheight, tilewidth*4);

        GDpixfmt pixf(m_pattern_rbuf);
        agg::renderer_base<GDpixfmt> rb(pixf);
        agg::renderer_scanline_aa_solid<agg::renderer_base<GDpixfmt> > rs(rb);
        rb.clear(backgroundcolor);
        rs.color(color);
        ras_aa.add_path(tile);
        agg::render_scanlines(ras_aa, sl_poly, rs);
        renderPathTiledPixmapBGRA(shape,pixf);
        delete[](m_pattern);
    }
    ///tile a shape with a truetype character. this function
    ///doesn't do any actual rendering, it only creates the tile and forwards to the
    ///tiling rendering function.
    ///@param shape the polygon to tile
    ///@param font full path of the truetype font file to use
    ///@param glyphUnicode the code of the caracter used 
    ///@param glyphheight size of the character to be rendered
    ///@param gap size in pixels between each rendered character
    ///     (applied vertically and horizontally)
    ///@param color the color the character
    ///@param backgroundcolor optional background color of the tile, or
    ///     NULL to render the symbol on a transparent background
    ///@param outlinecolor optional color of a one pixel width outline drawn around 
    ///     the character, or NULL for no outline       
    template<class VertexSource1>
            void renderPathTruetypeTiled(VertexSource1 &shape, char *font, int glyphUnicode,
                    double glyphheight, double gap,
                    agg::rgba8 &color,
                    agg::rgba8 &backgroundcolor,
                    agg::rgba8 &outlinecolor) 
        {
        if(!m_feng.load_font(font, 0, agg::glyph_ren_outline)) {
            msSetError(MS_TTFERR, "AGG error loading font (%s)", "renderPathTruetypeTiled()", font);
            return;
        }
        m_feng.hinting(true);
        m_feng.height(glyphheight);
        m_feng.resolution(96);
        m_feng.flip_y(true);
        font_curve_type m_curves(m_fman.path_adaptor());
        const agg::glyph_cache* glyph=m_fman.glyph(glyphUnicode);
        if(!glyph) return;
        int gw=glyph->bounds.x2-glyph->bounds.x1+1,
            gh=glyph->bounds.y2-glyph->bounds.y1+1;
        int tilewidth=MS_NINT(gw+gap),
            tileheight=MS_NINT(gh+gap);
        
            ras_aa.filling_rule(agg::fill_non_zero);
            agg::int8u* m_pattern;
            agg::rendering_buffer m_pattern_rbuf;
            m_pattern = new agg::int8u[tilewidth * tileheight * 4];
            m_pattern_rbuf.attach(m_pattern, tilewidth,tileheight, tilewidth*4);

            GDpixfmt pixf(m_pattern_rbuf);
            agg::renderer_base<GDpixfmt> rb(pixf);
            agg::renderer_scanline_aa_solid<agg::renderer_base<GDpixfmt> > rs(rb);
            rb.clear(backgroundcolor);
            
            double fy=(tileheight+gh)/2.;
            double fx=(tilewidth-gw)/2.;
            if(outlinecolor.a) {
                ras_aa.reset();
                m_fman.init_embedded_adaptors(glyph,fx,fy);
                for(int i=-1;i<=1;i++)
                    for(int j=-1;j<=1;j++) {
                        if(i||j) { 
                            agg::trans_affine_translation tr(i,j);
                            agg::conv_transform<font_curve_type, agg::trans_affine> trans_c(m_curves, tr);
                            ras_aa.add_path(trans_c);
                        }
                    }
                rs.color(outlinecolor);
                agg::render_scanlines(ras_aa, sl_line, rs);
            }
            if(color.a) {
                ras_aa.reset();
                m_fman.init_embedded_adaptors(glyph,fx,fy);
                ras_aa.add_path(m_curves);
                rs.color(color);
                agg::render_scanlines(ras_aa, sl_line, rs);
            }
            renderPathTiledPixmapBGRA(shape,pixf);
            delete[](m_pattern);
        }
    
    
    ///tile a path with a pixmap symbol. the pixmap is repeated in each direction
    ///@param path the polygon to fill
    ///@param tile a pixmap to use as a tile. this pixmap must be in a 
    ///     premultiplied state, i.e. each color has been divided by its alpha (mapped to 0..1).
    ///     images produced by the AGG renderers are already premultiplied, but images
    ///     read from an another source (i.e the GD pixmaps) should be explicitely
    ///     premultiplied before calling
    template<class VertexSource1>
    void renderPathTiledPixmapBGRA(VertexSource1 &path ,GDpixfmt &tile) {
        typedef agg::wrap_mode_repeat wrap_type;
        typedef agg::image_accessor_wrap<GDpixfmt,wrap_type,wrap_type> img_source_type;
        typedef agg::span_pattern_rgba<img_source_type> span_gen_type;
        agg::span_allocator<agg::rgba8> sa;
        ras_aa.reset();
        ras_aa.filling_rule(agg::fill_even_odd);
        img_source_type img_src(tile);
        span_gen_type sg(img_src, 0, 0);
        ras_aa.add_path(path);
        agg::render_scanlines_aa(ras_aa, sl_poly, ren_base, sa, sg);
    }

    ///render a single pixmap at a specified location
    ///@param img_pixf the pixmap to render. must be premultiplied
    ///@param x,y where to render the pixmap. this is the point where the
    ///     center of the pixmap will be placed
    ///@param angle,scale angle and scale for rendering the pixmap. angle is in radians.
    ///     if one of these values is meaningfull (i.e angle!=0, scale!=1), bilinear
    ///     filtering will be applied. if not the image is copied without subpixel positioning
    ///     (i.e. at the nearest integer position)to avoid the blur caused by the bilinear filtering
    void renderPixmapBGRA(GDpixfmt &img_pixf, double x, double y, double angle, double scale) {
        ras_aa.reset();
        ras_aa.filling_rule(agg::fill_non_zero);
        
        if( (fabs(angle)>_EPSILON) || (fabs(MS_2PI-angle)>_EPSILON) || scale !=1) {
            agg::trans_affine image_mtx;
            image_mtx *= agg::trans_affine_translation(-(double)img_pixf.width()/2.,
                    -(double)img_pixf.height()/2.);
            /*agg angles are antitrigonometric*/
            image_mtx *= agg::trans_affine_rotation(-angle);
            image_mtx *= agg::trans_affine_scaling(scale);



            image_mtx*= agg::trans_affine_translation(x,y);
            image_mtx.invert();
            typedef agg::span_interpolator_linear<> interpolator_type;
            interpolator_type interpolator(image_mtx);
            agg::span_allocator<agg::rgba8> sa;

            // "hardcoded" bilinear filter
            //------------------------------------------
            typedef agg::span_image_filter_rgba_bilinear_clip<GDpixfmt, interpolator_type> span_gen_type;
            span_gen_type sg(img_pixf, agg::rgba(0,0,0,0), interpolator);
            agg::path_storage pixmap_bbox;
            int ims_2 = MS_NINT(MS_MAX(img_pixf.height(),img_pixf.width())*scale*1.415)/2+1;
            pixmap_bbox.move_to(x-ims_2,y-ims_2);
            pixmap_bbox.line_to(x+ims_2,y-ims_2);
            pixmap_bbox.line_to(x+ims_2,y+ims_2);
            pixmap_bbox.line_to(x-ims_2,y+ims_2);
            pixmap_bbox.close_polygon();      
            ras_aa.add_path(pixmap_bbox);
            agg::render_scanlines_aa(ras_aa, sl_line, ren_base, sa, sg);
        }
        else {
            //just copy the image at the correct location (we place the pixmap on 
            //the nearest integer pixel to avoid blurring)
            ren_base.blend_from(img_pixf,0,MS_NINT(x-img_pixf.width()/2.),MS_NINT(y-img_pixf.height()/2.));
        }
    }
    
    int renderRasterGlyphs(double x, double y, agg::rgba8 &color, agg::rgba8 &outlinecolor,
            int size, char *thechars) {
        glyph_gen glyph(0);
        agg::renderer_raster_htext_solid<renderer_base, glyph_gen> rt(ren_base, glyph);
        glyph.font(rasterfonts[size]);
        int numlines=0;
        char **lines;
        /*masking out the out-of-range character codes*/
        int len;
        int cc_start = rasterfonts[size][2];
        int cc_end = cc_start + rasterfonts[size][3];
        if((lines = msStringSplit((const char*)thechars, '\n', &(numlines))) == NULL)
            return(-1);
        for(int n=0;n<numlines;n++) {
            len = strlen(lines[n]);
            for (int i = 0; i < len; i++)
            if (lines[n][i] < cc_start || lines[n][i] > cc_end)
                lines[n][i] = '.';
            
            if(outlinecolor.a) {
                rt.color(outlinecolor);
                for(int i=-1;i<=1;i++) {
                    for(int j=-1;j<=1;j++) {
                        if(i||j) {
                            rt.render_text(x+i, y+j, lines[n], true);
                        }
                    }
                }
            }
            rt.color(color);
            rt.render_text(x, y, lines[n], true);
            y += glyph.height();
        }
        msFreeCharArray(lines, numlines);
        return MS_SUCCESS;
    }
    
    int getLabelSize(char *string, char *font, double size, rectObj *rect, double **advances) {

        if(!m_feng.load_font(font, 0, agg::glyph_ren_outline)) {
            msSetError(MS_TTFERR, "AGG error loading font (%s)", "getLabelSize()", font);
            return MS_FAILURE;
        }
        m_feng.hinting(true);
        m_feng.height(size);
        m_feng.resolution(96);
        m_feng.flip_y(true);
        int unicode,curGlyph=1,numglyphs;
        if(advances) {
            numglyphs=msGetNumGlyphs(string);
        }
        const agg::glyph_cache* glyph;
        string+=msUTF8ToUniChar(string, &unicode);
        glyph=m_fman.glyph(unicode);
        if(glyph){
            rect->minx=glyph->bounds.x1;
            rect->maxx=glyph->bounds.x2;
            rect->miny=glyph->bounds.y1;
            rect->maxy=glyph->bounds.y2;
        }
        else
            return MS_FAILURE;
        if(advances) {
            *advances = (double*)malloc(numglyphs*sizeof(double));
            (*advances)[0]=glyph->advance_x;
        }
        double fx=glyph->advance_x,fy=glyph->advance_y;
        while(*string) {
            if(advances) {
                if(*string=='\r' || *string=='\n')
                    (*advances)[curGlyph++]=-fx;
            }
            if(*string=='\r') {fx=0;string++;continue;}
            if(*string=='\n') {fx=0;fy+=ceil(size*LINESPACE);string++;continue;}
            string+=msUTF8ToUniChar(string, &unicode);
            glyph=m_fman.glyph(unicode);
            if(glyph)
            {
                double t;
                if((t=fx+glyph->bounds.x1)<rect->minx) rect->minx=t;
                if((t=fx+glyph->bounds.x2)>rect->maxx) rect->maxx=t;
                if((t=fy+glyph->bounds.y1)<rect->miny) rect->miny=t;
                if((t=fy+glyph->bounds.y2)>rect->maxy) rect->maxy=t;

                fx += glyph->advance_x;
                fy += glyph->advance_y;
                if(advances) {
                    (*advances)[curGlyph++]=glyph->advance_x;
                }
            }
        }
        return MS_SUCCESS;
    }
    
      
    ///render a freetype string
    ///@param x,y the lower left corner where to start the string, or the center of
    ///     the character if isMarker is true
    ///@param color the font color
    ///@param outlinecolor optional color used for outlining the text
    ///@param size height in pixels of the font
    ///@param font full path of the truetype font to use
    ///@param thechars null terminated string to render
    ///@param angle angle to use. in radians
    ///@param shadowcolor, shdx,shdy color and offset of an optional shadow. defaults
    ///     to being offset one pixel to the lower right.
    ///@param isMarker defines if the text should have its lower left corner start at the
    ///     given x,y (false), or if the text should be centered on x,y (true).
    ///     when set to true, will only center the text if this one is a single character
    int renderGlyphs(double x, double y, agg::rgba8 &color, agg::rgba8 &outlinecolor,
            double size, char *font, char *thechars, double angle,
            agg::rgba8 &shadowcolor, double shdx, double shdy,
            int outlinewidth) {
        if(!m_feng.load_font(font, 0, agg::glyph_ren_outline)) {
            msSetError(MS_TTFERR, "AGG error loading font (%s)", "renderGlyphs()", font);
            return MS_FAILURE;
        }
        ras_aa.filling_rule(agg::fill_non_zero);
        agg::trans_affine mtx;
        mtx *= agg::trans_affine_translation(-x,-y);
        /*agg angles are antitrigonometric*/
        mtx *= agg::trans_affine_rotation(-angle);
        mtx *= agg::trans_affine_translation(x,y);
        
        
        
        m_feng.hinting(true);
        m_feng.height(size);
        m_feng.resolution(96);
        m_feng.flip_y(true);
        font_curve_type m_curves(m_fman.path_adaptor());
        const agg::glyph_cache* glyph;
        int unicode;
        
        
        double fx=x,fy=y;
        const char *utfptr=thechars;
        agg::path_storage glyphs;
        
        //first render all the glyphs to a path
        while(*utfptr) {
            if(*utfptr=='\r') {fx=x;utfptr++;continue;}
            if(*utfptr=='\n') {fx=x;fy+=ceil(size*LINESPACE);utfptr++;continue;}
            utfptr+=msUTF8ToUniChar(utfptr, &unicode);
            glyph=m_fman.glyph(unicode);;
            if(glyph)
            {
                m_fman.init_embedded_adaptors(glyph,fx,fy);
                agg::conv_transform<font_curve_type, agg::trans_affine> trans_c(m_curves, mtx);
                glyphs.concat_path(trans_c);
                fx += glyph->advance_x;
                fy += glyph->advance_y;
            }
        }
        
        //use a smoother renderer for the shadow
        if(shadowcolor.a) {
            agg::trans_affine_translation tr(shdx,shdy);
            agg::conv_transform<agg::path_storage, agg::trans_affine> tglyphs(glyphs,tr);
            agg::line_profile_aa prof;
            prof.width(0.5);
            renderer_oaa ren_oaa(ren_base,prof);
            rasterizer_outline_aa rasterizer_smooth(ren_oaa);
            ren_oaa.color(shadowcolor);
            rasterizer_smooth.add_path(tglyphs);
        }
        if(outlinecolor.a) {
            ras_aa.reset();
            ras_aa.filling_rule(agg::fill_non_zero);
            if(outlinewidth==1) {
            //draw the text offset by one pixel in each direction (NW,W,SW,N,S,NE,E,SE)
                for(int i=-1;i<=1;i++) {
                    for(int j=-1;j<=1;j++) {
                        if(i||j) {
                            agg::trans_affine_translation tr(i,j);
                            agg::conv_transform<agg::path_storage, agg::trans_affine> tglyphs(glyphs,tr);
                            ras_aa.add_path(tglyphs);
                        }
                    }
                }
            }
            else {
                agg::conv_contour<agg::path_storage> cc(glyphs);
                cc.width(outlinewidth);
                ras_aa.add_path(cc);
            }
            ren_aa.color(outlinecolor);
            agg::render_scanlines(ras_aa, sl_line, ren_aa);
        }
    
        if(color.a) {
            ras_aa.reset();
            ras_aa.filling_rule(agg::fill_non_zero);
            ras_aa.add_path(glyphs);
            ren_aa.color(color);
            agg::render_scanlines(ras_aa, sl_line, ren_aa);
        }
        return MS_SUCCESS;
    }
private:
    mapserv_row_ptr_cache<int>  *pRowCache;
    pixelFormat thePixelFormat;
    renderer_base ren_base;
    renderer_aa ren_aa;
    renderer_prim ren_prim;
    renderer_bin ren_bin;
    agg::scanline_p8 sl_poly; /*packed scanlines, works faster when the area is larger 
    than the perimeter, in number of pixels*/
    agg::scanline_u8 sl_line; /*unpacked scanlines, works faster if the area is roughly
    equal to the perimeter, in number of pixels*/
    agg::scanline_bin m_sl_bin;
    rasterizer_scanline ras_aa;
    rasterizer_outline ras_oa;
    font_engine_type m_feng;
    font_manager_type m_fman;
};

// ----------------------------------------------------------------------
// Utility function to create a GD image and its associated AGG renderer.
// Returns a pointer to a newly created imageObj structure.
// a pointer to the AGG renderer is stored in the imageObj, used for caching
// ----------------------------------------------------------------------
imageObj *msImageCreateAGG(int width, int height, outputFormatObj *format, char *imagepath, char *imageurl) 
{
    imageObj *pNewImage = NULL;

    if(format->imagemode != MS_IMAGEMODE_RGB && format->imagemode != MS_IMAGEMODE_RGBA) {
      msSetError(MS_AGGERR, "AGG driver only supports RGB or RGBA pixel models.", "msImageCreateAGG()");
      return NULL;
    }

    pNewImage = msImageCreateGD(width, height, format, imagepath, imageurl);
    if(!pNewImage)
      return pNewImage;

    mapserv_row_ptr_cache<int>  *pRowCache = new mapserv_row_ptr_cache<int>(pNewImage->img.gd);
    if(! pRowCache) {
      msSetError(MS_AGGERR, "Error binding GD image to AGG.", "msImageCreateAGG()");
      return NULL;
    }

    AGGMapserverRenderer *ren = new AGGMapserverRenderer(pRowCache);
    pNewImage->imageextra=(void *)ren;
    return pNewImage;
}

///internally used function to get the cached AGG renderer.
AGGMapserverRenderer* getAGGRenderer(imageObj *image) {
    return (AGGMapserverRenderer*)image->imageextra;
}

// ----------------------------------------------------------------------
// Utility function to initialize the color of an image.  The background
// color is passed, but the outputFormatObj is consulted to see if the
// transparency should be set (for RGBA images).
// for the time being we fall back to GD
// ----------------------------------------------------------------------
void msImageInitAGG(imageObj *image, colorObj *background)
{
    
    AGGMapserverRenderer* ren = getAGGRenderer(image);
    if(image->format->imagemode == MS_IMAGEMODE_RGBA) {
        ren->clear(AGG_NO_COLOR);
    } else {
        agg::rgba8 bc = getAGGColor(background,100);
        ren->clear(bc);
    }
    image->buffer_format=MS_RENDER_WITH_AGG;
    /*
    msImageInitGD(image, background);
    image->buffer_format=MS_RENDER_WITH_GD;*/
}

// ------------------------------------------------------------------------ 
// Function to create a custom hatch symbol based on an arbitrary angle. 
// ------------------------------------------------------------------------
static agg::path_storage createHatchAGG(int sx, int sy, double angle, double step)
{
    agg::path_storage path;
    //restrict the angle to [0 180[
    angle = fmod(angle, 360.0);
    if(angle < 0) angle += 360;
    if(angle >= 180) angle -= 180;

    //treat 2 easy cases which would cause divide by 0 in generic case
    if(angle==0) {
        for(double y=step/2;y<sy;y+=step) {
            path.move_to(0,y);
            path.line_to(sx,y);
        }
        return path;
    }
    if(angle==90) {
        for(double x=step/2;x<sx;x+=step) {
            path.move_to(x,0);
            path.line_to(x,sy);
        }
        return path;
    }


    double theta = (90-angle)*MS_DEG_TO_RAD;
    double ct = cos(theta);
    double st = sin(theta);
    double rmax = sqrt((double)sx*sx+sy*sy);

    //parametrize each line as r = x.cos(theta) + y.sin(theta)
    for(double r=(angle<90)?0:-rmax;r<rmax;r+=step) {
        int inter=0;
        double x,y;
        double pt[8]; //array to store the coordinates of intersection of the line with the sides
        //in the general case there will only be two intersections
        //so pt[4] should be sufficient to store the coordinates of the intersection,
        //but we allocate pt[8] to treat the special and rare/unfortunate case when the
        //line is a perfect diagonal (and therfore intersects all four sides)
        //note that the order for testing is important in this case so that the first
        //two intersection points actually correspond to the diagonal and not a degenerate line
        
        //test for intersection with each side

        y=r/st;x=0; // test for intersection with top of image
        if(y>=0&&y<=sy) {
            pt[2*inter]=x;pt[2*inter+1]=y;
            inter++;
        }     
        x=sx;y=(r-sx*ct)/st;// test for intersection with bottom of image
        if(y>=0&&y<=sy) {
            pt[2*inter]=x;pt[2*inter+1]=y;
            inter++;
        }
        y=0;x=r/ct;// test for intersection with left of image
        if(x>=0&&x<=sx) {
            pt[2*inter]=x;pt[2*inter+1]=y;
            inter++;
        }
        y=sy;x=(r-sy*st)/ct;// test for intersection with right of image
        if(x>=0&&x<=sx) {
            pt[2*inter]=x;pt[2*inter+1]=y;
            inter++;
        }
        if(inter==2) { 
            //the line intersects with two sides of the image, it should therefore be drawn
            path.move_to(pt[0],pt[1]);
            path.line_to(pt[2],pt[3]);
        }
    }
    return path;
}
// ----------------------------------------------------------------
// create a path from the list of points contained in the symbolObj
// -----------------------------------------------------------------
static agg::path_storage imageVectorSymbolAGG(symbolObj *symbol, double scale) {
    agg::path_storage path;
    bool is_new=true;
    for(int i=0;i < symbol->numpoints;i++) {
        if((symbol->points[i].x == -99) && (symbol->points[i].y == -99)) { // (PENUP) 
            is_new=true;
        } else {
            if(is_new) {
                path.move_to(scale*symbol->points[i].x,scale*symbol->points[i].y);
                is_new=false;                         
            }
            else {
                path.line_to(scale*symbol->points[i].x,scale*symbol->points[i].y);
            }
        }
    }         
    return path;
}

// ---------------------------------------------------------------------------
//       Stroke an ellipse with a line symbol of the specified size and color
//  NOTE: this function is actually never called . 
//  redirecting to msCircleDrawShadeSymbolAGG to allow compilation
// ---------------------------------------------------------------------------
void msCircleDrawLineSymbolAGG(symbolSetObj *symbolset, imageObj *image, pointObj *p, double r, styleObj *style, double scalefactor)
{
    msCircleDrawShadeSymbolAGG(symbolset, image, p, r, style, scalefactor);
}

// ------------------------------------------------------------------------------- 
//      Fill a circle with a shade symbol of the specified size and color         
// ------------------------------------------------------------------------------- 
void msCircleDrawShadeSymbolAGG(symbolSetObj *symbolset, imageObj *image, pointObj *p, double r, styleObj *style, double scalefactor)
{

    AGGMapserverRenderer* ren = getAGGRenderer(image);
    char bRotated=MS_FALSE;
    symbolObj *symbol;

    double size, d, angle, angle_radians,width;

    if(!p) return;
    if(style->symbol >= symbolset->numsymbols || style->symbol < 0) return; // no such symbol, 0 is OK
    symbol = symbolset->symbol[style->symbol];

    /**
     * this seems to never be used - leaving for history's sake
     * 
    if(!MS_VALID_COLOR(style->color) && MS_VALID_COLOR(style->outlinecolor) && symbol->type != MS_SYMBOL_PIXMAP) {
      msCircleDrawLineSymbolAGG(symbolset, image, p, r, style, scalefactor);
      return;
    }
     */

    if(style->size == -1) {
        size = msSymbolGetDefaultSize( ( symbolset->symbol[style->symbol] ) );
        size = size*scalefactor;
    } else
        size = style->size*scalefactor;
    size = MS_MAX(size, style->minsize);
    size = MS_MIN(size, style->maxsize);

    width = style->width*scalefactor;
    width = MS_MAX(width, style->minwidth);
    width = MS_MIN(width, style->maxwidth);

    angle = (style->angle) ? style->angle : 0.0;
    angle_radians = angle*MS_DEG_TO_RAD;

    agg::path_storage circle;
    agg::arc ellipse( p->x,p->y,r,r,0,MS_2PI,true );
    //agg::ellipse ellipse(p->x,p->y,r,r);
    ellipse.approximation_scale ( 1 );
    circle.concat_path(ellipse);
    circle.transform(agg::trans_affine_translation(style->offsetx,style->offsety));
    if(size < 1) return; // size too small
    
    agg::rgba8 agg_color,agg_ocolor,agg_bcolor;
    agg_color=getAGGColor(&style->color,style->opacity);
    agg_ocolor=getAGGColor(&style->outlinecolor,style->opacity);
    agg_bcolor=getAGGColor(&style->backgroundcolor,style->opacity);
    
    
    
    if(style->symbol == 0) { // solid fill
        ren->renderPathSolid(circle,agg_color,agg_ocolor,style->width);
        return; // done simple case
    }
    switch(symbol->type) {
    case(MS_SYMBOL_TRUETYPE):
        //TODO
    break;
    case(MS_SYMBOL_HATCH): {
        agg::path_storage hatch;
        //fill the circle
        ren->renderPathSolid(circle,agg_bcolor,AGG_NO_COLOR,1);
        int s = MS_NINT(2*r)+1;
        hatch = createHatchAGG(s,s,style->angle,size);
        hatch.transform(agg::trans_affine_translation(p->x-r,p->y-r));
        agg::conv_stroke <agg::path_storage > stroke(hatch);
        stroke.width(style->width);
        //render the actual hatches
        ren->renderPathSolidClipped(stroke,circle,agg_color);
        //render the outline. this is done at the end so the outline is drawn
        //over the hatches (prevents faint artifacts)
        ren->renderPathSolid(circle,AGG_NO_COLOR,agg_ocolor,1);
        return;
    }
    case(MS_SYMBOL_PIXMAP): {
        //TODO: rotate and scale image before tiling ?
        //TODO: treat symbol GAP ?
        GDpixfmt img_pixf=loadSymbolPixmap(symbol);
        //render the optional background
        ren->renderPathSolid(circle,agg_bcolor,AGG_NO_COLOR,width);
        //render the actual tiled circle
        ren->renderPathTiledPixmapBGRA(circle,img_pixf);
        //render the optional outline (done at the end to avoid artifacts)
        ren->renderPathSolid(circle,AGG_NO_COLOR,agg_ocolor,style->width);      
    }
    break;
    case(MS_SYMBOL_ELLIPSE): {       
        d = size/symbol->sizey; // size ~ height in pixels 
        int pw = MS_NINT(symbol->sizex*d)+1;
        int ph = MS_NINT(symbol->sizey*d)+1;

        if((pw <= 1) && (ph <= 1)) { // No sense using a tile, just fill solid 
            ren->renderPathSolid(circle,agg_color,agg_ocolor,style->width);
        }
        else {
            agg::path_storage path;
            agg::arc ellipse ( pw/2.,ph/2.,
                    d*symbol->points[0].x/2.,d*symbol->points[0].y/2.,
                    0,MS_2PI,true );
            ellipse.approximation_scale(1);
            path.concat_path(ellipse);
            if(symbol->gap>0) {
                double gap = symbol->gap*d;
                //adjust the size of the tile to count for the gap
                pw+=MS_NINT(gap);
                ph+=MS_NINT(gap);
                //center the ellipse symbol on the tile
                path.transform(agg::trans_affine_translation(gap/2.,gap/2.));
            }
            //render the actual tiled circle
            ren->renderPathTiled(circle,ellipse,pw,ph,
                    agg_color,agg_bcolor);
            //render the optional outline (done at the end to avoid artifacts)
            ren->renderPathSolid(circle,AGG_NO_COLOR,agg_ocolor,style->width);
        }
    }
    break;
    case(MS_SYMBOL_VECTOR): {
        d = size/symbol->sizey; /* size ~ height in pixels */

        if (angle != 0.0 && angle != 360.0) {
            bRotated = MS_TRUE;
            symbol = msRotateSymbol(symbol, style->angle);
        }

        int pw = MS_NINT(symbol->sizex*d);    
        int ph = MS_NINT(symbol->sizey*d);

        if((pw <= 1) && (ph <= 1)) { // No sense using a tile, just fill solid
            ren->renderPathSolid(circle,agg_color,agg_ocolor,style->width);
            return;
        }
        agg::path_storage path = imageVectorSymbolAGG(symbol,d);

        if(symbol->gap>0) {
            double gap = symbol->gap*d;
            //adjust the size of the tile to count for the gap
            pw+=MS_NINT(gap);
            ph+=MS_NINT(gap);
            //center the vector symbol on the tile
            path.transform(agg::trans_affine_translation(gap/2.,gap/2.));
        }
        if(symbol->filled) {
            ren->renderPathTiled(circle,path,pw,ph,agg_color,agg_bcolor);
            ren->renderPathSolid(circle,AGG_NO_COLOR,agg_ocolor,style->width);
        } else  { //symbol is a line, convert to a stroke to apply the width to the line
            agg::conv_stroke <agg::path_storage > stroke(path);
            stroke.width(width);
            strokeFromSymbol(stroke,symbol);
            ren->renderPathTiled(circle,stroke,pw,ph,agg_color,agg_bcolor);
            ren->renderPathSolid(circle,AGG_NO_COLOR,agg_ocolor,1);
        }

        if(bRotated) { // free the rotated symbol
            msFreeSymbol(symbol);
            msFree(symbol);
        }
    }
    break;
    default:
        break;
    }

    return;
}

// ------------------------------------------------------------------------------- 
//       Draw a single marker symbol of the specified size and color               
// ------------------------------------------------------------------------------- 
void msDrawMarkerSymbolAGG(symbolSetObj *symbolset, imageObj *image, pointObj *p, styleObj *style, double scalefactor)
{
    AGGMapserverRenderer* ren = getAGGRenderer(image);
    double size, angle, angle_radians,width,ox,oy;
    if(!p) return;
    bool bRotated=false;
    double d;

    if(style->symbol >= symbolset->numsymbols || style->symbol < 0) return; /* no such symbol, 0 is OK   */
    symbolObj *symbol = symbolset->symbol[style->symbol];

    ox = style->offsetx; /* TODO: add scaling? */
    oy = style->offsety;

    if(style->size == -1) {
        size = msSymbolGetDefaultSize(symbolset->symbol[style->symbol]);
        size = MS_NINT(size*scalefactor);
    } else
        size = MS_NINT(style->size*scalefactor);
    size = MS_MAX(size, style->minsize);
    size = MS_MIN(size, style->maxsize);
    if (symbol->sizey)
        d = size/symbol->sizey; /* compute the scaling factor (d) on the unrotated symbol */
    else
        d = 1;
    width = MS_NINT(style->width*scalefactor);
    width = MS_MAX(width, style->minwidth);
    width = MS_MIN(width, style->maxwidth);

    angle = (style->angle) ? style->angle : 0.0;
    angle_radians = angle*MS_DEG_TO_RAD;

   if(!MS_VALID_COLOR(style->color) && 
           !MS_VALID_COLOR(style->outlinecolor) && 
           symbol->type != MS_SYMBOL_PIXMAP) 
       return; // nothing to do if no color, except for pixmap symbols
   
    if(size < 1) return; // size too small 
    agg::rgba8 agg_color,agg_ocolor,agg_bcolor;
    agg_color=getAGGColor(&style->color,style->opacity);
    agg_ocolor=getAGGColor(&style->outlinecolor,style->opacity);
    agg_bcolor=getAGGColor(&style->backgroundcolor,style->opacity);
    if(style->symbol == 0) { // simply draw a circle of the specified color
        ren->renderEllipse(p->x+ox,p->y+oy,size,size,0,agg_color,agg_ocolor,width);
        return;
    }  

    switch(symbol->type) {
    case(MS_SYMBOL_TRUETYPE): {
        char* font = msLookupHashTable(&(symbolset->fontset->fonts), symbol->font);
        if(!font) return;
        double x,y;
        rectObj bounds;
        if(ren->getLabelSize(symbol->character,font,size,&bounds,NULL)!=MS_SUCCESS)
            return;
        x = p->x + ox - bounds.minx - (bounds.maxx-bounds.minx)/2.;
        y = p->y + oy - bounds.maxy + (bounds.maxy-bounds.miny)/2.;
        ren->renderGlyphs(x,y,agg_color,agg_ocolor,
                size,font,symbol->character,angle_radians,AGG_NO_COLOR,0,0,MS_NINT(style->width));
    }
    break;    
    case(MS_SYMBOL_PIXMAP): {
        GDpixfmt img_pixf = loadSymbolPixmap(symbol);
        ren->renderPixmapBGRA(img_pixf,p->x+ox,p->y+oy,angle_radians,d);
    }
    break;    
    case(MS_SYMBOL_ELLIPSE): {
        double w, h, x, y;
        w = size*symbol->sizex/symbol->sizey; // ellipse size
        h = size;
        x = p->x + ox;
        y = p->y + oy;

        if(symbol->filled) {
            //draw an optionnally filled and/or outlined ellipse
            ren->renderEllipse(x,y,w,h,angle_radians,agg_color,agg_ocolor,width);
        }
        else {
            agg::rgba8 *c;
            if(agg_color.a)
                c=&agg_color;
            else if(agg_ocolor.a)
                c=&agg_ocolor;
            else
                return;
            //draw only the outline
            ren->renderEllipse(x,y,w,h,angle_radians,AGG_NO_COLOR,*c,width);
        }
    }
    break;    
    case(MS_SYMBOL_VECTOR): {
        if(angle != 0.0 && angle != 360.0) {      
            bRotated = true;
            symbol = msRotateSymbol(symbol, angle);
        }
        agg::path_storage path = imageVectorSymbolAGG(symbol,d);
        //center the symbol on the marker location
        agg::trans_affine translation = agg::trans_affine_translation(
                p->x - d*.5*symbol->sizex + ox,
                p->y - d*.5*symbol->sizey + oy);
        path.transform(translation);
        if(symbol->filled) {
            //draw an optionnally filled and/or outlined vector symbol
            ren->renderPathSolid(path,agg_color,agg_ocolor,width);
        }
        else {
            agg::rgba8 *c;
            if(agg_color.a)
                c=&agg_color;
            else if(agg_ocolor.a)
                c=&agg_ocolor;
            else
                return;
            //draw only the outline
            ren->renderPathSolid(path,AGG_NO_COLOR,*c,width);
        }
    }
    break;
    default:
        break; 
    }
    if(bRotated) {
        msFreeSymbol(symbol); // clean up
        msFree(symbol);
    }
}


// --------------------------------------------------------------------------
// render markers along a polyline according to the symbolObj's GAP parameter
// draws only the markers, not the line itself
// --------------------------------------------------------------------------
void drawPolylineMarkers(imageObj *image, shapeObj *p, symbolSetObj *symbolset,
        styleObj *style, double size) {
    symbolObj *symbol=symbolset->symbol[style->symbol];
    GDpixfmt img_pixf;
    agg::path_storage vector_symbol;
    
    bool bRotated=false;
    AGGMapserverRenderer* ren = getAGGRenderer(image);
    double gap = symbol->gap;
    double d;
    double outlinewidth=1;
    if(style->width!=-1)
        outlinewidth=style->width;
    pointObj point;
    bool rotate_symbol = gap<0;
    if (symbol->sizey)
        d = size/symbol->sizey; // compute the scaling factor
    else
        d = 1;
    
    //preload the symbol if necessary
    if(symbol->type==MS_SYMBOL_PIXMAP) {
        img_pixf = loadSymbolPixmap(symbol);
    }
    else if(symbol->type==MS_SYMBOL_VECTOR) {
        if(style->angle != 0.0 && style->angle != 360.0) {      
            bRotated = true;
            symbol = msRotateSymbol(symbol, style->angle);
        }
        vector_symbol = imageVectorSymbolAGG(symbol,d);  
    }
    
    double sw = size*symbol->sizex/symbol->sizey; // symbol size
    double sh = size;
    gap = MS_ABS(gap)*d; //TODO: original version uses scalefactor, why?
    double symbol_width;
    if(symbol->type==MS_SYMBOL_PIXMAP)
        symbol_width = img_pixf.width();
    else
        symbol_width=sw;
    double angle_radians = style->angle*MS_DEG_TO_RAD;
    
    agg::rgba8 agg_color,agg_ocolor,agg_bcolor;
    agg_color=getAGGColor(&style->color,style->opacity);
    agg_ocolor=getAGGColor(&style->outlinecolor,style->opacity);
    agg_bcolor=getAGGColor(&style->backgroundcolor,style->opacity);
    
    for(int i=0; i<p->numlines; i++) 
    {
        double current_length = 1+symbol_width/2.0; // initial padding for each line
        for(int j=1;j<p->line[i].numpoints;j++) 
        {
            double length = sqrt((pow((p->line[i].point[j].x - p->line[i].point[j-1].x),2) + pow((p->line[i].point[j].y - p->line[i].point[j-1].y),2)));
            if(length==0)continue;
            double rx = (p->line[i].point[j].x - p->line[i].point[j-1].x)/length;
            double ry = (p->line[i].point[j].y - p->line[i].point[j-1].y)/length;  
            double theta = asin(ry);
            if(rx < 0) {
                if(rotate_symbol){
                    theta += MS_PI;
                }
            }
            else theta = -theta;       
            double angle=angle_radians;
            if(rotate_symbol)
                angle += theta;
            bool in = false;
            while(current_length <= length) {
                point.x = p->line[i].point[j-1].x + current_length*rx;
                point.y = p->line[i].point[j-1].y + current_length*ry;
                switch(symbol->type) {
                case MS_SYMBOL_PIXMAP: {
                    ren->renderPixmapBGRA(img_pixf,point.x,point.y,angle,d);
                }
                    break;
                case MS_SYMBOL_ELLIPSE:
                    if(symbol->filled) {
                        //draw an optionnally filled and/or outlined vector symbol
                        ren->renderEllipse(point.x,point.y,sw,sh,0,agg_color,agg_ocolor,outlinewidth);
                    }
                    else {
                        agg::rgba8 *c;
                        if(agg_color.a)
                            c=&agg_color;
                        else if(agg_ocolor.a)
                            c=&agg_ocolor;
                        else
                            return;
                        //draw only the outline
                        ren->renderEllipse(point.x,point.y,sw,sh,0,AGG_NO_COLOR,*c,outlinewidth);
                    }
                    break;
                case MS_SYMBOL_VECTOR: {
                    agg::path_storage rotsym = vector_symbol;
                    rotsym.transform(agg::trans_affine_translation(-sw/2,-sh/2));
                    rotsym.transform(agg::trans_affine_rotation(-angle));
                    rotsym.transform(agg::trans_affine_translation(point.x,point.y));
                    if(symbol->filled) {
                        //draw an optionnally filled and/or outlined vector symbol
                        ren->renderPathSolid(rotsym,agg_color,agg_ocolor,outlinewidth);
                    }
                    else {
                        agg::rgba8 *c;
                        if(agg_color.a)
                            c=&agg_color;
                        else if(agg_ocolor.a)
                            c=&agg_ocolor;
                        else
                            return;
                        //draw only the outline
                        ren->renderPathSolid(rotsym,AGG_NO_COLOR,*c,outlinewidth);
                    }
                }
                break;
                }

                current_length += symbol_width + gap;
                in = true;
            }

            if(in)
            {
                current_length -= length + symbol_width/2.0;
            }         
            else current_length -= length;
        }

    }


    if(symbol->type==MS_SYMBOL_VECTOR && bRotated) {
        msFreeSymbol(symbol); // clean up
        msFree(symbol);
    }
}

// --------------------------------------------------------------------------
// render a truetype character along a polyline according to the symbolObj's GAP parameter
// draws only the characters, not the line itself
// TODO: should this function be merged with drawPolylineMarkers ?
// --------------------------------------------------------------------------
void msImageTruetypePolylineAGG(symbolSetObj *symbolset, imageObj *image, shapeObj *p, styleObj *style, double scalefactor)
{
  int i,j;
  double theta, length, current_length;
  labelObj label;
  pointObj point, label_point;
  rectObj label_rect;
  int label_width;
  int  rot, position, gap, in;
  double rx, ry, size;
  
  symbolObj *symbol;

  AGGMapserverRenderer* ren = getAGGRenderer(image);
  symbol = symbolset->symbol[style->symbol];

  initLabel(&label);
  rot = (symbol->gap <= 0);
  label.type = MS_TRUETYPE;
  label.font = symbol->font;
  // -- rescaling symbol and gap 
  if(style->size == -1) {
      size = msSymbolGetDefaultSize( symbol );
  }
  else
      size = style->size;
  if(size*scalefactor > style->maxsize) scalefactor = (float)style->maxsize/(float)size;
  if(size*scalefactor < style->minsize) scalefactor = (float)style->minsize/(float)size;
  gap = MS_ABS(symbol->gap)* (int) scalefactor;
  label.size = (int) (size * scalefactor);
  // label.minsize = style->minsize; 
  // label.maxsize = style->maxsize; 

  label.color = style->color;
  label.outlinecolor = style->outlinecolor;
  
  char * font = msLookupHashTable(&(symbolset->fontset->fonts), label.font);
    if(!font) {
        msSetError(MS_TTFERR, "Requested font (%s) not found.", "msDrawTextAGG()", label.font);
        return;
    }
  if(ren->getLabelSize(symbol->character, font, label.size, &label_rect,NULL) != MS_SUCCESS)
    return;

  label_width = (int) label_rect.maxx - (int) label_rect.minx;
  agg::rgba8 agg_color,agg_ocolor;
  agg_color=getAGGColor(&label.color,100);
  agg_ocolor=getAGGColor(&label.outlinecolor,100);
  for(i=0; i<p->numlines; i++) {
    current_length = 1+label_width/2.0; // initial padding for each line
    
    for(j=1;j<p->line[i].numpoints;j++) {
      length = sqrt((pow((p->line[i].point[j].x - p->line[i].point[j-1].x),2) + pow((p->line[i].point[j].y - p->line[i].point[j-1].y),2)));
      if(length==0)continue;
      rx = (p->line[i].point[j].x - p->line[i].point[j-1].x)/length;
      ry = (p->line[i].point[j].y - p->line[i].point[j-1].y)/length;  
      theta = asin(ry);
      position = symbol->position;
      if(rx < 0) {
          if(rot){
              theta += MS_PI;
              if((position == MS_UR)||(position == MS_UL)) position = MS_LC;
              if((position == MS_LR)||(position == MS_LL)) position = MS_UC;
          }else{
              if(position == MS_UC) position = MS_LC;
              else if(position == MS_LC) position = MS_UC;
          }
      }
      else theta = -theta;
      if((position == MS_UR)||(position == MS_UL)) position = MS_UC;
      if((position == MS_LR)||(position == MS_LL)) position = MS_LC;
      label.angle = style->angle ;
      if(rot)
          label.angle+=theta*MS_RAD_TO_DEG;

      in = 0;
      while(current_length <= length) {
        point.x = p->line[i].point[j-1].x + current_length*rx;
        point.y = p->line[i].point[j-1].y + current_length*ry;
        
        label_point = get_metrics(&point, position, label_rect, 0, 0, label.angle, 0, NULL);
        ren->renderGlyphs(label_point.x,label_point.y,agg_color,agg_ocolor,label.size,
                          font,symbol->character,label.angle*MS_DEG_TO_RAD,
                          AGG_NO_COLOR,0,0,MS_NINT(style->width));
        current_length += label_width + gap;
        in = 1;
      }

      if(in){
        current_length -= length + label_width/2.0;
      } else current_length -= length;
    }
  }
}

// ------------------------------------------------------------------------------- 
//       Draw a line symbol of the specified size and color                        
// ------------------------------------------------------------------------------- 
void msDrawLineSymbolAGG(symbolSetObj *symbolset, imageObj *image, shapeObj *p, styleObj *style, double scalefactor)
{
    double width;
    double nwidth, size;
    symbolObj *symbol;
    AGGMapserverRenderer* ren = getAGGRenderer(image);
    shapeObj *offsetLine = NULL;
    
    if(style->symbol >= symbolset->numsymbols || style->symbol < 0) return; /* no such symbol, 0 is OK   */
    symbol = symbolset->symbol[style->symbol];

    if(p->numlines==0)
        return;

    if(style->size == -1)
        size = msSymbolGetDefaultSize(symbolset->symbol[style->symbol]);
    else
        size = style->size;

    size = (size*scalefactor);
    size = MS_MAX(size, style->minsize);
    size = MS_MIN(size, style->maxsize);

    width = (style->width*scalefactor);
    width = MS_MAX(width, style->minwidth);
    width = MS_MIN(width, style->maxwidth);
    
    agg::rgba8 agg_color,agg_ocolor,agg_bcolor;
    agg_color=getAGGColor(&style->color,style->opacity);
    agg_ocolor=getAGGColor(&style->outlinecolor,style->opacity);
    agg_bcolor=getAGGColor(&style->backgroundcolor,style->opacity);
    agg::rgba8 *color;
    if(agg_color.a) {
        color = &(agg_color);
    } else if(agg_ocolor.a) {
        color = &(agg_ocolor);// try the outline color, polygons drawing thick outlines often do this
    } else {
        if(symbol->type != MS_SYMBOL_PIXMAP)
            //all symbols except pixmap symbols must specify a color
            return;
    }
    
    //transform the shapeobj to something AGG understands
    
    line_adaptor *lines;
    if(style->offsety==-99) {
        offsetLine = msOffsetPolyline(p,style->offsetx,style->offsety);
    }
    if(offsetLine!=NULL) {
        lines=new line_adaptor(offsetLine);
    } else {
        if(style->offsetx!=0 || style->offsety!=0) {
            lines=new offset_line_adaptor(p,style->offsetx,style->offsety);
        } else {
            lines=new line_adaptor(p);
        }
    }
    
    // treat the easy case
    // NOTE/TODO:  symbols of type ELLIPSE are included here, as using those with a SIZE param was
    // standard practice for drawing thick lines. This should probably be removed some day
    // for consistency
    if(style->symbol == 0 || (symbol->type==MS_SYMBOL_SIMPLE) 
            || (symbol->type == MS_SYMBOL_ELLIPSE && symbol->gap==0)) {
         // for setting line width use SIZE if symbol is of type ELLIPSE, 
         //otherwise use WIDTH (cf. documentation)
        if(symbol->type == MS_SYMBOL_ELLIPSE)
            nwidth=(style->size==-1)?width:size;
        else
            nwidth=width;
        //read caps and joins from symbol
        enum agg::line_cap_e lc=agg::round_cap;
        enum agg::line_join_e lj=agg::round_join;
        if(symbol->type==MS_SYMBOL_SIMPLE) {
            switch(symbol->linejoin) {
            case MS_CJC_ROUND:
                lj=agg::round_join;
                break;
            case MS_CJC_MITER:
                lj=agg::miter_join;
                break;
            case MS_CJC_BEVEL:
                lj=agg::bevel_join;
                break;
            }
            switch(symbol->linecap) {
            case MS_CJC_BUTT:
                lc=agg::butt_cap;
                break;
            case MS_CJC_ROUND:
                lc=agg::round_cap;
                break;
            case MS_CJC_SQUARE:
                lc=agg::square_cap;
                break;
            }
        }
        ren->renderPolyline(*lines,*color,nwidth,symbol->patternlength,symbol->pattern,lc,lj);
    }
    else if(symbol->type==MS_SYMBOL_TRUETYPE) {
        //specific function that treats truetype symbols
        msImageTruetypePolylineAGG(symbolset,image,p,style,scalefactor);
    }
    else if(symbol->gap!=0) {
        //special function that treats any other symbol used as a marker, not a brush
        drawPolylineMarkers(image,p,symbolset,style,size);
    }
    else { // from here on, the symbol is treated as a brush for the line
        switch(symbol->type) {
        case MS_SYMBOL_PIXMAP: {
             GDpixfmt img_pixf = loadSymbolPixmap(symbol);
            ren->renderPathPixmapBGRA(*lines,img_pixf);
        }
        break;
        case MS_SYMBOL_VECTOR: {
            double d = size/symbol->sizey; // compute the scaling factor (d) on the unrotated symbol
            double angle = style->angle;
            char bRotated=MS_FALSE;
            if (angle != 0.0 && angle != 360.0) {
                bRotated = MS_TRUE;
                symbol = msRotateSymbol(symbol, style->angle);
            }

            int pw =(int) ceil(symbol->sizex*d);    
            int ph =(int) ceil(symbol->sizey*d);
            
            
            if((pw <= 1) && (ph <= 1)) { // No sense using a tile, just draw a simple line
                ren->renderPolyline(*lines,*color,size,0,NULL);
                break;
            }
            agg::path_storage path = imageVectorSymbolAGG(symbol,d);
            
            //more or less ugly way of getting the symbol to draw entirely when stroked 
            //with a thick line. as we're stroking a line with the vector
            //brush, we don't want to add a white space horizontally to avoid gaps, but we
            //do add some space vertically so the thick lines of the vector symbol appear.
            ph+=MS_NINT(style->width);
            path.transform(agg::trans_affine_translation(0,((double)style->width)/2.0));
            
            if(symbol->filled) {
                //brush with a filled vector symbol, with an optional background
                ren->renderPolylineVectorSymbol(*lines,path,pw,ph,*color,agg_bcolor);
            } else  {
                //brush with a stroked vector symbol (to get width), 
                //with an optional background
                agg::conv_stroke <agg::path_storage > stroke(path);
                stroke.width(style->width);            
                strokeFromSymbol(stroke,symbol);             
                ren->renderPolylineVectorSymbol(*lines,stroke,pw,ph,*color,agg_bcolor);
            }
            if(bRotated) { /* free the rotated symbol */
                msFreeSymbol(symbol);
                msFree(symbol);
            }
        }
        break;
        case MS_SYMBOL_CARTOLINE:
            msSetError(MS_AGGERR, "Cartoline drawing is deprecated with AGG", "msDrawLineSymbolAGG()");
        default:
            //we don't treat hatches on lines
            break;
        }
    }
    if(offsetLine!=NULL) {
        msFreeShape(offsetLine);
        free(offsetLine);
    }
    delete lines;
    return;
}

// ------------------------------------------------------------------------------- 
//       Draw a shade symbol of the specified size and color                       
// ------------------------------------------------------------------------------- 
void msDrawShadeSymbolAGG(symbolSetObj *symbolset, imageObj *image, shapeObj *p, styleObj *style, double scalefactor)
{
    if(style->symbol >= symbolset->numsymbols || style->symbol < 0) return; // no such symbol, 0 is OK   
    if(p->numlines==0) return;
    
    symbolObj *symbol = symbolset->symbol[style->symbol];;
    if(!MS_VALID_COLOR(style->color) && 
            MS_VALID_COLOR(style->outlinecolor) && 
            symbol->type != MS_SYMBOL_PIXMAP) { 
        // use msDrawLineSymbolAGG if we only have an outline color and we're not using a pixmap symbol
        msDrawLineSymbolAGG(symbolset, image, p, style, scalefactor);
        return;
    }

    double ox,oy,size, angle_radians,width;
    shapeObj *offsetPolygon=NULL;

    if(!p) return;
    if(p->numlines <= 0) return;

    if(style->size == -1) {
        size = msSymbolGetDefaultSize(symbolset->symbol[style->symbol]);
        size = size*scalefactor;
    } else
        size = style->size*scalefactor;
    size = MS_MAX(size, style->minsize);
    size = MS_MIN(size, style->maxsize);

    width = style->width*scalefactor;
    width = MS_MAX(width, style->minwidth);
    width = MS_MIN(width, style->maxwidth);

    angle_radians = style->angle*MS_DEG_TO_RAD;

    ox = style->offsetx*scalefactor; // should we scale the offsets?
    oy = style->offsety*scalefactor;

    if(!MS_VALID_COLOR(style->color) && symbol->type!=MS_SYMBOL_PIXMAP)
        return; // nothing to do (colors are not required with PIXMAP symbols)
    if(size < 1) return; // size too small 

    AGGMapserverRenderer* ren = getAGGRenderer(image);
    polygon_adaptor *polygons;
    if(style->offsety==-99) {
        offsetPolygon = msOffsetPolyline(p,style->offsetx,style->offsety);
    }
    if(offsetPolygon!=NULL) {
        polygons=new polygon_adaptor(offsetPolygon);
    } else {
        if(style->offsetx!=0 || style->offsety!=0) {
            polygons = new offset_polygon_adaptor(p,style->offsetx,style->offsety);
        } else {
            polygons = new polygon_adaptor(p);
        }
    }
    agg::rgba8 agg_color,agg_ocolor,agg_bcolor;
    agg_color=getAGGColor(&style->color,style->opacity);
    agg_ocolor=getAGGColor(&style->outlinecolor,style->opacity);
    agg_bcolor=getAGGColor(&style->backgroundcolor,style->opacity);
    
    if(style->symbol == 0 || symbol->type==MS_SYMBOL_SIMPLE) {
        // simply draw a solid fill and outline of the specified colors
        if(MS_VALID_COLOR(style->outlinecolor))
            ren->renderPathSolid(*polygons,agg_color,agg_ocolor,style->width);
            //use outline width without scalefactor applied
        else
            //draw a one pixel outline of the same color as the fill to avoid a faint outline
            ren->renderPathSolid(*polygons,agg_color,agg_color,1); 
    }
    else {
        switch(symbol->type) {
        case(MS_SYMBOL_HATCH): {
            
            msComputeBounds(p);
            int pw=MS_NINT(p->bounds.maxx-p->bounds.minx)+1;
            int ph=MS_NINT(p->bounds.maxy-p->bounds.miny)+1;
            agg::path_storage hatch;
            
            //optional backgroundcolor before drawing the symbol
            ren->renderPathSolid(*polygons,agg_bcolor,AGG_NO_COLOR,1);
            
            //create a rectangular hatch of size pw,ph starting at 0,0
            //the created hatch is of the size of the shape's bounding box
            hatch = createHatchAGG(pw,ph,style->angle,size);
            
            //translate the hatch so it overlaps the current shape
            hatch.transform(agg::trans_affine_translation(p->bounds.minx, p->bounds.miny));
            
            
            
            if(symbol->patternlength>1) {
                //dash the hatch and render it clipped by the shape
                agg::conv_dash<agg::path_storage > dash(hatch);
                agg::conv_stroke<agg::conv_dash<agg::path_storage> > stroke_dash(dash);  
                for (int i=0; i<symbol->patternlength; i+=2) {
                    if (i < symbol->patternlength-1)
                        dash.add_dash(symbol->pattern[i], symbol->pattern[i+1]);
                }
                stroke_dash.width(style->width);
                ren->renderPathSolidClipped(stroke_dash,*polygons,agg_color);
            } else {
                //render the hatch clipped by the shape
                agg::conv_stroke <agg::path_storage > stroke(hatch);
                stroke.width(style->width);
                ren->renderPathSolidClipped(stroke,*polygons,agg_color);
            }
            
            //render the optional outline
            ren->renderPathSolid(*polygons,AGG_NO_COLOR,agg_ocolor,1);
        }
        break;
        case(MS_SYMBOL_VECTOR): {
            double d = size/symbol->sizey; // compute the scaling factor (d) on the unrotated symbol
            char bRotated=MS_FALSE;
            if (style->angle != 0.0 && style->angle != 360.0) {
                bRotated = MS_TRUE;
                symbol = msRotateSymbol(symbol, style->angle);
            }

            int pw = MS_NINT(symbol->sizex*d);    
            int ph = MS_NINT(symbol->sizey*d);
            if((pw <= 1) && (ph <= 1)) {
                //use a solid fill if the symbol is too small
                if(MS_VALID_COLOR(style->outlinecolor))
                    ren->renderPathSolid(*polygons,agg_color,agg_ocolor,width);
                else
                    //render a one pixel outline of the same color as the fill to prevent a
                    //faint due to antialiasing with contiguous polygons
                    ren->renderPathSolid(*polygons,agg_color,agg_color,1);
                break;
            }
            agg::path_storage path = imageVectorSymbolAGG(symbol,d);
            if(symbol->gap>0) {
                //adjust the size of the tile if a gap is specified
                double gap = symbol->gap*d;
                pw+=MS_NINT(gap);
                ph+=MS_NINT(gap);
                //center the symbol on the adjusted tile
                path.transform(agg::trans_affine_translation(gap/2.,gap/2.));
            }
            if(symbol->filled) {
                ren->renderPathTiled(*polygons,path,pw,ph,agg_color,agg_bcolor);
            } else  {
                agg::conv_stroke <agg::path_storage > stroke(path);
                stroke.width(style->width);
                //apply symbol caps and joins
                strokeFromSymbol(stroke,symbol);             
                ren->renderPathTiled(*polygons,stroke,pw,ph,agg_color,agg_bcolor);
            }
            
            //draw an outline on the shape
            //TODO: change this as outlinecolor should be used for the symbol, not the shape
            agg::rgba8 *oc=NULL;
            if(agg_ocolor.a)
                oc=&agg_ocolor;
            else if(agg_bcolor.a)
                oc=&agg_bcolor; /*avoid faint outline*/
            if(oc!=NULL)
                ren->renderPathSolid(*polygons,AGG_NO_COLOR,*oc,1);
            
            if(bRotated) { // free the rotated symbol
                msFreeSymbol(symbol);
                msFree(symbol);
            }
        }
        break;
        case MS_SYMBOL_PIXMAP: {
            //TODO: rotate and scale image before tiling
            GDpixfmt img_pixf = loadSymbolPixmap(symbol);
            ren->renderPathSolid(*polygons,agg_bcolor,agg_bcolor,1);
            ren->renderPathTiledPixmapBGRA(*polygons,img_pixf);
            ren->renderPathSolid(*polygons,AGG_NO_COLOR,agg_ocolor,style->width);
        }
        break;
        case MS_SYMBOL_ELLIPSE: {
            double d = size/symbol->sizey; /* size ~ height in pixels */
            int pw = MS_NINT(symbol->sizex*d);
            int ph = MS_NINT(symbol->sizey*d);
            if((ph <= 1) && (pw <= 1)) { /* No sense using a tile, just fill solid */
                if(MS_VALID_COLOR(style->outlinecolor))
                    ren->renderPathSolid(*polygons,agg_color,agg_ocolor,style->width);
                else
                    ren->renderPathSolid(*polygons,agg_color,agg_color,1);
            }
            else {
                agg::path_storage path;
                agg::arc ellipse ( pw/2.,ph/2.,
                        d*symbol->points[0].x/2.,d*symbol->points[0].y/2.,
                        0,MS_2PI,true );
                ellipse.approximation_scale(1);
                path.concat_path(ellipse);
                if(symbol->gap>0) {
                    double gap = symbol->gap*d;
                    pw+=MS_NINT(gap);
                    ph+=MS_NINT(gap);
                    path.transform(agg::trans_affine_translation(gap/2.,gap/2.));
                }
                ren->renderPathTiled(*polygons,ellipse,pw,ph,
                        agg_color,agg_bcolor);
                
                //draw an outline on the shape
                //TODO: change this as outlinecolor should be used for the symbol, not the shape
                agg::rgba8 *oc=NULL;
                if(agg_ocolor.a)
                    oc=&agg_ocolor;
                else if(agg_bcolor.a)
                    oc=&agg_bcolor;
                if(oc!=NULL)
                    ren->renderPathSolid(*polygons,AGG_NO_COLOR,*oc,1);
            }
        }
        break;
        case MS_SYMBOL_TRUETYPE: {
            char *font = msLookupHashTable(&(symbolset->fontset->fonts), symbol->font);
            if(!font)
                break;
            double gap=(symbol->gap>0)?symbol->gap*size:0;
            ren->renderPathTruetypeTiled(*polygons,font,(unsigned int)((unsigned char)symbol->character[0]),size,
                    gap,agg_color,agg_bcolor,agg_ocolor);
            //if a background was specified, draw an outline of the color
            //to avoid faint outlines in contiguous polygons
            ren->renderPathSolid(*polygons,AGG_NO_COLOR,agg_bcolor,1);
        }
        break;
        case MS_SYMBOL_CARTOLINE:
            msSetError(MS_AGGERR, "Cartoline drawing is deprecated with AGG", "msDrawShadeSymbolAGG()");
            break;
        default:
        break;
        }
    }
    if(offsetPolygon!=NULL) {
        msFreeShape(offsetPolygon);
        free(offsetPolygon);
    }
    delete polygons;
    
    return;
}

// ---------------------------------------------------------------------------
// Simply draws a label based on the label point and the supplied label object.
// -----------------------------------------------------------------------------
int msDrawTextAGG(imageObj* image, pointObj labelPnt, char *string, 
        labelObj *label, fontSetObj *fontset, double scalefactor)
{
    double x, y;
    AGGMapserverRenderer* ren = getAGGRenderer(image);
    if(!string) return(0); // not errors, just don't want to do anything
    if(strlen(string) == 0) return(0);

    x = labelPnt.x;
    y = labelPnt.y;
    agg::rgba8 agg_color,agg_ocolor,agg_scolor;
    agg_color=getAGGColor(&label->color,100);
    agg_ocolor=getAGGColor(&label->outlinecolor,100);
    agg_scolor=getAGGColor(&label->shadowcolor,100);
    if(label->type == MS_TRUETYPE) {
        char *font=NULL;
        double angle_radians = MS_DEG_TO_RAD*label->angle;
        double size;

        size = label->size*scalefactor;
        size = MS_MAX(size, label->minsize);
        size = MS_MIN(size, label->maxsize);

        if(!fontset) {
            msSetError(MS_TTFERR, "No fontset defined.", "msDrawTextAGG()");
            return(-1);
        }

        if(!label->font) {
            msSetError(MS_TTFERR, "No Trueype font defined.", "msDrawTextAGG()");
            return(-1);
        }

        font = msLookupHashTable(&(fontset->fonts), label->font);
        if(!font) {
            msSetError(MS_TTFERR, "Requested font (%s) not found.", "msDrawTextAGG()", label->font);
            return(-1);
        }
        ren->renderGlyphs(x,y,agg_color,agg_ocolor,size,
                font,string,angle_radians,
                agg_scolor,label->shadowsizex,label->shadowsizey,
                label->outlinewidth);


        return 0;
    } else {
        /*adjust top line*/
        int n=msCountChars(string,'\n');
        glyph_gen glyph(0);
        glyph.font(rasterfonts[label->size]);
        y -= glyph.height()*(n);
        ren->renderRasterGlyphs(x,y,
                agg_color,
                agg_ocolor,
                label->size,
                string);
        return 0;
    }

}

int msGetTruetypeTextBBoxAGG(imageObj *img, char *font, int size, char *string, rectObj *rect, double **advances) {
        AGGMapserverRenderer* ren = getAGGRenderer(img);
        return ren->getLabelSize(string, font, size, rect,advances);
}

int msGetRasterTextBBoxAGG(imageObj *img, int size, char *string, rectObj *rect) {
    char **token=NULL;
    int t, num_tokens, max_token_length=0;
    if ((token = msStringSplit(string, '\n', &(num_tokens))) == NULL)
        return (0);

    for (t=0; t<num_tokens; t++)
        //what's the longest token
        max_token_length = MS_MAX(max_token_length, (int) strlen(token[t]));

    rect->minx = 0;
    rect->miny = -(rasterfont_sizes[size].height * num_tokens);
    rect->maxx = rasterfont_sizes[size].width * max_token_length;
    rect->maxy = 0;

    msFreeCharArray(token, num_tokens);
    return MS_SUCCESS;
}

// ---------------------------------------------------------------------------
// Draw a label curved along a line
// ---------------------------------------------------------------------------
int msDrawTextLineAGG(imageObj *image, char *string, labelObj *label, 
        labelPathObj *labelpath, fontSetObj *fontset, double scalefactor)
{
    double size;
    int i;
    AGGMapserverRenderer* ren = getAGGRenderer(image);
    if (!string) return(0); // do nothing 
    if (strlen(string) == 0) return(0); // do nothing
    agg::rgba8 agg_color,agg_ocolor,agg_scolor;
    agg_color=getAGGColor(&label->color,100);
    agg_ocolor=getAGGColor(&label->outlinecolor,100);
    agg_scolor=getAGGColor(&label->shadowcolor,100);
    
    if(label->type == MS_TRUETYPE) {
        char *font=NULL;
        const char *string_ptr;  /* We use this to walk through 'string'*/
        char s[11]; /* UTF-8 characters can be up to 6 bytes wide, entities 10 (&thetasym;) */

        size = label->size*scalefactor;
        size = MS_MAX(size, label->minsize);
        size = MS_MIN(size, label->maxsize);

        if(!fontset) {
            msSetError(MS_TTFERR, "No fontset defined.", "msDrawTextLineAGG()");
            return(-1);
        }

        if(!label->font) {
            msSetError(MS_TTFERR, "No Trueype font defined.", "msDrawTextLineAGG()");
            return(-1);
        }

        font = msLookupHashTable(&(fontset->fonts), label->font);
        if(!font) {
            msSetError(MS_TTFERR, "Requested font (%s) not found.", "msDrawTextLineAGG()", label->font);
            return(-1);
        }

        /* Iterate over the label line and draw each letter.*/
        string_ptr = string; 

        for (i = 0; i < labelpath->path.numpoints; i++) {
            double x, y;
            double theta;
            
            if (msGetNextGlyph(&string_ptr, s) == -1)
                    break;  /* Premature end of string??? */
            
            theta = labelpath->angles[i];
            x = labelpath->path.point[i].x;
            y = labelpath->path.point[i].y;

            ren->renderGlyphs(x,y,agg_color,agg_ocolor,
                    size,font,s,theta,agg_scolor,
                    label->shadowsizex,label->shadowsizey,
                    label->outlinewidth);
        }      
        return(0);
    }
    else {
         msSetError(MS_TTFERR, "BITMAP font is not supported for curved labels", "msDrawTextLineAGG()");              
         return -1;           
    }

}

// -----------------------------------------------------------------------------------------
// draw a filled pie slice centered on center_x,center_y
// start and end angles are given clockwise in degrees; 0 is horizontal to the right ( -> ) 
// the slice is filled with the styleObj's color and outlinecolor if specified
// the styleObj's width parameter defines the width of the outline if appropriate
// if the style contains an offset (first value used only), the slice will be offset
// along the appropriate radius with respect to the center of the pie 
// -----------------------------------------------------------------------------------------

void msPieSliceAGG ( imageObj *image, styleObj *style, double center_x, double center_y, double radius, double start, double end )
{
    AGGMapserverRenderer* ren = getAGGRenderer(image);

    // offset the center of the slice
    // NOTE: agg angles are anti-trigonometric
    // formula before simplification is (-(start+end)/2)*MS_PI/180 which is direction of offset
    if(style->offsetx>0) {
        center_x+=style->offsetx*cos(((-start-end)*MS_PI/360.));
        center_y-=style->offsetx*sin(((-start-end)*MS_PI/360.));
    }

    //create a path with pie slice
    agg::path_storage path;
    path.remove_all();
    path.move_to ( center_x,center_y );
    //NOTE: agg angles are anti-trigonometric
    agg::arc arc ( center_x,center_y,radius,radius,start*MS_DEG_TO_RAD,end*MS_DEG_TO_RAD,true );
    arc.approximation_scale ( 1 );
    path.concat_path(arc);
    path.line_to ( center_x,center_y );
    path.close_polygon();
    agg::rgba8 agg_color,agg_ocolor;
    agg_color=getAGGColor(&style->color,style->opacity);
    agg_ocolor=getAGGColor(&style->outlinecolor,style->opacity);
        
    if(MS_VALID_COLOR(style->outlinecolor))
        ren->renderPathSolid(path,agg_color,agg_ocolor,(style->width!=-1)?style->width:1);
    else
        ren->renderPathSolid(path,agg_color,agg_color,0.75); //render with same outlinecolor to avoid faint outline
}

// -----------------------------------------------------------------------------------------
// draw a rectangle from point c1_x,c1_y to corner c2_x,c2_y
// processes the styleObj's color and outlinecolor
// styleObj's width defines width of outline
// -----------------------------------------------------------------------------------------
void msFilledRectangleAGG ( imageObj *image, styleObj *style, double c1_x, double c1_y, 
        double c2_x, double c2_y )
{
    AGGMapserverRenderer* ren = getAGGRenderer(image);
    agg::path_storage path;
    path.remove_all();
    path.move_to ( c1_x,c1_y );
    path.line_to ( c2_x,c1_y );
    path.line_to ( c2_x,c2_y );
    path.line_to ( c1_x,c2_y );
    path.close_polygon();
    double width=1;
    if(style->width!=-1)
        width=style->width;
    agg::rgba8 agg_color,agg_ocolor;
    agg_color=getAGGColor(&style->color,style->opacity);
    agg_ocolor=getAGGColor(&style->outlinecolor,style->opacity);
        
    ren->renderPathSolid(path,agg_color,agg_ocolor,width);
}

/* ===========================================================================
   msSaveImageGD

   Save an image to a file named filename, if filename is NULL it goes to
   stdout.  This function wraps msSaveImageGDCtx.  --SG
   ======================================================================== */
int msSaveImageAGG(imageObj* image, char *filename, outputFormatObj *format)
{
    char *pFormatBuffer;
    char cGDFormat[128];
    int   iReturn = 0;
    msAlphaAGG2GD(image);
    pFormatBuffer = format->driver;

    strcpy(cGDFormat, "gd/");
    strcat(cGDFormat, &(format->driver[4]));

    format->driver = &cGDFormat[0];

    iReturn = msSaveImageGD(image->img.gd, filename, format);

    format->driver = pFormatBuffer;

    return iReturn;
}

/* ===========================================================================
   msSaveImageGDCtx

   Save image data through gdIOCtx only.  All mapio conditional compilation
   definitions have been moved up to msSaveImageGD (bug 1047).
   ======================================================================== */
int msSaveImageAGGCtx(imageObj* image, gdIOCtx *ctx, outputFormatObj *format)
{
    char *pFormatBuffer;
    char cGDFormat[128];
    int   iReturn = 0;
    msAlphaAGG2GD(image);
    pFormatBuffer = format->driver;

    strcpy(cGDFormat, "gd/");
    strcat(cGDFormat, &(format->driver[4]));

    format->driver = &cGDFormat[0];

    iReturn = msSaveImageGDCtx(image->img.gd, ctx, format);

    format->driver = pFormatBuffer;

    return iReturn;
}

/* ===========================================================================
   msSaveImageBufferGD

   Save image data to a unsigned char * buffer.  In the future we should try
   to merge this with msSaveImageStreamGD function.

   The returned buffer is owned by the caller. It should be freed with gdFree()
   ======================================================================== */
unsigned char *msSaveImageBufferAGG(imageObj* image, int *size_ptr, outputFormatObj *format)
{
    char *pFormatBuffer;
    char *pszGDFormat = NULL;
    unsigned char *buf = NULL;
    msAlphaAGG2GD(image);
    pFormatBuffer = format->driver;

    pszGDFormat = msStringConcatenate(pszGDFormat,(char*)"gd/");
    pszGDFormat = msStringConcatenate(pszGDFormat, &(format->driver[4]));

    format->driver = pszGDFormat;

    buf = msSaveImageBufferGD(image->img.gd, size_ptr, format);

    format->driver = pFormatBuffer;

    msFree(pszGDFormat);

    return buf;
}

int msDrawLegendIconAGG(mapObj *map, layerObj *lp, classObj *theclass, 
        int width, int height, imageObj *image, int dstX, int dstY)
{
  int i, type;
  shapeObj box, zigzag;
  pointObj marker;
  char szPath[MS_MAXPATHLEN];
  AGGMapserverRenderer* ren = getAGGRenderer(image);
  styleObj outline_style;
  //bool clip = MS_VALID_COLOR(map->legend.outlinecolor); //TODO: enforce this

  /* initialize the box used for polygons and for outlines */
  box.line = (lineObj *)malloc(sizeof(lineObj));
  box.numlines = 1;
  box.line[0].point = (pointObj *)malloc(sizeof(pointObj)*5);
  box.line[0].numpoints = 5;

  box.line[0].point[0].x = dstX;
  box.line[0].point[0].y = dstY;
  box.line[0].point[1].x = dstX + width - 1;
  box.line[0].point[1].y = dstY;
  box.line[0].point[2].x = dstX + width - 1;
  box.line[0].point[2].y = dstY + height - 1;
  box.line[0].point[3].x = dstX;
  box.line[0].point[3].y = dstY + height - 1;
  box.line[0].point[4].x = box.line[0].point[0].x;
  box.line[0].point[4].y = box.line[0].point[0].y;
  box.line[0].numpoints = 5;
    
  /* if the class has a keyimage then load it, scale it and we're done */
  if(theclass->keyimage != NULL) {
      
    imageObj* keyimage = msImageLoadGD(msBuildPath(szPath, map->mappath, theclass->keyimage));
    if(!keyimage) return(MS_FAILURE);
    agg::rendering_buffer thepixmap = gdImg2AGGRB_BGRA(keyimage->img.gd);
    GDpixfmt img_pixf(thepixmap);
    img_pixf.premultiply();
    double scalefactor = (double)width / (double)keyimage->width;
    ren->renderPixmapBGRA(img_pixf,dstX+width/2,dstY+height/2,0,scalefactor);
    delete[](thepixmap.buf());
    /* TO DO: we may want to handle this differently depending on the relative size of the keyimage */
  } else {        
    /* some polygon layers may be better drawn using zigzag if there is no fill */
    type = lp->type;
    if(type == MS_LAYER_POLYGON) {
      type = MS_LAYER_LINE;
      for(i=0; i<theclass->numstyles; i++) {
       if(MS_VALID_COLOR(theclass->styles[i]->color)) { /* there is a fill */
      type = MS_LAYER_POLYGON;
      break;
        }
      }
    }

    /* 
    ** now draw the appropriate color/symbol/size combination 
    */     
    switch(type) {
    case MS_LAYER_ANNOTATION:
      if (theclass->label.size != -1)
      {
        rectObj label_rect;
        labelObj label = theclass->label;
        label.angle = 0;
        if (label.type == MS_TRUETYPE) label.size = height;
        marker.x = dstX + MS_NINT(width / 2.0);
        marker.y = dstY + MS_NINT(height / 2.0);
        if(msGetLabelSize(image, (char*)"Aa", &label, &label_rect, &map->fontset, 1.0, MS_FALSE,NULL) != -1)
        {
          pointObj label_point = get_metrics(&marker, MS_CC, label_rect, 0, 0, label.angle, 0, NULL);
          msDrawTextAGG(image, label_point, (char*)"Aa", &label, &map->fontset, 1.0);
        }
      }
      break;
    case MS_LAYER_POINT:
      marker.x = dstX + MS_NINT(width / 2.0);
      marker.y = dstY + MS_NINT(height / 2.0);

      for(i=0; i<theclass->numstyles; i++)
        msDrawMarkerSymbolAGG(&map->symbolset, image, &marker, theclass->styles[i], lp->scalefactor);          
      break;
    case MS_LAYER_LINE:
      zigzag.line = (lineObj *)malloc(sizeof(lineObj));
      zigzag.numlines = 1;
      zigzag.line[0].point = (pointObj *)malloc(sizeof(pointObj)*4);
      zigzag.line[0].numpoints = 4;

      zigzag.line[0].point[0].x = dstX;
      zigzag.line[0].point[0].y = dstY + height - 1;
      zigzag.line[0].point[1].x = dstX + MS_NINT(width / 3.0) - 1; 
      zigzag.line[0].point[1].y = dstY;
      zigzag.line[0].point[2].x = dstX + MS_NINT(2.0 * width / 3.0) - 1; 
      zigzag.line[0].point[2].y = dstY + height - 1; 
      zigzag.line[0].point[3].x = dstX + width - 1; 
      zigzag.line[0].point[3].y = dstY; 

      for(i=0; i<theclass->numstyles; i++)
        msDrawLineSymbolAGG(&map->symbolset, image, &zigzag, theclass->styles[i], lp->scalefactor); 

      free(zigzag.line[0].point);
      free(zigzag.line);    
      break;
    case MS_LAYER_CIRCLE:
    case MS_LAYER_RASTER:
    case MS_LAYER_CHART:
    case MS_LAYER_POLYGON:
      for(i=0; i<theclass->numstyles; i++)     
        msDrawShadeSymbolAGG(&map->symbolset, image, &box, theclass->styles[i], lp->scalefactor);
      break;
    default:
      return MS_FAILURE;
      break;
    } /* end symbol drawing */
  }   

  /* handle an outline if necessary */
  if(MS_VALID_COLOR(map->legend.outlinecolor)) {
    initStyle(&outline_style);
    outline_style.color = map->legend.outlinecolor;
    msDrawLineSymbolAGG(&map->symbolset, image, &box, &outline_style, 1.0);    
  }

  free(box.line[0].point);
  free(box.line);
  
  return MS_SUCCESS;
}
/*
 ** Free gdImagePtr
 */
void msFreeImageAGG(imageObj *img)
{
    delete (AGGMapserverRenderer*)img->imageextra;
    if( img->img.gd != NULL )
        msFreeImageGD(img->img.gd);
}

void msFreeSymbolCacheAGG(void *buffer) {
    if(buffer!=NULL) {
        agg::rendering_buffer *rb = (agg::rendering_buffer*)buffer;
        delete[] rb->buf();
        delete rb;
    }
}

void msTransformShapeAGG(shapeObj *shape, rectObj extent, double cellsize)
{
    int i,j,k,beforelast; /* loop counters */
    double dx,dy;
    double inv_cs = 1.0 / cellsize; /* invert and multiply much faster */
    if(shape->numlines == 0) return; /* nothing to transform */
    pointObj *point;
    if(shape->type == MS_SHAPE_LINE) {
        /*
         * loop through the shape's lines, and do naive simplification
         * to discard the points that are too close to one another.
         * currently the threshold is to discard points if they fall
         * less than a pixel away from their predecessor.
         * the simplified line is guaranteed to contain at 
         * least its first and last point
         */
        for(i=0; i<shape->numlines; i++) { /* for each part */
            if(shape->line[i].numpoints<2) {
                shape->line[i].numpoints=0;
                continue; /*skip degenerate lines*/
            }
            point=shape->line[i].point;
            /*always keep first point*/
            point[0].x = MS_MAP2IMAGE_X_IC_DBL(point[0].x, extent.minx, inv_cs);
            point[0].y = MS_MAP2IMAGE_Y_IC_DBL(point[0].y, extent.maxy, inv_cs);
            beforelast=shape->line[i].numpoints-1;
            for(j=1,k=1; j < beforelast; j++ ) { /*loop from second point to first-before-last point*/
                point[k].x = MS_MAP2IMAGE_X_IC_DBL(point[j].x, extent.minx, inv_cs);
                point[k].y = MS_MAP2IMAGE_Y_IC_DBL(point[j].y, extent.maxy, inv_cs);
                dx=(point[k].x-point[k-1].x);
                dy=(point[k].y-point[k-1].y);
                if(dx*dx+dy*dy>1)
                    k++;
            }
            /*try to keep last point*/
            point[k].x = MS_MAP2IMAGE_X_IC_DBL(point[j].x, extent.minx, inv_cs);
            point[k].y = MS_MAP2IMAGE_Y_IC_DBL(point[j].y, extent.maxy, inv_cs);
            /*discard last point if equal to the one before it*/
            if(point[k].x!=point[k-1].x || point[k].y!=point[k-1].y) {
                shape->line[i].numpoints=k+1;
            } else {
                shape->line[i].numpoints=k;
            }
        }
    }
    else if(shape->type == MS_SHAPE_POLYGON) {
        /*
         * loop through the shape's lines, and do naive simplification
         * to discard the points that are too close to one another.
         * currently the threshold is to discard points if they fall
         * less than a pixel away from their predecessor.
         * the simplified polygon is guaranteed to contain at 
         * least its first, second and last point
         */
        for(i=0; i<shape->numlines; i++) { /* for each part */
            if(shape->line[i].numpoints<3) {
                shape->line[i].numpoints=0;
                continue; /*skip degenerate lines*/
            }
            point=shape->line[i].point;
            /*always keep first and second point*/
            point[0].x = MS_MAP2IMAGE_X_IC_DBL(point[0].x, extent.minx, inv_cs);
            point[0].y = MS_MAP2IMAGE_Y_IC_DBL(point[0].y, extent.maxy, inv_cs);
            point[1].x = MS_MAP2IMAGE_X_IC_DBL(point[1].x, extent.minx, inv_cs);
            point[1].y = MS_MAP2IMAGE_Y_IC_DBL(point[1].y, extent.maxy, inv_cs);         
            beforelast=shape->line[i].numpoints-1;
            for(j=2,k=2; j < beforelast; j++ ) { /*loop from second point to first-before-last point*/
                point[k].x = MS_MAP2IMAGE_X_IC_DBL(point[j].x, extent.minx, inv_cs);
                point[k].y = MS_MAP2IMAGE_Y_IC_DBL(point[j].y, extent.maxy, inv_cs);
                dx=(point[k].x-point[k-1].x);
                dy=(point[k].y-point[k-1].y);
                if(dx*dx+dy*dy>1)
                    k++;
            }
            /*always keep last point*/
            point[k].x = MS_MAP2IMAGE_X_IC_DBL(point[j].x, extent.minx, inv_cs);
            point[k].y = MS_MAP2IMAGE_Y_IC_DBL(point[j].y, extent.maxy, inv_cs);
            shape->line[i].numpoints=k+1;
        }
    }
    else { /* only for untyped shapes, as point layers don't go through this function */
        for(i=0; i<shape->numlines; i++) {
            point=shape->line[i].point;
            for(j=0;j<shape->line[i].numpoints;j++) {
                point[j].x = MS_MAP2IMAGE_X_IC_DBL(point[j].x, extent.minx, inv_cs);
                point[j].y = MS_MAP2IMAGE_Y_IC_DBL(point[j].y, extent.maxy, inv_cs);
            }
        }
    }
}

/*
 * transform the alpha values of the pixels in im from gd-convention (127 to 0)
 * to agg convention (0 to 255)
 */
void msAlphaGD2AGG(imageObj *im) {
    if(im->buffer_format==MS_RENDER_WITH_AGG) return;
    //msDebug("msAlphaGD2AGG(): switching to AGG alpha on a %dx%d image\n",im->img.gd->sy,im->img.gd->sx);
    int x, y;
    for (y = 0; (y < im->img.gd->sy); y++) {
        for (x = 0; (x < im->img.gd->sx); x++) {
            int c = gdImageTrueColorPixel(im->img.gd, x, y);
            int alpha=((c) & 0x7F000000) >> 24;
            
            if(alpha==127) { //treat the case when the pixel is fully transparent
                gdImageTrueColorPixel(im->img.gd, x, y) = gdTrueColorAlpha(0,0,0,0);
            }
            else if(alpha==0) { //treat the case when the pixel is fully opaque
                gdImageTrueColorPixel(im->img.gd, x, y) = gdTrueColorAlpha(
                        gdTrueColorGetRed(c),
                        gdTrueColorGetGreen(c),
                        gdTrueColorGetBlue(c),
                        255);
            }
            else { //treat semi-opaque pixel
                alpha=255-(alpha>>1);
                double a=alpha/255.;
                gdImageTrueColorPixel(im->img.gd, x, y) = gdTrueColorAlpha(
                        MS_NINT(gdTrueColorGetRed(c)*a),
                        MS_NINT(gdTrueColorGetGreen(c)*a),
                        MS_NINT(gdTrueColorGetBlue(c)*a),
                        alpha);
            }
        }
    }
    im->buffer_format=MS_RENDER_WITH_AGG;
}

/*
 * transform the alpha values of the pixels in im from agg convention (0 to 255)
 * to gd-convention (127 to 0)
 */
void msAlphaAGG2GD(imageObj *im) {
    if(im->buffer_format!=MS_RENDER_WITH_AGG) return;
    //msDebug("msAlphaAGG2GD(): switching to GD alpha on a %dx%d image\n",im->img.gd->sy,im->img.gd->sx);
    int x, y;
    for (y = 0; (y < im->img.gd->sy); y++) {
        for (x = 0; (x < im->img.gd->sx); x++) {
            int c = gdImageTrueColorPixel(im->img.gd, x, y);
            int alpha = ((c) & 0xFF000000) >> 24;
            if(alpha==0) { //treat the case when the pixel is fully transparent
                gdImageTrueColorPixel(im->img.gd, x, y)=gdTrueColorAlpha(0,0,0,127); 
            }
            else if(alpha==255) { //treat the case when the pixel is fully opaque
                gdImageTrueColorPixel(im->img.gd, x, y) = gdTrueColorAlpha(
                        gdTrueColorGetRed(c),
                        gdTrueColorGetGreen(c),
                        gdTrueColorGetBlue(c),
                        0);
            }
            else { //treat semi-opaque pixel
                double a = alpha/255.;
                alpha=127-(alpha/2);
                gdImageTrueColorPixel(im->img.gd, x, y) = gdTrueColorAlpha(
                        MS_NINT(gdTrueColorGetRed(c)/a),
                        MS_NINT(gdTrueColorGetGreen(c)/a),
                        MS_NINT(gdTrueColorGetBlue(c)/a),
                        alpha);
            }
        }
    }
    im->buffer_format=MS_RENDER_WITH_GD;
}

///merge image src over image dst with pct opacity
void msImageCopyMergeAGG (imageObj *dst, imageObj *src, int pct)
{ 
    msAlphaGD2AGG(dst);
    msAlphaGD2AGG(src);
    int x, y;
    int w,h;
    w=dst->width;h=dst->height;
    float factor =((float)pct)/100.;
    for (y = 0; (y < h); y++) {
        for (x = 0; (x < w); x++) {
            agg::int8u *src_p = (agg::int8u*)&(gdImageTrueColorPixel(src->img.gd, x, y));
            if(src_p[gd_color_order::A] == 0) continue;
            //get a pointer to the destination pixel
            agg::int8u *p = (agg::int8u*)&(gdImageTrueColorPixel(dst->img.gd, x, y));

            //blend the src pixel over it.
            //the color channels must also be scaled by the opacity
            //as the blender expects premultiplied colors
            agg::blender_bgra32_pre::blend_pix(p,
                    MS_NINT(src_p[gd_color_order::R]*factor),
                    MS_NINT(src_p[gd_color_order::G]*factor),
                    MS_NINT(src_p[gd_color_order::B]*factor),
                    MS_NINT(src_p[gd_color_order::A]*factor));
        }
    }
}

#endif
