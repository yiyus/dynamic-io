/* See LICENSE file for copyright and license details. */
#define _BSD_SOURCE
#include <ctype.h>
#include <errno.h>
#include <fcntl.h>
#include <locale.h>
#include <signal.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <strings.h>
#include <unistd.h>
#include <sys/wait.h>
#include <X11/keysym.h>
#include <X11/Xlib.h>
#include <X11/Xatom.h>
#include <X11/Xutil.h>

/* macros */
#define CLEANMASK(mask)	(mask & ~(numlockmask | LockMask))
#define VSEND				((multicol && tw > maxw ? tw / maxw : 1) * th / lh)

/* enums */
enum { ColFG, ColBG, ColLast };

/* typedefs */
typedef struct {
	int x, y, w, h;
	unsigned long filter[ColLast];
	unsigned long norm[ColLast];
	unsigned long sel[ColLast];
	unsigned long other[ColLast];
	GC gc;
	struct {
		XFontStruct *xfont;
		XFontSet set;
		int ascent;
		int descent;
		int height;
	} font;
	Window win;
} DC; /* draw context */

typedef struct Item Item;
struct Item {
	Bool played;
	char *text;
	Item *next;		/* traverses all items */
	Item *up, *down;	/* traverses items matching current search pattern */
};

/* forward declarations */
static void additem(char *p);
static void bpress(XButtonEvent * e);
static char *cistrstr(const char *s, const char *sub);
static void cleanup(void);
static void clearlist(void);
static void delitem(Item *it);
static void doexit(void);
static void (*donext)(void);
static void dorandom(void);
static void dosort(void);
static void drawline(const char *text, unsigned long bgcol[ColLast], unsigned long fgcol[ColLast]);
static void drawlist(void);
static void drawout(void);
static void drawtext(const char *text, unsigned int l, unsigned int xoffset);
static void eprint(const char *errstr, ...);
static unsigned long getcolor(const char *colstr);
static Item *getitem(int l);
static unsigned char * getsel(unsigned long offset, unsigned long *len, unsigned long *remain);
static void initfont(const char *fontstr);
static void kpress(XKeyEvent * e);
static void match(void);
static void pastesel(void);
static void play(void);
static void play2(Item *it);
static void pointerdown(int x, int y);
static void pointerup(int x, int y);
static void procev(XEvent ev);
static int readstdin(void);
static void run(void);
static void scroll(int nhs, int nvs);
static void scrollto(Item *it);
static void sendout(void);
static void selorstop(Item *it);
static void setcommon(void);
static void setup(void);
static void seturgent(void);
static void skip(void);
static void stop(void);
static int textnw(const char *text, unsigned int len);
static int textw(const char *text);
static void updatetxt(void);

#include "config.h"

/* variables */
static char *intxt;
static char outtxt[4096];
static char *p = NULL;
static char *playcmd = NULL;
static char *playcmd2 = NULL;
static char searchtxt[4096];
static int common = 0;
static int hscroll, vscroll;
static int maxw = 0;
static int naitems = 0;
static int nitems;
static int screen;
static int wx, wy, ww, wh = 0;
static int lh, tw, th = 0;
static unsigned int numlockmask = 0;
static Bool chlddied = False;
static Bool chording = False;
static Bool clearout = False;
static Bool doing = False;
static Bool exit3 = False;
static Bool follow = False;
static Bool multicol = False;
static Bool markout = False;
static Bool out = False;
static Bool over = False;
static Bool playdelete = False;
static Bool played = False;
static Bool readonly = False;
static Bool removecommon = False;
static Bool running = False;
static Bool scrolling = False;
static Bool urgent = False;
static Display *dpy;
static DC dc;
static Item *allitems = NULL;	/* first of all items */
static Item *item = NULL;	/* first of pattern matching items */
static Item *first = NULL;
static Item *last = NULL;
static Item *lastview = NULL;
static Item *mark = NULL;
static Item *nextpage = NULL;
static Item *sel = NULL;
static Window outwin, root, txtwin, win;
static int (*fstrncmp)(const char *, const char *, size_t n) = strncmp;
static char *(*fstrstr)(const char *, const char *) = strstr;
static pid_t chldpid = -1;
Atom wmdeletemsg;

void
additem(char *p) {
	Item *new;

	if(p &&  !strcmp(p, clr)) {
		free(p);
		clearlist();
		return;
	}
	if((new = (Item *)malloc(sizeof(Item))) == NULL)
		eprint("fatal: could not malloc() %u bytes\n", sizeof(Item));
	new->next = new->up = new->down = NULL;
	new->played = !played;
	new->text = p;
	if(!last || !allitems)
		allitems = new;
	else 
		last->next = new;
	last = new;
	naitems++;
	seturgent();
}

void
bpress(XButtonEvent * e) {
	int l;

	l = (multicol && tw > maxw ? (e->x / maxw) * (th / lh) : 0) + e->y / lh;
	switch(e->button) {
	default:
		return;
		break;
	case Button1:
		if(e->window == win) {
			if(playcmd && CLEANMASK(e->state) & Button3Mask) {
				chording = True;
				if(donext && donext != doexit)
					donext = (donext == &dosort) ? &dorandom : &dosort;
				drawlist();
				break;
			}
			scrolling = True;
			scroll(hscroll, (e->y - 1) * nitems / (wh - 2));
		}
		else if(CLEANMASK(e->state) & Button3Mask) {
			chording = True;
			if(readonly)
				break;
			delitem(getitem(l));
			drawlist();
		} else
			selorstop(getitem(l));
		break;
	case Button2:
		if(e->window == outwin) {
			pastesel();
			break;
		}
		if(e->window == win) {
			scrollto(mark);
			break;
		}
		if(playcmd2) {
			play2(getitem(l));
			break;
		}
		if(getitem(l) != mark)
			mark = getitem(l);
		else
			mark = NULL;
		drawlist();
		break;
	case Button3:
		chording = False;
		break;
	case Button4:
		l = (l == 0) ? 1 : l;
		scroll(hscroll, vscroll - l);
		break;
	case Button5:
		l = (l == 0) ? 1 : l;
		scroll(hscroll, vscroll + l);
		break;
	case 6:
		scroll(hscroll - 1, vscroll);
		break;
	case 7:
		scroll(hscroll + 1, vscroll);
		break;
	}
}

void
chld() {
//	if(wait(NULL) != chldpid)
//		return;
	chlddied = True;
}

char *
cistrstr(const char *s, const char *sub) {
	int c, csub;
	unsigned int len;

	if(!sub)
		return (char *)s;
	if((c = *sub++) != 0) {
		c = tolower(c);
		len = strlen(sub);
		do {
			do {
				if((csub = *s++) == 0)
					return (NULL);
			}
			while(tolower(csub) != c);
		}
		while(strncasecmp(s, sub, len) != 0);
		s--;
	}
	return (char *)s;
}

void
cleanup(void) {
	Item *itm;

	signal(SIGCHLD, SIG_IGN);
	if(chldpid != -1)
		kill(chldpid, SIGTERM);
	while(allitems) {
		itm = allitems->next;
		free(allitems->text);
		free(allitems);
		allitems = itm;
	}
	if(dc.font.set)
		XFreeFontSet(dpy, dc.font.set);
	else
		XFreeFont(dpy, dc.font.xfont);
	XFreeGC(dpy, dc.gc);
	XDestroyWindow(dpy, win);
	XUngrabKeyboard(dpy, CurrentTime);
}

void
clearlist(void) {
	while(allitems)
		delitem(allitems);
	drawlist();
}

void
configwin(int width, int height) {
	ww = width;
	wh = height;
	tw = ww - lh;
	th = (intxt == outtxt && wh > lh + 1) ? wh - lh - 1 : wh;
	XResizeWindow(dpy, txtwin, tw, th);
	if(follow && nextpage == NULL)
		scroll(hscroll, nitems);
	if(intxt == outtxt) {
		XMoveResizeWindow(dpy, outwin, 0, wh > lh + 1 ? th + 1 : 0, ww, lh);
		XMapRaised(dpy, outwin);
	}
	else if(out)
		XUnmapWindow(dpy, outwin);
	scroll(hscroll, vscroll);
	drawlist();
}

void
delitem(Item *it) {
	Item *i;

	if(!it)
		return;
	for(i = allitems; i && i->next != it; i = i->next);
	if(i)
		i->next = it->next;
	if(it == last)
		i = last;
	if(it == item)
		item = it->down;
	if(it->down)
		it->down->up = it->up;
	if(it->up)
		it->up->down = it->down;
	if(it == first)
		first = (it->down) ? it->down : it->up;
	if(first == it->up)
		vscroll--;
	if(it == allitems)
		allitems = it->next;
	nitems--;
	naitems--;
	setcommon();
	match();
	free(it->text);
	free(it);
}

void
doexit(void) {
	running = False;
}

void
dorandom(void) {
	int i, j, r;
	Item *it;

	if(!doing)
		return;
	for(i = 0; i < naitems && !mark; i++) {
		mark = allitems;
		r = (int) ((float)naitems * (rand() / (RAND_MAX + 1.0)));
		for(j = 0; j < r; j++)
			mark = mark->next;
	}
	sel = mark;
	for(i = 0; i < naitems && mark == sel; i++) {
		mark = allitems;
		r = (int) ((float)naitems * (rand() / (RAND_MAX + 1.0)));
		for(j = 0; j < r; j++)
			mark = mark->next;
	}
	it = mark;
	while(mark && mark->played == played) {
		mark = mark->next ? mark->next: allitems;
		if(mark == it)
			played = !played;
	}
	play();
}

void
dosort(void) {
	if(!doing)
		return;
	if(mark)
		sel = mark;
	else if(sel && sel->next)
		sel = sel->next;
	else
		sel = item;
	if(sel == mark)
		mark = NULL;
	play();
}

void
drawline(const char *text, unsigned long bgcol[ColLast], unsigned long fgcol[ColLast]) {
	int i, i0, len, x;
	XRectangle r = { dc.x, dc.y, dc.w, dc.h };

	XSetForeground(dpy, dc.gc, bgcol[ColBG]);
	XFillRectangles(dpy, dc.win, dc.gc, &r, 1);
	if(!text)
		return;
	len = strlen(text);
	XSetForeground(dpy, dc.gc, fgcol[ColFG]);
	for(i = i0 = x = 0; i < len; i++)
		if(text[i] == '\t') {
			drawtext(text + i0, i - i0, x);
			x += (textnw(text + i0, i - i0) / TABWIDTH + 1) * TABWIDTH;
			i0 = i + 1;
		}
	drawtext(text + i0, i - i0, x);
}

void
drawlist(void) {
	int height;
	unsigned long *bg, *fg;
	Item *i;

	XStoreName(dpy, win, sel ? &sel->text[common] : wtitle);

	dc.h = lh;
	dc.x = 0 - hscroll * lh;
	dc.y = 0;
	dc.w = tw - dc.x;
	dc.win = txtwin;
	i = first;
	bg = vscroll % 2 == 1 && normaltbgcolor ? dc.other : dc.norm;
	fg = (!urgent) || lastview ? dc.norm : dc.other;
	do {
		drawline(i ? &i->text[common] : NULL, (i && mark == i) ? dc.sel : bg, (sel == i) ? dc.sel : fg);
		bg = normaltbgcolor && bg == dc.norm ? dc.other : dc.norm;
		if(i) {
			if(urgent && i == lastview && i->next)
				fg = dc.other;
			i = i->down;
		}
		dc.y += lh;
		if(dc.y + dc.h > th) {
			drawline(NULL, dc.norm, dc.norm);
			dc.y += lh;
		}
		if(multicol && i && dc.y > th) {
			dc.x += maxw;
			dc.y = 0;
		}
	}
	while(dc.y < th && (dc.x == 0 || dc.x + maxw <= tw));
	nextpage = i;

	/* print filter */
	dc.w = dc.font.height + textw(searchtxt);
	dc.x = tw - dc.w;
	dc.y = 0;
	if(searchtxt[0])
		drawline(searchtxt[0] ? searchtxt : NULL, dc.filter, dc.filter);

	/* vertical scrollbar */
	XSetForeground(dpy, dc.gc, dc.sel[ColBG]);
	XFillRectangle(dpy, win, dc.gc, 0, 0, lh, th);
	XSetForeground(dpy, dc.gc, donext == &dorandom ? dc.sel[ColFG] : dc.norm[ColBG]);
	if(nitems != 0) {
		height = VSEND * (th - 2) / nitems > 0 ? VSEND * (th - 2) / nitems : 1;
		XFillRectangle(dpy, win, dc.gc, 1, vscroll * (th - 2) / nitems, lh - 2, height);
	}
	else
		XFillRectangle(dpy, win, dc.gc, 1, 1, lh - 2, th - 2);

	drawout();
	XFlush(dpy);
}

void
drawout(void) {
	if(intxt != outtxt)
		return;
	XSetForeground(dpy, dc.gc, dc.sel[ColBG]);
	XFillRectangle(dpy, win, dc.gc, 0, th, ww, 1);
	XSetForeground(dpy, dc.gc, dc.norm[ColBG]);
	XFillRectangle(dpy, outwin, dc.gc, 0, 0, ww, lh);
	dc.h = lh;
	dc.w = dc.font.height / 2 + textnw(outtxt, strlen(outtxt));
	dc.x = dc.w < ww ? 0 : ww - dc.w;
	dc.y = 0;
	dc.win = outwin;
	drawline(outtxt[0] ? outtxt : NULL, dc.norm, dc.sel);
	XSetForeground(dpy, dc.gc, dc.sel[ColFG]);
	XFillRectangle(dpy, outwin, dc.gc, dc.font.height / 2 + textnw(outtxt, strlen(outtxt)), 0, 2, lh);
}

void
drawtext(const char *text, unsigned int l, unsigned int xoffset) {
	int h, y, x;

	h = dc.font.ascent + dc.font.descent;
	y = dc.y + (dc.h / 2) - (h / 2) + dc.font.ascent;
	x = dc.x + (h / 2) + xoffset;
	if(dc.font.set)
		XmbDrawString(dpy, dc.win, dc.font.set, dc.gc, x, y, text, l);
	else
		XDrawString(dpy, dc.win, dc.gc, x, y,  text, l);
}

void
eprint(const char *errstr, ...) {
	va_list ap;

	va_start(ap, errstr);
	vfprintf(stderr, errstr, ap);
	va_end(ap);
	exit(EXIT_FAILURE);
}

unsigned long
getcolor(const char *colstr) {
	Colormap cmap = DefaultColormap(dpy, screen);
	XColor color;

	if(!XAllocNamedColor(dpy, cmap, colstr, &color, &color))
		eprint("error, cannot allocate color '%s'\n", colstr);
	return color.pixel;
}

Item*
getitem(int l) {
	int i;
	Item *it;

	it = first;
	for(i = 0; i < l && it; i++)
		it = it->next;
	return it;
}

static unsigned char *
getsel(unsigned long offset, unsigned long *len, unsigned long *remain) {
	Atom utf8_string;
	Atom xa_clip_string;
	XEvent ev;
	Atom typeret;
	int format;
	unsigned char *data;
	unsigned char *result = NULL;

	utf8_string = XInternAtom(dpy, "UTF8_STRING", False);
	xa_clip_string = XInternAtom(dpy, "_SSELP_STRING", False);
	XConvertSelection(dpy, XA_PRIMARY, utf8_string, xa_clip_string,
			win, CurrentTime);
	XFlush(dpy);
	XNextEvent(dpy, &ev);
	if(ev.type == SelectionNotify && ev.xselection.property != None) {
		XGetWindowProperty(dpy, win, ev.xselection.property, offset, 4096L, False,
				AnyPropertyType, &typeret, &format, len, remain, &data);
		if(*len) {
			result = malloc(sizeof(unsigned char) * *len);
			memcpy(result, data, *len);
		}
		XDeleteProperty(dpy, win, ev.xselection.property);
	}
	return result;
}

void
initfont(const char *fontstr) {
	char *def, **missing;
	int i, n;

	if(!fontstr || fontstr[0] == '\0')
		eprint("error, cannot load font: '%s'\n", fontstr);
	missing = NULL;
	dc.font.set = XCreateFontSet(dpy, fontstr, &missing, &n, &def);
	if(missing)
		XFreeStringList(missing);
	if(dc.font.set) {
		XFontSetExtents *font_extents;
		XFontStruct **xfonts;
		char **font_names;
		dc.font.ascent = dc.font.descent = 0;
		font_extents = XExtentsOfFontSet(dc.font.set);
		n = XFontsOfFontSet(dc.font.set, &xfonts, &font_names);
		for(i = 0, dc.font.ascent = 0, dc.font.descent = 0; i < n; i++) {
			if(dc.font.ascent < (*xfonts)->ascent)
				dc.font.ascent = (*xfonts)->ascent;
			if(dc.font.descent < (*xfonts)->descent)
				dc.font.descent = (*xfonts)->descent;
			xfonts++;
		}
	}
	else {
		if(!(dc.font.xfont = XLoadQueryFont(dpy, fontstr))
		&& !(dc.font.xfont = XLoadQueryFont(dpy, "fixed")))
			eprint("error, cannot load font: '%s'\n", fontstr);
		dc.font.ascent = dc.font.xfont->ascent;
		dc.font.descent = dc.font.xfont->descent;
	}
	dc.font.height = dc.font.ascent + dc.font.descent;
}

void
kpress(XKeyEvent * e) {
	char buf[32];
	int i, l, num;
	unsigned int len;
	KeySym ksym;

	l = e->y / lh;
	len = strlen(intxt);
	buf[0] = 0;
	num = XLookupString(e, buf, sizeof buf, &ksym, 0);
	if(IsKeypadKey(ksym)) {
		if(ksym == XK_KP_Enter)
			ksym = XK_Return;
		else if(ksym >= XK_KP_0 && ksym <= XK_KP_9)
			ksym = (ksym - XK_KP_0) + XK_0;
	}
	if(ksym == XK_Insert) {
		if(out)
			intxt = outtxt;
		configwin(ww, wh);
		return;
	}
	if(IsFunctionKey(ksym) || IsKeypadKey(ksym)
	   || IsMiscFunctionKey(ksym) || IsPFKey(ksym)
	   || IsPrivateKeypadKey(ksym))
		return;
	/* first check if a control mask is omitted */
	if(e->state & ControlMask) {
		switch (ksym) {
		default:	/* ignore other control sequences */
			return;
		case XK_bracketleft:
			ksym = XK_Escape;
			break;
		case XK_h:
		case XK_H:
			ksym = XK_BackSpace;
			break;
		case XK_i:
		case XK_I:
			ksym = XK_Tab;
			break;
		case XK_j:
		case XK_J:
			ksym = XK_Return;
			break;
		case XK_l:
		case XK_L:
			clearlist();
			break;
		case XK_u:
		case XK_U:
			intxt[0] = 0;
			updatetxt();
			return;
		case XK_v:
		case XK_V:
			pastesel();
			return;
		case XK_w:
		case XK_W:
			if(len) {
				i = len - 1;
				while(i >= 0 && intxt[i] == ' ')
					intxt[i--] = 0;
				while(i >= 0 && intxt[i] != ' ')
					intxt[i--] = 0;
				updatetxt();
			}
			return;
		}
	}
	if(CLEANMASK(e->state) & Mod1Mask) {
		switch(ksym) {
		default: return;
		case XK_h:
			ksym = XK_Left;
			break;
		case XK_l:
			ksym = XK_Right;
			break;
		case XK_j:
			ksym = XK_Next;
			break;
		case XK_k:
			ksym = XK_Prior;
			break;
		case XK_g:
			ksym = XK_Home;
			break;
		case XK_G:
			ksym = XK_End;
			break;
		}
	}
	switch(ksym) {
	default:
		if(num && !iscntrl((int) buf[0])) {
			buf[num] = 0;
			if(len > 0)
				strncat(intxt, buf, sizeof intxt);
			else
				strncpy(intxt, buf, sizeof intxt);
			updatetxt();
		}
		break;
	case XK_BackSpace:
		if(len) {
			intxt[--len] = 0;
			updatetxt();
		}
		break;
	case XK_End:
		scroll(hscroll, nitems);
		break;
	case XK_Escape:
		if(intxt == searchtxt && searchtxt[0]) {
			intxt[0] = 0;
			updatetxt();
		}
		else if(doing) {
			doing = False;
			mark = (playcmd ? sel : NULL);
			sel = NULL;
			stop();
		}
		else if(intxt == outtxt) {
			intxt = searchtxt;
			configwin(ww, wh);
		}
		else
			running = False;
		break;
	case XK_Down:
		pointerdown(e->x, e->y);
		break;
	case XK_Home:
		scroll(hscroll, 0);
		break;
	case XK_Left:
		scroll(hscroll - 1, vscroll);
		break;
	case XK_Next:
		scroll(hscroll, vscroll + wh / lh - 1);
		break;
	case XK_Prior:
		scroll(hscroll, vscroll + 1 - wh / lh);
		break;
	case XK_Return:
		if(intxt == outtxt) {
			sendout();
			break;
		}
		if(CLEANMASK(ShiftMask) & CLEANMASK(e->state)) {
			if(playcmd && getitem(l) != mark)
				mark = getitem(l);
			else
				mark = NULL;
			drawlist();
		}
		else
			selorstop(getitem(l));
		break;
	case XK_Right:
		scroll(hscroll + 1, vscroll);
		break;
	case XK_Tab:
		if(intxt == searchtxt && searchtxt[0]) {
			mark = first;
			intxt[0] = 0;
			if(donext == doexit)
				selorstop(first);
			else
				updatetxt();
		}
		else
			skip();
		break;
	case XK_Up:
		pointerup(e->x, e->y);
		break;
	}
}

void
match(void) {
	int w;
	Item *i, *itemend;

	item = itemend = NULL;
	maxw = 0;
	nitems = 0;
	for(i = allitems; i; i = i->next)
		if(fstrstr(i->text, searchtxt)) {
			if(!itemend)
				item = i;
			else
				itemend->down = i;
			i->down = NULL;
			i->up = itemend;
			itemend = i;
			w = textw(&i->text[common]);
			maxw = (w > maxw) ? w : maxw;
			nitems++;
		}
		else if(first == i)
			first = NULL;
	if(!first) {
			first = item;
			hscroll = vscroll = 0;
		}
}

void
pastesel(void) {
	unsigned char *data;
	unsigned long i, offset, len, outlen, remain;

	len = offset = remain = 0;
	do {
		data = getsel(offset, &len, &remain);
		for(i = 0; i < len; i++) {
			outlen = strlen(outtxt);
			if(data[i] == '\n' || outlen == sizeof(outtxt) / sizeof(outtxt[0]))
				sendout();
			else {
				outtxt[outlen] = (char)data[i];
				outtxt[outlen + 1] = 0;
			}
		}
		offset += len;
		free(data);
	}
	while(remain);
	drawlist();
}

void
play(void) {
	char *cmd[3];

	if(!sel)
		return;
	cmd[0] = playcmd;
	cmd[1] = sel->text;
	cmd[2] = NULL;

/*	Not neccesary with the current UI:
	if(chldpid != -1)
		kill(chldpid, SIGKILL);
*/

	if((chldpid = fork()) == 0) {	// TODO: switch to handle -1
		if(dpy)
			close(ConnectionNumber(dpy));
		setsid();
		execvp(cmd[0], cmd);
		fprintf(stderr, "dio: execvp %s %s", cmd[0], cmd[1]);
		perror(" failed");
	}
	if(follow)
		scrollto(sel);
	drawlist();
}

void
play2(Item *it) {
	char *cmd[3];

	if(!it)
		return;
	cmd[0] = playcmd2;
	cmd[1] = it->text;
	cmd[2] = NULL;

	if((chldpid = fork()) == 0) {	// TODO: switch to handle -1
		if(dpy)
			close(ConnectionNumber(dpy));
		setsid();
		execvp(cmd[0], cmd);
		fprintf(stderr, "dio: execvp %s %s", cmd[0], cmd[1]);
		perror(" failed");
	}
}

void
pointerdown(int x, int y) {
	int nx, ny;

	nx = (x < 0 || x > tw) ? 1 : x;
	ny= (y < 0 || y > th) ? 1 : y + lh;
	if(ny > th) {
		scroll(hscroll, vscroll + 1);
		ny = y;
	}
	XWarpPointer(dpy, None, txtwin, 0, 0, 0, 0, nx, ny);
}

void
pointerup(int x, int y) {
	int nx, ny;

	nx = (x < 0 || x > tw) ? 1 : x;
	ny= (y < 0 || y > wh) ? 1 : y - lh;
	if(ny < 0) {
		scroll(hscroll, vscroll - 1);
		ny = y;
	}
	XWarpPointer(dpy, None, txtwin, 0, 0, 0, 0, nx, ny);
}

void
procev(XEvent ev) {
	int hs = hscroll, vs = vscroll;

	/* main event loop */
	switch (ev.type) {
	default:	/* ignore all crap */
		break;
	case ButtonPress:
		bpress(&ev.xbutton);
		break;
	case ButtonRelease:
		if(ev.xbutton.button == Button1)
			scrolling = False;
		if(!chording && ev.xbutton.button == Button3) {
			if(ev.xbutton.window == win)
				scrollto(sel);
			else if(exit3)
				running = False;
			else
				skip();
		}
		break;
	case ClientMessage:		/* window closed */
		if(ev.xclient.data.l[0] == wmdeletemsg) {
			doing = False;
			running = False;
		}
		break;
	case ConfigureNotify:
		if(ev.xconfigure.window == win)
			configwin(ev.xconfigure.width, ev.xconfigure.height);
		break;
	case Expose:
		if(ev.xexpose.count == 0)
			drawlist();
		break;
	case KeyPress:
		if(lastview != last) {
			lastview = last;
			drawlist();
		}
		kpress(&ev.xkey);
		break;
	case MotionNotify:
		if(lastview != last) {
			lastview = last;
			drawlist();
		}
		if(scrolling) {
			if(maxw > tw && ev.xmotion.x > lh)
				hs = (ev.xmotion.x - lh) * (maxw + lh - tw) / (tw -lh) / lh;
			else
				vs = (ev.xmotion.y - 1) * nitems / (th - 2);
			scroll(hs, vs);
		}
		break;
	}
}

int
readstdin(void) {
	char *p2, buf[1024];
	int fl;
	int n = 0;
	unsigned int len;

	fl = fcntl(STDIN_FILENO, F_GETFL, 0);
	while(fgets(buf, sizeof buf, stdin) > 0) {
		fcntl(STDIN_FILENO, F_SETFL, fl|O_NONBLOCK);
		len = strlen(buf);
		if (buf[len - 1] == '\n')
			buf[len - 1] = 0;
		else
			len = 0;
		if(p != NULL) {
			if(!(p2 = malloc(strlen(buf) + strlen(p))))
				eprint("fatal: could not malloc() %u bytes\n", strlen(buf) + strlen(p));
			strncpy(p2, p, strlen(p));
			strncpy(p2 + strlen(p), buf, strlen(buf));
			free(p);
			p = p2;
		}
		else if(!(p = strdup(buf)))
			eprint("fatal: could not strdup() %u bytes\n", strlen(buf));
		if(len > 0) {
			additem(p);
			p = NULL;
			n++;
		}
	}
	fcntl(STDIN_FILENO, F_SETFL, fl);
	return n;
}

void
run(void) {
	Bool pipeopen = False;
	Bool readin = True;
	fd_set rd;
	int xfd;
	XEvent ev;

	signal(SIGCHLD, chld);
	if(ww == 0 || wh == 0)
		readstdin();
	setup();

	if(doing && donext)
		donext();
	else {
		if(follow)
			scroll(hscroll, nitems);
		else
			drawlist();
	}
	drawlist();

	xfd = ConnectionNumber(dpy);
	while(running) {
		FD_ZERO(&rd);
		FD_SET(xfd, &rd);
		if(readin)
			FD_SET(STDIN_FILENO, &rd);
		if(chlddied) {
			if(sel) {
				if(playdelete)
					delitem(sel);
				else
					sel->played = played;
			}
			if(playcmd && donext)
				donext();
			else {
				doing = False;
				XStoreName(dpy, win, wtitle);
				sel = NULL;
			}
			drawlist();
			chlddied = False;
		}
		if(select(xfd + 1, &rd, NULL, NULL, NULL) == -1) {
			if(errno == EINTR)
				continue;
			fprintf(stderr, "select failed\n");
			running = False;
			return;
		}
		if(readin && FD_ISSET(STDIN_FILENO, &rd)) {
			readin = readstdin() > 0;
			if(readin) {
				setcommon();
				match();
				if(follow && nextpage != first)
					scroll(hscroll, nitems);
				drawlist();
				if(donext && doing && !sel && win)
					donext();
				pipeopen = True;
			}
			else if(pipeopen && follow)
				running = False;
		}
		while(XPending(dpy)) {
			XNextEvent(dpy, &ev);
			procev(ev);
		}
	}
}

void
scroll(int nhs, int nvs) {
	int i, hs, vs;

	hs = nhs > (maxw + lh - tw) / lh ? (maxw + lh - tw) / lh : nhs;
	hs = hs < 0 ? 0 : hs;
	vs = (nvs > (nitems - ((multicol && maxw > 0 && tw > maxw) ? tw / maxw : 1) * (th / lh))) ?
		        (nitems - ((multicol && maxw > 0 && tw > maxw) ? tw / maxw : 1) * (th / lh)) : nvs;
	vs = vs < 0 ? 0 : vs;
	if(!first)
		first = item;
	if(hs != hscroll || vs != vscroll) {
		hscroll = hs;
		for(i = 0; first && i < abs(vs - vscroll); i++)
			first = (vs - vscroll > 0) ? first->down : first->up;
		vscroll = vs;
		drawlist();
	}
}

void
scrollto(Item* it) {
	int vs = 0;
	Item *f;

	if(!item || !it)
		return;
	for(f = item; f && f != it; f = f->down)
		vs++;
	if(it == f)
		scroll(hscroll, vs);
}

void
selorstop(Item *it) {
	if(!playcmd)
		return;
	doing = !doing;
	mark = (doing ? mark : sel);
	if(donext && doing && it == mark)
		mark = NULL;
	if(doing) {
		sel = it;
		play();
	}
	else {
		stop();
		sel = NULL;
	}
}

void
sendout(void){
	char *p;

	if(clearout)
		clearlist();
	if(markout) {
		if(!(p = strdup(outtxt)))
			eprint("fatal: could not strdup() %u bytes\n", strlen(outtxt));
		additem(p);
		mark = last;
		setcommon();
		match();
		if(follow && nextpage != first)
			scroll(hscroll, nitems);
	}
	fprintf(stdout, "%s\n", outtxt);
	fflush(stdout);
	outtxt[0] = 0;
	drawlist();
}

void
setcommon(void) {
	Item *i;

	if(!removecommon || !allitems)
		return;
	common = strlen(allitems->text);
	for(i = allitems->next; i && common != 0; i = i->next)
		while(common != 0 && strncmp(allitems->text, i->text, common) != 0)
			common--;
	/* always show something (basename) when there is only one item */
	if(common > 0 && naitems == 1)
		common--;
	while(common != 0 && allitems->text[common - 1] != '/')
		common--;
}

void
setup(void) {
	int i, j;
	XClassHint classhint;
	XModifierKeymap *modmap;
	XSetWindowAttributes wa;

	/* init modifier map */
	modmap = XGetModifierMapping(dpy);
	for(i = 0; i < 8; i++)
		for(j = 0; j < modmap->max_keypermod; j++) {
			if(modmap->modifiermap[i * modmap->max_keypermod + j]
			== XKeysymToKeycode(dpy, XK_Num_Lock))
				numlockmask = (1 << i);
		}
	XFreeModifiermap(modmap);

	/* style */
	dc.norm[ColBG] = getcolor(normbgcolor);
	dc.norm[ColFG] = getcolor(normfgcolor);
	dc.filter[ColBG] = getcolor(filterbgcolor);
	dc.filter[ColFG] = getcolor(filterfgcolor);
	dc.sel[ColBG] = getcolor(selbgcolor);
	dc.sel[ColFG] = getcolor(selfgcolor);
	if(normaltbgcolor)
		dc.other[ColBG] = getcolor(normaltbgcolor);
	dc.other[ColFG] = getcolor(urgentfgcolor);
	initfont(font);

	/* window */
	wa.override_redirect = over;
	wa.background_pixmap = ParentRelative;
	wa.event_mask = ButtonMotionMask | PointerMotionMask | ButtonPressMask |
	ButtonReleaseMask | ExposureMask | KeyPressMask | StructureNotifyMask;
	classhint.res_name = classhint.res_class = (char *)wclass;

	/* window geometry */
	lh = dc.font.height + 2;
	if(ww == 0 || wh == 0) {
		setcommon();
		match();
		ww = (lh + maxw > lh) ? lh + maxw : 2 * lh;
		wh = lh * nitems > DisplayHeight(dpy, screen) ? DisplayHeight(dpy, screen) : lh * nitems;
		wh = (wh == 0) ? lh : wh;
	}

	win = XCreateWindow(dpy, root, wx, wy, ww, wh, 0,
			DefaultDepth(dpy, screen), CopyFromParent,
			DefaultVisual(dpy, screen),
			CWOverrideRedirect | CWBackPixmap | CWEventMask, &wa);
	XSetClassHint(dpy, win, &classhint);

	/* text window */
	txtwin =  XCreateWindow(dpy, win, lh, 0, ww - lh, out && wh > lh ? wh - lh : lh, 0,
			DefaultDepth(dpy, screen), CopyFromParent,
			DefaultVisual(dpy, screen),
			CWBackPixmap | CWEventMask, &wa);

	/* out window */
	if(out)
		outwin =  XCreateWindow(dpy, win, 0, wh > lh ? wh - lh : 0, ww, lh, 0,
				DefaultDepth(dpy, screen), CopyFromParent,
				DefaultVisual(dpy, screen),
				CWBackPixmap | CWEventMask, &wa);

	/* catch delete window events */
	wmdeletemsg = XInternAtom(dpy, "WM_DELETE_WINDOW", False);
	(void) XSetWMProtocols(dpy, win, &wmdeletemsg, 1);

	dc.gc = XCreateGC(dpy, win, 0, 0);
	XSetLineAttributes(dpy, dc.gc, 1, LineSolid, CapButt, JoinMiter);
	if(!dc.font.set)
		XSetFont(dpy, dc.gc, dc.font.xfont->fid);
	intxt = (out ? outtxt : searchtxt);
	outtxt[0] = searchtxt[0] = 0;
	XMapRaised(dpy, win);
	XMapRaised(dpy, txtwin);
	if(out)
		XMapRaised(dpy, outwin);
	XSync(dpy, False);
}

void
seturgent(void) {
	XWMHints hints;

	if(urgent && win) {
		hints.flags = XUrgencyHint;
		XSetWMHints(dpy, win, &hints);
	}
}

void
skip(void) {
	if(!doing && playcmd && donext) {
		doing = True;
		donext();
	}
	else
		stop();
}

void
stop(void) {
	if(chldpid != -1)
		kill(chldpid, SIGTERM);
}

int
textnw(const char *text, unsigned int len) {
	XRectangle r;

	if(dc.font.set) {
		XmbTextExtents(dc.font.set, text, len, NULL, &r);
		return r.width;
	}
	return XTextWidth(dc.font.xfont, text, len);
}

int
textw(const char *text) {
	int i, i0, len, x;

	if(!text)
		return 0;
	len = strlen(text);
	for(i = i0 = x = 0; i < len; i++)
		if(text[i] == '\t') {
			x += (textnw(text + i0, i - i0) / TABWIDTH + 1) * TABWIDTH;
			i0 = i + 1;
		}
	x += textnw(text + i0, i - i0);
	return x + dc.font.height;
}

void
updatetxt(void) {
	if(intxt == searchtxt) {
		match();
		drawlist();
	}
	else
		drawout();
}

int
main(int argc, char *argv[]) {
	unsigned int i;

	/* command line args */
	for(i = 1; i < argc; i++)
		if(!strcmp(argv[i], "-m")) {
			multicol = True;
		}
		else if(!strcmp(argv[i], "-fb")) {
			if(++i < argc) filterbgcolor = argv[i];
		}
		else if(!strcmp(argv[i], "-ff")) {
			if(++i < argc) filterfgcolor = argv[i];
		}
		else if(!strcmp(argv[i], "-nb")) {
			if(++i < argc) normbgcolor = argv[i];
		}
		else if(!strcmp(argv[i], "-nba")) {
			if(++i < argc) normaltbgcolor = argv[i];
		}
		else if(!strcmp(argv[i], "-nf")) {
			if(++i < argc) normfgcolor = argv[i];
		}
		else if(!strcmp(argv[i], "-sb")) {
			if(++i < argc) selbgcolor = argv[i];
		}
		else if(!strcmp(argv[i], "-sf")) {
			if(++i < argc) selfgcolor = argv[i];
		}
		else if(!strcmp(argv[i], "-uf")) {
			if(++i < argc) urgentfgcolor = argv[i];
		}
		else if(!strcmp(argv[i], "-fn")) {
			if(++i < argc) font = argv[i];
		}
		else if(!strcmp(argv[i], "-ar") && !donext) {
			donext = dorandom;
		}
		else if(!strcmp(argv[i], "-as") && !donext) {
			donext = dosort;
		}
		else if(!strcmp(argv[i], "-ax") && !donext) {
			donext = doexit;
		}
		else if(!strcmp(argv[i], "-p") && !playcmd) {
			if(++i < argc) playcmd = argv[i];
		}
		else if(!strcmp(argv[i], "-pd") && !playcmd) {
			playdelete = True;
			if(++i < argc) playcmd = argv[i];
		}
		else if(!strcmp(argv[i], "-p2")) {
			if(++i < argc) playcmd2 = argv[i];
		}
		else if(!strcmp(argv[i], "-c")) {
			if(++i < argc) wclass = argv[i];
		}
		else if(!strcmp(argv[i], "-t")) {
			if(++i < argc) wtitle = argv[i];
		}
		else if(!strcmp(argv[i], "-u")) {
			urgent = True;
		}
		else if(!strcmp(argv[i], "-w") || !strcmp(argv[i], "-wo")) {
			if(!strcmp(argv[i], "-wo"))
				over = True;
			if(++i < argc) wx = atoi(argv[i]);
			if(++i < argc) wy = atoi(argv[i]);
			if(++i < argc) ww = atoi(argv[i]);
			if(++i < argc) wh = atoi(argv[i]);
		}
		else if(!strcmp(argv[i], "-f")) {
			follow = True;
		}
		else if(!strcmp(argv[i], "-i")) {
			fstrncmp = strncasecmp;
			fstrstr = cistrstr;
		}
		else if(!strcmp(argv[i], "-o")) {
			out = True;
		}
		else if(!strcmp(argv[i], "-oc")) {
			clearout = True;
			out = True;
		}
		else if(!strcmp(argv[i], "-om")) {
			markout = True;
			out = True;
		}
		else if(!strcmp(argv[i], "-ocm")) {
			clearout = True;
			markout = True;
			out = True;
		}
		else if(!strcmp(argv[i], "-rc")) {
			removecommon = True;
		}
		else if(!strcmp(argv[i], "-ro")) {
			readonly = True;
		}
		else if(!strcmp(argv[i], "-x")) {
			exit3 = True;
		}
		else if(!strcmp(argv[i], "-v"))
			eprint("dio-"VERSION", © 2008-2009 JGL (yiyus), see LICENSE for details\n");
		else
			eprint("usage: dio [-ar|as|ax] [-f] [-fb,ff,nb,nba,nf,sb,sf,uf <color>] [-fn <font>] [-i]\n"
			       "       [-m] [-rc] [-ro] [-u] [-x] [-o|oc|om|ocm] [-p|pd <cmd>] [-p2 <cmd2>]\n"
				   "       [-c <class>] [-t <title>] [-w|wo <x> <y> <w> <h>] [-v]\n");
	if(!setlocale(LC_CTYPE, "") || !XSupportsLocale())
		fprintf(stderr, "warning: no locale support\n");
	if(!(dpy = XOpenDisplay(0)))
		eprint("dio: cannot open display\n");
	screen = DefaultScreen(dpy);
	root = RootWindow(dpy, screen);

	doing = (playcmd && donext && donext != doexit);
	running = True;
	run();

	cleanup();
	XCloseDisplay(dpy);
	return 0;
}
