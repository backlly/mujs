#include "jsi.h"
#include "jslex.h"
#include "jscompile.h"
#include "jsvalue.h"
#include "jsbuiltin.h"
#include "utf.h"

static void jsB_globalf(js_State *J, const char *name, js_CFunction cfun, int n)
{
	js_newcfunction(J, cfun, name, n);
	js_defglobal(J, name, JS_DONTENUM);
}

void jsB_propf(js_State *J, const char *name, js_CFunction cfun, int n)
{
	const char *pname = strrchr(name, '.');
	pname = pname ? pname + 1 : name;
	js_newcfunction(J, cfun, name, n);
	js_defproperty(J, -2, pname, JS_DONTENUM);
}

void jsB_propn(js_State *J, const char *name, double number)
{
	js_pushnumber(J, number);
	js_defproperty(J, -2, name, JS_READONLY | JS_DONTENUM | JS_DONTCONF);
}

void jsB_props(js_State *J, const char *name, const char *string)
{
	js_pushliteral(J, string);
	js_defproperty(J, -2, name, JS_DONTENUM);
}

static void jsB_parseInt(js_State *J)
{
	const char *s = js_tostring(J, 1);
	int radix = js_isdefined(J, 2) ? js_tointeger(J, 2) : 10;
	double sign = 1;
	double n;
	char *e;

	while (jsY_iswhite(*s) || jsY_isnewline(*s))
		++s;
	if (*s == '-') {
		++s;
		sign = -1;
	} else if (*s == '+') {
		++s;
	}
	if (radix == 0) {
		radix = 10;
		if (s[0] == '0' && (s[1] == 'x' || s[1] == 'X')) {
			s += 2;
			radix = 16;
		}
	} else if (radix < 2 || radix > 36) {
		js_pushnumber(J, NAN);
		return;
	}
	n = strtol(s, &e, radix);
	if (s == e)
		js_pushnumber(J, NAN);
	else
		js_pushnumber(J, n * sign);
}

static void jsB_parseFloat(js_State *J)
{
	const char *s = js_tostring(J, 1);
	char *e;
	double n;

	while (jsY_iswhite(*s) || jsY_isnewline(*s)) ++s;
	if (!strncmp(s, "Infinity", 8))
		js_pushnumber(J, INFINITY);
	else if (!strncmp(s, "+Infinity", 9))
		js_pushnumber(J, INFINITY);
	else if (!strncmp(s, "-Infinity", 9))
		js_pushnumber(J, -INFINITY);
	else {
		n = js_stringtofloat(s, &e);
		if (e == s)
			js_pushnumber(J, NAN);
		else
			js_pushnumber(J, n);
	}
}

static void jsB_isNaN(js_State *J)
{
	double n = js_tonumber(J, 1);
	js_pushboolean(J, isnan(n));
}

static void jsB_isFinite(js_State *J)
{
	double n = js_tonumber(J, 1);
	js_pushboolean(J, isfinite(n));
}

static void Encode(js_State *J, const char *str, const char *unescaped)
{
	js_Buffer *sb = NULL;

	static const char *HEX = "0123456789ABCDEF";

	if (js_try(J)) {
		js_free(J, sb);
		js_throw(J);
	}

	while (*str) {
		int c = (unsigned char) *str++;
		if (strchr(unescaped, c))
			js_putc(J, &sb, c);
		else {
			js_putc(J, &sb, '%');
			js_putc(J, &sb, HEX[(c >> 4) & 0xf]);
			js_putc(J, &sb, HEX[c & 0xf]);
		}
	}
	js_putc(J, &sb, 0);

	js_pushstring(J, sb ? sb->s : "");
	js_endtry(J);
	js_free(J, sb);
}

static void Decode(js_State *J, const char *str, const char *reserved)
{
	js_Buffer *sb = NULL;
	int a, b;

	if (js_try(J)) {
		js_free(J, sb);
		js_throw(J);
	}

	while (*str) {
		int c = (unsigned char) *str++;
		if (c != '%')
			js_putc(J, &sb, c);
		else {
			if (!str[0] || !str[1])
				js_urierror(J, "truncated escape sequence");
			a = *str++;
			b = *str++;
			if (!jsY_ishex(a) || !jsY_ishex(b))
				js_urierror(J, "invalid escape sequence");
			c = jsY_tohex(a) << 4 | jsY_tohex(b);
			if (!strchr(reserved, c))
				js_putc(J, &sb, c);
			else {
				js_putc(J, &sb, '%');
				js_putc(J, &sb, a);
				js_putc(J, &sb, b);
			}
		}
	}
	js_putc(J, &sb, 0);

	js_pushstring(J, sb ? sb->s : "");
	js_endtry(J);
	js_free(J, sb);
}

#define URIRESERVED ";/?:@&=+$,"
#define URIALPHA "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ"
#define URIDIGIT "0123456789"
#define URIMARK "-_.!~*`()"
#define URIUNESCAPED URIALPHA URIDIGIT URIMARK

static void jsB_decodeURI(js_State *J)
{
	Decode(J, js_tostring(J, 1), URIRESERVED "#");
}

static void jsB_decodeURIComponent(js_State *J)
{
	Decode(J, js_tostring(J, 1), "");
}

static void jsB_encodeURI(js_State *J)
{
	Encode(J, js_tostring(J, 1), URIUNESCAPED URIRESERVED "#");
}

static void jsB_encodeURIComponent(js_State *J)
{
	Encode(J, js_tostring(J, 1), URIUNESCAPED);
}

static void jsB_escape(js_State *J) {
    static const char *HEX = "0123456789ABCDEF";
    js_Buffer *buffer = NULL;
    js_Buffer **sb = &buffer;
    const char* s = js_isdefined(J, 1) ? js_tostring(J, 1) : NULL;
    Rune c;
    if(s == NULL) {
        js_pushstring(J, "");
        return;
    }
    while (*s) {
        s += chartorune(&c, s);
        switch (c) {
            case '"': js_puts(J, sb, "\\\""); break;
            case '\\': js_puts(J, sb, "\\\\"); break;
            case '\b': js_puts(J, sb, "\\b"); break;
            case '\f': js_puts(J, sb, "\\f"); break;
            case '\n': js_puts(J, sb, "\\n"); break;
            case '\r': js_puts(J, sb, "\\r"); break;
            case '\t': js_puts(J, sb, "\\t"); break;
            default:
                if (c < ' ' || c > 127) {
                    js_puts(J, sb, "\\u");
                    js_putc(J, sb, HEX[(c>>12)&15]);
                    js_putc(J, sb, HEX[(c>>8)&15]);
                    js_putc(J, sb, HEX[(c>>4)&15]);
                    js_putc(J, sb, HEX[c&15]);
                } else {
                    js_putc(J, sb, c); break;
                }
        }
    }
    if(buffer) {
        js_putc(J, sb, 0);
    }
    js_pushstring(J, buffer ? buffer->s : "");
    js_free(J, buffer);
}

static inline const char* jsB_unescape_next(const char* haystack, int* ret) {
    Rune rune = 0;
    if(haystack && *haystack != '\0') {
        haystack += chartorune(&rune, haystack);
        /* consume CR LF as one unit */
        if (rune == '\r' && *haystack == '\n')
            ++haystack;
        if (jsY_isnewline(rune)) {
            rune = '\n';
        }
    }
    *ret = rune;
    return haystack;
}
static void jsB_unescape(js_State *J) {
    const char* haystack = js_isdefined(J, 1) ? js_tostring(J, 1) : NULL;
    js_Buffer *buffer = NULL;
    js_Buffer **sb = &buffer;
    char tmp[8] = {0};
    int lexchar = 0;
    int x = 0;
    int xLen = 0;
    if(haystack) {
        while (*haystack) {
            haystack = jsB_unescape_next(haystack, &lexchar);
            if(lexchar == '\\') {
                haystack = jsB_unescape_next(haystack, &lexchar);
                switch (lexchar) {
                    case 'u':
                        haystack = jsB_unescape_next(haystack, &lexchar);
                        if (jsY_ishex(lexchar)) { x = (jsY_tohex(lexchar) << 12); } else { js_putc(J, sb, lexchar); break; }
                        haystack = jsB_unescape_next(haystack, &lexchar);
                        if (jsY_ishex(lexchar)) { x |= (jsY_tohex(lexchar) << 8); } else { js_putc(J, sb, lexchar); break; }
                        haystack = jsB_unescape_next(haystack, &lexchar);
                        if (jsY_ishex(lexchar)) { x |= (jsY_tohex(lexchar) << 4); } else { js_putc(J, sb, lexchar); break; }
                        haystack = jsB_unescape_next(haystack, &lexchar);
                        if (jsY_ishex(lexchar)) { x |= (jsY_tohex(lexchar) << 0); } else { js_putc(J, sb, lexchar); break; }
                        if(x > 127) {
                            xLen = runetochar(tmp, (const Rune *)&x);
                            for( x = 0 ; x < xLen; ++x) {
                                js_putc(J, sb, tmp[x]);
                            }
                        } else {
                            js_putc(J, sb, x);
                        }
                        break;
                    case '"': js_putc(J, sb, '"');   break;
                    case '\\': js_putc(J, sb, '\\'); break;
                    case 'b': js_putc(J, sb, '\b');  break;
                    case 'f': js_putc(J, sb, '\f');  break;
                    case 'n': js_putc(J, sb, '\n');  break;
                    case 'r': js_putc(J, sb, '\r');  break;
                    case 't': js_putc(J, sb, '\t');  break;
                    default:
                        js_report(J, "invalid escape sequence");
                        break;
                }
            } else {
                js_putc(J, sb, lexchar);
            }
        }
        if(buffer) {
            js_putc(J, &buffer, 0);
        }
        js_pushstring(J, buffer ? buffer->s : "");
        js_free(J, buffer);
    } else {
        js_pushstring(J, "");
    }
}

void jsB_init(js_State *J)
{
	/* Create the prototype objects here, before the constructors */
	J->Object_prototype = jsV_newobject(J, JS_COBJECT, NULL);
	J->Array_prototype = jsV_newobject(J, JS_CARRAY, J->Object_prototype);
	J->Function_prototype = jsV_newobject(J, JS_CCFUNCTION, J->Object_prototype);
	J->Boolean_prototype = jsV_newobject(J, JS_CBOOLEAN, J->Object_prototype);
	J->Number_prototype = jsV_newobject(J, JS_CNUMBER, J->Object_prototype);
	J->String_prototype = jsV_newobject(J, JS_CSTRING, J->Object_prototype);
	J->RegExp_prototype = jsV_newobject(J, JS_COBJECT, J->Object_prototype);
	J->Date_prototype = jsV_newobject(J, JS_CDATE, J->Object_prototype);

	/* All the native error types */
	J->Error_prototype = jsV_newobject(J, JS_CERROR, J->Object_prototype);
	J->EvalError_prototype = jsV_newobject(J, JS_CERROR, J->Error_prototype);
	J->RangeError_prototype = jsV_newobject(J, JS_CERROR, J->Error_prototype);
	J->ReferenceError_prototype = jsV_newobject(J, JS_CERROR, J->Error_prototype);
	J->SyntaxError_prototype = jsV_newobject(J, JS_CERROR, J->Error_prototype);
	J->TypeError_prototype = jsV_newobject(J, JS_CERROR, J->Error_prototype);
	J->URIError_prototype = jsV_newobject(J, JS_CERROR, J->Error_prototype);

	/* Create the constructors and fill out the prototype objects */
	jsB_initobject(J);
	jsB_initarray(J);
	jsB_initfunction(J);
	jsB_initboolean(J);
	jsB_initnumber(J);
	jsB_initstring(J);
	jsB_initregexp(J);
	jsB_initdate(J);
	jsB_initerror(J);
	jsB_initmath(J);
	jsB_initjson(J);

	/* Initialize the global object */
	js_pushnumber(J, NAN);
	js_defglobal(J, "NaN", JS_READONLY | JS_DONTENUM | JS_DONTCONF);

	js_pushnumber(J, INFINITY);
	js_defglobal(J, "Infinity", JS_READONLY | JS_DONTENUM | JS_DONTCONF);

	js_pushundefined(J);
	js_defglobal(J, "undefined", JS_READONLY | JS_DONTENUM | JS_DONTCONF);

	jsB_globalf(J, "parseInt", jsB_parseInt, 1);
	jsB_globalf(J, "parseFloat", jsB_parseFloat, 1);
	jsB_globalf(J, "isNaN", jsB_isNaN, 1);
	jsB_globalf(J, "isFinite", jsB_isFinite, 1);

	jsB_globalf(J, "decodeURI", jsB_decodeURI, 1);
	jsB_globalf(J, "decodeURIComponent", jsB_decodeURIComponent, 1);
	jsB_globalf(J, "encodeURI", jsB_encodeURI, 1);
	jsB_globalf(J, "encodeURIComponent", jsB_encodeURIComponent, 1);
    // 用 Unicode 字符 \u00xx 和 \uxxxx 这样的字符序列进行解码
    jsB_globalf(J, "escape", jsB_escape, 1);
    // 对通过 escape() 编码的字符串进行解码
    jsB_globalf(J, "unescape", jsB_unescape, 1);
}
