#include "js.h"
#include "js-ast.h"

js_Ast *jsP_newnode(js_State *J, int type, js_Ast *a, js_Ast *b, js_Ast *c, js_Ast *d)
{
	js_Ast *node = malloc(sizeof(js_Ast));

	node->type = type;
	node->a = a;
	node->b = b;
	node->c = c;
	node->d = d;
	node->n = 0;
	node->s = NULL;

	return node;
}

js_Ast *jsP_newsnode(js_State *J, int type, const char *s)
{
	js_Ast *node = jsP_newnode(J, type, 0, 0, 0, 0);
	node->s = js_intern(J, s);
	return node;
}

js_Ast *jsP_newnnode(js_State *J, int type, double n)
{
	js_Ast *node = jsP_newnode(J, type, 0, 0, 0, 0);
	node->n = n;
	return node;
}

static const char *strast(int type)
{
	switch (type) {
	case AST_LIST: return "LIST";
	case AST_IDENTIFIER: return "IDENTIFIER";
	case AST_NUMBER: return "NUMBER";
	case AST_STRING: return "STRING";
	case AST_REGEXP: return "REGEXP";
	case EXP_NULL: return "NULL";
	case EXP_TRUE: return "TRUE";
	case EXP_FALSE: return "FALSE";
	case EXP_THIS: return "THIS";
	case EXP_ARRAY: return "ARRAY";
	case EXP_OBJECT: return "OBJECT";
	case EXP_PROP_VAL: return "PROP_VAL";
	case EXP_PROP_GET: return "PROP_GET";
	case EXP_PROP_SET: return "PROP_SET";
	case EXP_INDEX: return "EXP_INDEX";
	case EXP_MEMBER: return "EXP_MEMBER";
	case EXP_NEW: return "new";
	case EXP_CALL: return "EXP_CALL";
	case EXP_FUNC: return "EXP_FUNC";
	case EXP_COND: return "?:";
	case EXP_COMMA: return ",";
	case EXP_DELETE: return "delete";
	case EXP_VOID: return "void";
	case EXP_TYPEOF: return "typeof";
	case EXP_PREINC: return "PRE++";
	case EXP_PREDEC: return "PRE--";
	case EXP_POSTINC: return "POST++";
	case EXP_POSTDEC: return "POST--";
	case EXP_POS: return "+";
	case EXP_NEG: return "-";
	case EXP_BITNOT: return "~";
	case EXP_LOGNOT: return "!";
	case EXP_LOGOR: return "||";
	case EXP_LOGAND: return "&&";
	case EXP_BITOR: return "|";
	case EXP_BITXOR: return "^";
	case EXP_BITAND: return "&";
	case EXP_EQ: return "==";
	case EXP_NE: return "!=";
	case EXP_EQ3: return "===";
	case EXP_NE3: return "!==";
	case EXP_LT: return "<";
	case EXP_GT: return ">";
	case EXP_LE: return "<=";
	case EXP_GE: return ">=";
	case EXP_INSTANCEOF: return "instanceof";
	case EXP_IN: return "in";
	case EXP_SHL: return "<<";
	case EXP_SHR: return ">>";
	case EXP_USHR: return ">>>";
	case EXP_ADD: return "+";
	case EXP_SUB: return "-";
	case EXP_MUL: return "*";
	case EXP_DIV: return "/";
	case EXP_MOD: return "%";
	case EXP_ASS: return "=";
	case EXP_ASS_MUL: return "*=";
	case EXP_ASS_DIV: return "/=";
	case EXP_ASS_MOD: return "%=";
	case EXP_ASS_ADD: return "+=";
	case EXP_ASS_SUB: return "-=";
	case EXP_ASS_SHL: return "<<=";
	case EXP_ASS_SHR: return ">>=";
	case EXP_ASS_USHR: return ">>>=";
	case EXP_ASS_BITAND: return "&=";
	case EXP_ASS_BITXOR: return "^=";
	case EXP_ASS_BITOR: return "|=";
	case STM_NOP: return "STM_NOP";
	case STM_EXP: return "STM_EXP";
	case STM_VAR: return "STM_VAR";
	case STM_IF: return "if";
	case STM_DO: return "do-while";
	case STM_WHILE: return "while";
	case STM_FOR_EXP: return "for_3";
	case STM_FOR_VAR_EXP: return "for_var_3";
	case STM_FOR_IN: return "for_in";
	case STM_FOR_VAR_IN: return "for_var_in";
	case STM_CONTINUE: return "continue";
	case STM_BREAK: return "break";
	case STM_RETURN: return "return";
	case STM_WITH: return "with";
	case STM_SWITCH: return "switch";
	case STM_THROW: return "throw";
	case STM_TRY: return "try";
	case STM_LABEL: return "label";
	case STM_CASE: return "case";
	case STM_DEFAULT: return "default";
	case STM_DEBUGGER: return "debugger";
	default: return "(unknown)";
	}
}

void printast(js_Ast *n)
{
	switch (n->type) {
		case AST_IDENTIFIER: printf("%s", n->s); return;
		case AST_NUMBER: printf("%g", n->n); return;
		case AST_STRING: printf("'%s'", n->s); return;
		case AST_REGEXP: printf("/%s/", n->s); return;
		default: printf("(%s", strast(n->type));
	}
	if (n->a) { putchar(' '); printast(n->a); }
	if (n->b) { putchar(' '); printast(n->b); }
	if (n->c) { putchar(' '); printast(n->c); }
	if (n->d) { putchar(' '); printast(n->d); }
	putchar(')');
}