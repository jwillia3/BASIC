#include <setjmp.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define SYMSZ	16			/* SYMBOL SIZE */
#define PRGSZ	65536			/* PROGRAM SIZE */
#define STKSZ	256			/* STACK SIZE */
#define STRSZ	4096			/* STRING TABLE SIZE */
#define VARS	512			/* VARIABLE COUNT */
#define LOCS	8			/* LOCAL COUNT */

typedef ptrdiff_t	Val;		/* SIGNED INT/POINTER */
typedef int		(*Code)();	/* BYTE-CODE */

enum {	NAME=1,NUMBER,STRING,LP,RP,COMMA,ADD,SUBS,MUL,DIV,MOD,
	EQ,LT,GT, NE,LE,GE,AND,OR,FORMAT,SUB,END,RETURN,LOCAL,
	WHILE,FOR,TO,IF,ELSE,THEN,DIM,UBOUND,BYE,BREAK,RESUME };
char	*kwd[]={ "AND","OR","FORMAT","SUB","END","RETURN","LOCAL","WHILE",
	"FOR","TO","IF","ELSE","THEN","DIM","UBOUND","BYE","BREAK","RESUME",0 };

char	lbuf[256],tokn[SYMSZ],*lp;	/* LEXER STATE */
int	lnum,tok,tokv,ungot;		/* LEXER STATE */
int	(*prg[PRGSZ])(),(**pc)(),cpc,lmap[PRGSZ]; /* COMPILED PROGRAM */
Val	stk[STKSZ],*sp;			/* RUN-TIME STACK */
Val	value[VARS];			/* VARIABLE VALUES */
char	name[VARS][SYMSZ];		/* VARIABLE NAMES */
int	sub[VARS][LOCS+2];		/* N,LOCAL VAR INDEXES */
int	mode[VARS];			/* 0=NONE, 1=DIM, 2=SUB */
Val	ret;				/* FUNCTION RETURN VALUE */
int	cstk[STKSZ], *csp;		/* COMPILER STACK */
int	nvar,cursub,temp,compile,ipc,(**opc)(); /* COMPILER STATE */
char	stab[STRSZ], *stabp;		/* STRING TABLE */
jmp_buf	trap;				/* TRAP ERRORS */

#define A	sp[1]			/* LEFT OPERAND */
#define B	sp[0]			/* RIGHT OPERAND */
#define PCV	((Val)*pc++)		/* GET IMMEDIATE */
#define STEP	return 1		/* CONTINUE RUNNING */
#define DRIVER	while ((*pc++)())	/* RUN PROGRAM */
#define LOC(N) value[sub[v][N+2]]	/* SUBROUTINE LOCAL */
Val *bound(Val *mem, int n) { if (n<1 || n>*mem) err("BOUNDS"); return mem+n;  }

int	(*kwdhook)(char *kwd);		/* KEYWORD HOOK */
int	(*funhook)(char *kwd, int n);	/* FUNCTION CALL HOOK */

initbasic(int comp) { pc=prg; sp=stk+STKSZ; csp=cstk+STKSZ; stabp=stab; compile=comp; }
bad(char *msg) { printf("ERROR %d: %s\n", lnum, msg); longjmp(trap,1); }
err(char *msg) { printf("ERROR %d: %s\n",lmap[pc-prg-1],msg); longjmp(trap,2); }
emit(int opcode()) { lmap[cpc]=lnum; prg[cpc++]=opcode; }
inst(int opcode(), Val x) { emit(opcode); emit((Code)x); }
BYE_() { longjmp(trap,4); }
BREAK_() { longjmp(trap,3); }
RESUME_() { pc=opc? opc:pc; opc=pc; cpc=ipc; STEP; }
NUMBER_() { *--sp=PCV; STEP; }
LOAD_() { *--sp=value[PCV]; STEP; }
STORE_() { value[PCV]=*sp++; STEP; }
ECHO_() { printf("%d\n",*sp++); }
FORMAT_() { char *f; Val n=PCV, *ap=(sp+=n)-1;
	for (f=stab + *sp++; *f; f++)
		if (*f=='%') printf("%d", (int)*ap--);
		else if (*f=='$') printf("%s", (char*)*ap--);
		else putchar(*f);
	putchar('\n'); STEP;
}
ADD_() { A+=B; sp++; STEP; };
SUBS_() { A-=B; sp++; STEP; };
MUL_() { A*=B; sp++; STEP; };
DIV_() { if (!B) sp+=2,err("DIVISION BY ZERO"); A/=B; sp++; STEP; };
MOD_() { if (!B) sp+=2,err("MODULUS OF ZERO"); A%=B; sp++; STEP; };
EQ_() { A=(A<B)? -1: 0; sp++; STEP; };
LT_() { A=(A<B)? -1: 0; sp++; STEP; };
GT_() { A=(A>B)? -1: 0; sp++; STEP; };
NE_() { A=(A!=B)? -1: 0; sp++; STEP; };
LE_() { A=(A<=B)? -1: 0; sp++; STEP; };
GE_() { A=(A>=B)? -1: 0; sp++; STEP; };
AND_() { A&=B; sp++; STEP; };
OR_() { A|=B; sp++; STEP; };
JMP_() { pc=prg+(int)*pc; STEP; }
FALSE_() { if (*sp++) pc++; else pc=prg+(int)*pc; STEP; }
FOR_() { if (value[PCV] >= *sp) pc=prg+(int)*pc, sp++; else PCV; STEP; }
NEXT_() { value[PCV]++; STEP; }
CALL_() { Val v=PCV, n=sub[v][1], x, *ap=sp;
	while (n--) { x=LOC(n); LOC(n)=*ap; *ap++=x; }
	for (n=sub[v][1]; n<sub[v][0]; n++) *--sp=LOC(n);
	*--sp=pc-prg;
	pc=prg+value[v];
	STEP;
}
RETURN_() { int v=PCV, n=sub[v][0];
	pc=prg+*sp++;
	while (n--) LOC(n)=*sp++;
	STEP;
}
SETRET_() { ret=*sp++; STEP; }
RV_() { *--sp=ret; STEP; }
DROP_() { sp+=PCV; STEP; }
DIM_() { int v=PCV, n=*sp++; Val *mem=calloc(sizeof(Val),n+1);
	mem[0]=n; value[v]=(Val)mem;
}
LOADI_() { Val x=*sp++; x=*bound((Val*)value[PCV],x); *--sp=x; STEP; }
STOREI_() { Val x=*sp++, i=*sp++; *bound((Val*)value[PCV],i)=x; STEP; }
UBOUND_() { *--sp=*(Val*)value[PCV]; STEP; }
find(char *var) {
	int	i;
	for (i=0; i<nvar && strcmp(var,name[i]); i++);
	if (i==nvar) strcpy(name[nvar++], var);
	return i;
}
read() {	/* READ TOKEN */
	char *p,*d,**k, *pun="(),+-*/\\=<>", *dub="<><==>";
	if (ungot) return ungot=0, tok;	/* UNGOT PREVIOUS */
	while (isspace(*lp)) lp++;	/* SKIP SPACE */
	if (!*lp || *lp=='#') return tok=0; /* END OF LINE */
	if (isdigit(*lp))		/* NUMBER */
		return tokv=strtol(lp,&lp,0), tok=NUMBER;
	if ((p=strchr(pun,*lp)) && lp++) { /* PUNCTUATION */
		for (d=dub; *d && strncmp(d,lp-1,2); d+=2);
		if (!*d) return tok=(p-pun)+LP;
		return lp++, tok=(d-dub)+NE;
	} else if (isalpha(*lp)) {	/* IDENTIFIER */
		for (p=tokn; isalnum(*lp); ) *p++=toupper(*lp++);
		for (*p=0, k=kwd; *k && strcmp(tokn,*k); k++);
		if (*k) return tok=(k-kwd)+AND;
		return tokv=find(tokn), tok=NAME;
	} else if (*lp=='"' && lp++) {	/* STRING */
		for (p=stabp; *lp && *lp!='"'; ) *stabp++=*lp++;
		return *stabp++=0, lp++, tokv=p-stab, tok=STRING;
	} else	return bad("BAD TOKEN");
}
want(int type) { return !(ungot=read()!=type); }
need(int type) { if (!want(type)) bad("SYNTAX ERROR"); }
#define LIST(BODY) if (!want(0)) do {BODY;} while (want(COMMA))
base() {		/* BASIC EXPRESSION */
	int neg=want(SUBS)? (inst(NUMBER_,0),1): 0;
	if (want(NUMBER)) inst(NUMBER_, tokv);
	else if (want(STRING)) inst(NUMBER_, (Val)(stab+tokv));
	else if (want(NAME)) {
		int var=tokv;
		if (want(LP))
			if (mode[var]==1) /* DIM */
				expr(), need(RP), inst(LOADI_, var);
			else {
				int n=0;
				LIST(if (tok==RP) break; expr(); n++);
				need(RP);
				if (!funhook || !funhook(name[var],n)) {
					if (mode[var]!=2 || n!=sub[var][1])
						bad("BAD SUB/ARG COUNT");
					inst(CALL_, var);
					emit(RV_);
				}
			}
		else		inst(LOAD_, var);
	} else if (want(LP))	expr(), need(RP);
	else if (want(UBOUND))	need(LP),need(NAME),need(RP),inst(UBOUND_,tokv);
	else			bad("BAD EXPRESSION");
	if (neg)		emit(SUBS_);	/* NEGATE */
}
int (*bin[])()={ADD_,SUBS_,MUL_,DIV_,MOD_,EQ_,LT_,GT_, NE_,LE_,GE_,AND_,OR_};
#define BIN(NAME,LO,HI,ELEM)  NAME() { int (*o)(); \
	ELEM(); \
	while (want(0), LO<=tok && tok<=HI) \
		o=bin[tok-ADD], read(), ELEM(), emit(o); \
	return 0; }
BIN(factor,MUL,MOD,base)
BIN(addition,ADD,SUBS,factor)
BIN(relation,EQ,GE,addition)
BIN(expr,AND,OR,relation)
stmt() {	/* STATEMENT */
	int	n,var;
	switch (read()) {
	case FORMAT:
		need(STRING), inst(NUMBER_, tokv);
		n=0; if (want(COMMA)) LIST(expr(); n++);
		inst(FORMAT_, n);
		break;
	case SUB:	/* CSTK: {SUB,INDEX,JMP} */
		if (!compile) bad("SUB MUST BE COMPILED");
		compile++;			/* MUST BALANCE WITH END */
		need(NAME), mode[cursub=var=tokv]=2; /* SUB NAME */
		n=0; LIST(need(NAME); sub[var][n+++2]=tokv); /* PARAMS */
		*--csp=cpc+1, inst(JMP_,0);	/* JUMP OVER CODE */
		sub[var][0]=sub[var][1]=n;	/* LOCAL=PARAM COUNT */
		value[var]=cpc;			/* ADDRESS */
		*--csp=var, *--csp=SUB;		/* FOR "END" CLAUSE */
		break;
	case LOCAL:
		LIST(need(NAME); sub[cursub][sub[cursub][0]+++2]=tokv;);
		break;
	case RETURN:
		if (temp) inst(DROP_, temp);
		if (!want(0))	expr(), emit(SETRET_);
		inst(RETURN_, cursub);
		break;
	case WHILE:	/* CSTK: {WHILE,TEST-FALSE,TOP} */
		compile++;			/* BODY IS COMPILED */
		*--csp=cpc, expr();
		*--csp=cpc+1, *--csp=WHILE, inst(FALSE_, 0);
		break;
	case FOR:	/* CSTK: {FOR,TEST-FALSE,I,TOP}; STK:{HI} */
		compile++;			/* BODY IS COMPILED */
		need(NAME), var=tokv, temp++;
		need(EQ), expr(), inst(STORE_,var);
		need(TO), expr();
		*--csp=cpc, inst(FOR_,var), emit(0);
		*--csp=var, *--csp=cpc-1, *--csp=FOR;
		break;
	case IF:	/* CSTK: {IF,N,ENDS...,TEST-FALSE} */
		expr(), inst(FALSE_,0), *--csp=cpc-1;
		if (want(THEN)) { stmt(); prg[*csp++]=(Code)cpc; }
		else	compile++, *--csp=0, *--csp=IF;
		break;
	case ELSE:
		n=csp[1]+1;
		inst(JMP_,0);			/* JUMP OVER "ELSE" */
		*--csp=IF, csp[1]=n, csp[2]=cpc-1; /* ADD A FIXUP */
		prg[csp[2+n]]=(Code)cpc;	/* PATCH "ELSE" */
		csp[2+n]=!want(IF)? 0:		/* "ELSE IF" */
			(expr(), inst(FALSE_,0), cpc-1);
		break;
	case END:
		need(*csp++), compile--;		/* MATCH BLOCK */
		if (csp[-1]==SUB) {
			inst(RETURN_, *csp++);
			prg[*csp++]=(Code)cpc;		/* PATCH JUMP */
		} else if (csp[-1]==WHILE) {
			prg[*csp++]=(Code)(cpc+2);	/* PATCH TEST */
			inst(JMP_, *csp++);		/* LOOP TO TEST */
		} else if (csp[-1]==FOR) {
			prg[*csp++]=(Code)(cpc+4);	/* PATCH TEST */
			inst(NEXT_, *csp++);		/* INCREMENT */
			inst(JMP_, *csp++);		/* LOOP TO TEST */
			temp--;				/* ONE LESS TEMP */
		} else if (csp[-1]==IF) {
			for (n=*csp++; n--; )		/* PATCH BLOCK ENDS */
				prg[*csp++]=(Code)cpc;
			if (n=*csp++) prg[n]=(Code)cpc; /* PATCH "ELSE" */
		}
		break;
	case NAME:
		var=tokv;
		if (want(EQ)) expr(), inst(STORE_, var);
		else if (want(LP))
			expr(),need(RP),need(EQ),expr(),inst(STOREI_,var);
		else if (!kwdhook || !kwdhook(tokn)) {
			int n=0; LIST(expr(); n++);
			if (!funhook || !funhook(name[var],n)) {
				if (mode[var]!=2 || n!=sub[var][1])
					bad("BAD SUB/ARG COUNT");
				inst(CALL_, var);
			}
		}
		break;
	case DIM:
		need(NAME), mode[var=tokv]=1;	/* SET VAR MODE TO DIM */
		need(LP), expr(), need(RP), inst(DIM_, var);
		break;
	case RESUME: if (!want(0)) expr(); emit(RESUME_); break;
	case BREAK:		emit(BREAK_); break;
	case BYE:		emit(BYE_); break;
	case GT:		expr(); emit(ECHO_); break;
	default:		if (tok) bad("BAD STATEMENT");
	}
	if (!want(0))		bad("TOKENS AFTER STATEMENT");
}
interp(FILE *sf) {	/* INTERPRETER LOOP */
	for (;;) {
		int code=setjmp(trap);			/* RETURN ON ERROR */
		if (code==1 && sf!=stdin) return 1;	/* FILE SYNTAX ERROR */
		if (code==2) opc=pc;			/* FAULT */
		if (code==3) pc=opc?opc:pc, cpc=ipc;	/* "BREAK" */
		if (code==4) return 0;			/* "BYE" */
		for (;;) {
			if (sf==stdin) printf("%d> ",lnum+1,stdout);
			if (!fgets(lp=lbuf,sizeof lbuf,sf)) break;
			lnum++, ungot=0, stmt();	/* PARSE AND COMPILE */
			if (compile) continue;		/* CONTINUE COMPILING */
			opc=pc, pc=prg+ipc;		/* START OF IMMEDIATE */
			emit(BREAK_); DRIVER;		/* RUN STATEMENT */
		}
		ipc=cpc+1, compile=0, fclose(sf), sf=stdin; /* DONE COMPILING */
		emit(BYE_); DRIVER;			/* RUN PROGRAM */
	}
}
