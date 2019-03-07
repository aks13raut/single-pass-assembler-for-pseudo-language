#include <stdio.h>
#include <string.h>
#include <stdlib.h>

//SYMTAB
struct symbol_table {
	struct symbol_table_entry {
		char symbol[10];
		int defined;
		int seg_name;
		int equ;
		//bool equ_type;
		int value;
		int owner;
		int len;
		int size;
		struct forward_reference* FRT;
		//int source_no;
		
	};
	struct symbol_table_entry s[15];
	int symbCount;
};

//SRTAB
struct srtab {
	int symtab_id[4];
	struct srtab *next;
};

//FRT
struct forward_reference {
	int addr;
	int m;
	int stsrt_no;
	struct forward_reference * next;
	char *word[5];
};

//MOT
struct mot_t {
	struct mot_entry {
		char mnem[15];
		int opcode;
		int  len;
		char format[2];
		void (*func_ptr)(char **, struct mot_t*, int m, struct symbol_table *,FILE*
						 ,int *, int*, int *, int *, struct srtab **,int *);
	};
	struct mot_entry m[15];
	int count;
};

void push_frwd_ref(	struct forward_reference ** t_start,int addr,
					char *word[],int m,int srtrt_no) {
	struct forward_reference * frwd_ref;
	int i=0;
	frwd_ref = (struct forward_reference *)malloc(sizeof(struct forward_reference));
	frwd_ref->addr = addr;
	while(word[i]!=NULL){
		frwd_ref->word[i] = (char*)malloc(sizeof(char)*(strlen(word[i])+1));
		frwd_ref->word[i] = strdup(word[i]);
		++i;
	}
	frwd_ref->m = m;
	frwd_ref->stsrt_no = srtrt_no;
	frwd_ref->next = *t_start;
	*t_start = frwd_ref;
}

struct forward_reference* pop_frwd_ref(	struct forward_reference ** t_start) {
	struct forward_reference * frwd_ref;
	if (*t_start==NULL)
		return NULL;
	frwd_ref = *t_start;
	*t_start = (*t_start)->next;
	return frwd_ref;
}

void print_frt(struct forward_reference *start) {

	struct forward_reference * frwd_ref= start;
	int i;
	if(frwd_ref==NULL)
		return;
	printf("FRT\n");
	while(frwd_ref != NULL){
		printf("%d %d ",frwd_ref->addr,frwd_ref->m);
		i=0;
		while(frwd_ref->word[i]!=NULL && i < 3){
			printf("%s ",frwd_ref->word[i]);
			++i;
		}
		printf("\n");
		frwd_ref = frwd_ref->next;
	}
}

int reg_code(char word[]) {
	if( 	 strcmp(word,"AX")==0)
		return 0;
	else if( strcmp(word,"BX")==0)
		return 1;
	else if( strcmp(word,"CX")==0)
		return 2;
	else if( strcmp(word,"DX")==0)
		return 3;
	else if( strcmp(word,"DS")==0)
		return 4;
	else if( strcmp(word,"CS")==0)
		return 5;
	else if( strcmp(word,"ES")==0)
		return 6;
	else if( strcmp(word,"SS")==0)
		return 7;
	return -1;
}

int check_symtab(char word[],struct symbol_table *symtab){
	int i;
	for(i=0; i < symtab->symbCount; i++)
		if(strcmp(word,symtab->s[i].symbol)==0)
			return i;
	return -1;
}

void process_imperative(char * word[], struct mot_t* mot, int m,
						struct symbol_table *symtab, FILE* opfp,
						int *LC, int* offset,int *L, int *active_owner_id, struct srtab **t_stsrt,int *srta) {
	char *operands[2],oprnd[20],*op[2];
	int op_count=0,id,is_complete=1;
	int opcode,op1,op2,sreg,sreg_index;

	
	*L = mot->m[m].len;
	strcpy(oprnd,word[1]);
	operands[0] = strtok(oprnd," ,\t");
	while(operands[op_count]!=NULL){
		op[op_count] = strdup(operands[op_count]);
		++op_count;
		operands[op_count] = strtok(NULL," ,\t");
	}
	if( strcmp(mot->m[m].format,"RR")==0 && op_count==2 ) {
		op1 = reg_code(operands[0]);
		if(op1 == -1) {
			id = check_symtab(operands[0],symtab);
			if(id == -1){
				is_complete = 0;
				id = symtab->symbCount;
				strcpy( symtab->s[id].symbol, operands[0]);
				symtab->s[id].defined = 0;
				symtab->s[id].seg_name = 0;
				symtab->s[id].equ = 1;
				symtab->s[id].FRT = NULL;
				++(symtab->symbCount);
			}
			else {
				if( symtab->s[id].defined == 0)
					is_complete = 0;
				else  op1 = symtab->s[id].value;
			}
		}
		if(is_complete==0){
			push_frwd_ref(&(symtab->s[id].FRT),*LC,word,m,*srta);
			printf("Added forward reference for %s\n",symtab->s[id].symbol);
			return;
		}
		op2 = reg_code(operands[1]);
		if(op2 == -1) {
			id = check_symtab(operands[1],symtab);
			if(id == -1){
				is_complete = 0;
				id = symtab->symbCount;
				strcpy( symtab->s[id].symbol, operands[1]);
				symtab->s[id].defined = 0;
				symtab->s[id].seg_name = 0;
				symtab->s[id].equ = 1;
				symtab->s[id].FRT = NULL;
				++(symtab->symbCount);
			}
			else {
				if( symtab->s[id].defined == 0)
					 is_complete = 0;
				else op2 = symtab->s[id].value;
			}
		}
		if(is_complete==0){
			push_frwd_ref(&(symtab->s[id].FRT),*LC,word,m,*srta);
			printf("Added forward reference for %s\n",symtab->s[id].symbol);
			return;
		}
		opcode = mot->m[m].opcode;
		if(is_complete==1)
			fprintf(opfp,"%03d %02d %d %d\n",*LC,opcode,op1,op2);
	}
	else if( strcmp(mot->m[m].format,"RM")==0 && op_count==2 ) {
		op1 = reg_code(operands[0]);
		if(op1 == -1) {
			id = check_symtab(operands[0],symtab);
			if(id == -1){
				is_complete = 0;
				id = symtab->symbCount;
				strcpy( symtab->s[id].symbol, operands[0]);
				symtab->s[id].defined = 0;
				symtab->s[id].seg_name = 0;
				symtab->s[id].equ = 1;
				symtab->s[id].FRT = NULL;				
				++(symtab->symbCount);
			}
			else {
				if( symtab->s[id].defined == 0){
					is_complete = 0;
					push_frwd_ref(&(symtab->s[id].FRT),*LC,word,m,*srta);
				}
				else op1 = symtab->s[id].value;
			}
		}
		if(is_complete==0){
			push_frwd_ref(&(symtab->s[id].FRT),*LC,word,m,*srta);
			printf("Added forward reference for %s\n",symtab->s[id].symbol);
			return;
		}
		id = check_symtab(operands[1],symtab);
		if(id == -1){
			is_complete = 0;
			id = symtab->symbCount;
			strcpy( symtab->s[id].symbol, operands[1]);
			symtab->s[id].defined = 0;
			symtab->s[id].FRT = NULL;
			++(symtab->symbCount);
		}
		else {
			if( symtab->s[id].defined == 0)
				 is_complete = 0;
			else {
				op2 = symtab->s[id].value;
				if(symtab->s[id].seg_name == 1){
					sreg = -1;
				}
				else{
					sreg_index = symtab->s[id].owner;
					for(int i=0;i<*srta;++i){
						t_stsrt = &((*t_stsrt)->next);
					}
					for(int j=0;j<4;++j)
						if((*t_stsrt)->symtab_id[j]==sreg_index)
							sreg = j+4;
				}
			}
		}
		if(is_complete==0){
			push_frwd_ref(&(symtab->s[id].FRT),*LC,word,m,*srta);
			printf("Added forward reference for %s\n",symtab->s[id].symbol);
			return;
		}
		opcode = mot->m[m].opcode;
		if(is_complete==1)
			if(sreg == -1)
					fprintf(opfp,"%03d %02d %d %d\n",*LC,opcode,op1,op2);
			else	fprintf(opfp,"%03d %02d %d %d:%d\n",*LC,opcode,op1,sreg,op2);
	}
}

void process_FRT( struct mot_t* mot, struct symbol_table *symtab, int id, FILE* opfp, struct srtab **t_stsrt,int *srta ){
	struct forward_reference* frwd_ref;
	int garbage=1;
	frwd_ref = pop_frwd_ref(&(symtab->s[id].FRT));
	while(frwd_ref != NULL){
		if( frwd_ref->m <= 3 ) // Imperative
			process_imperative(frwd_ref->word,mot,frwd_ref->m,symtab,opfp,&(frwd_ref->addr),&garbage,&garbage,&garbage,t_stsrt,&(frwd_ref->stsrt_no));
		frwd_ref = pop_frwd_ref(&(symtab->s[id].FRT));
	}
}

void process_segment(	char * word[], struct mot_t* mot, int m,
						struct symbol_table *symtab, FILE* opfp,
						int *LC, int* offset,int *L, int *active_owner_id, struct srtab **t_stsrt,int *srta) {
	*L = mot->m[m].len;
	int id = check_symtab(word[0],symtab);
	if(id == -1){
		id = symtab->symbCount;
		strcpy( symtab->s[id].symbol, word[0]);
		symtab->s[id].FRT = NULL;
	}
	symtab->s[id].defined = 1;
	symtab->s[id].seg_name = 1;
	symtab->s[id].equ = 0;
	symtab->s[id].value = *LC;
	symtab->s[id].size = 0;
	symtab->s[id].len = 0;
	if(id == symtab->symbCount)
		++(symtab->symbCount);
	*active_owner_id = id;
	*offset = 0;
	process_FRT(mot,symtab,id,opfp,t_stsrt,srta);
}
void process_assume(	char * word[], struct mot_t* mot, int m,
						struct symbol_table *symtab, FILE* opfp,
						int *LC, int* offset,int *L, int *active_owner_id, struct srtab **t_stsrt,int *srta) {
	char *operands[8];
	int op_count=0,regCode;
	struct srtab *t_srtab,*srtabs;
	*L = mot->m[m].len;
	operands[0] = strtok(word[1]," ,:\t");
	while(operands[op_count]!=NULL){
		++op_count;
		operands[op_count] = strtok(NULL," ,:\t");
	}
	//creating new srtab
	t_srtab = (struct srtab*)malloc(sizeof(struct srtab));
	if(*t_stsrt == NULL)
		for(int j=0; j<4; ++j)
			t_srtab->symtab_id[j] = -1;
	else 	{
		srtabs = *t_stsrt;
		for(int i=0;i<*srta;++i)
			srtabs = srtabs->next;
		for(int j=0; j<4; ++j){
			t_srtab->symtab_id[j] = (*t_stsrt)->symtab_id[j];
			printf("|%2d|%2d|\n",j+4,srtabs->symtab_id[j]);
		}
		
	}
	t_srtab->next = NULL;
	
	for(int i=0;i<op_count;i+=2) {
		printf("%s=%s => ",operands[i],operands[i+1]);
		int id = check_symtab(operands[i+1],symtab);
		if(id == -1 && strcmp(operands[i+1],"NOTHING")!=0 ){
			id = symtab->symbCount;
			symtab->s[id].defined = 0;
			strcpy( symtab->s[id].symbol, operands[i+1]);
			symtab->s[id].FRT = NULL;
		}
		regCode = reg_code(operands[i]);
		printf("reg_code = %d & value = %d\n",regCode,id);
		if(regCode != -1)
			t_srtab->symtab_id[regCode-4] = id;
		//symtab->s[id].seg_name = 1;??needed to check?
		if(id == symtab->symbCount)
			++(symtab->symbCount);
	}

	//adding newly created srtab to STSRT
	*srta += 1;
	while(*t_stsrt != NULL){
		t_stsrt = &((*t_stsrt)->next);
	}
	*t_stsrt = t_srtab;
	for(int j=0; j<4; ++j){
		printf("|%2d|%2d|\n",j+4,(*t_stsrt)->symtab_id[j]);
	}
}
int is_number(char str[]) {
	int i,len=strlen(str);
	for(i=0;i<len;i++)
		if(str[i]<'0'||str[i]>'9')
			return 0;
	return 1;
}
void process_org(	char * word[], struct mot_t* mot, int m,
					struct symbol_table *symtab, FILE* opfp,
					int *LC, int* offset,int *L, int *active_owner_id, struct srtab **t_stsrt,int *srta) {
	int value=*offset;
	*L = mot->m[m].len;
	if(is_number(word[1]))
		value = atoi(word[1]);
	*offset = value;
}
void process_ends(	char * word[], struct mot_t* mot, int m,
					struct symbol_table *symtab, FILE* opfp,
					int *LC, int* offset,int *L, int *active_owner_id, struct srtab **t_stsrt,int *srta) {
	*L = mot->m[m].len;
	int id = check_symtab(word[0],symtab);
	if(id == -1) {
		//error : no such segment name defined
		return;
	}
	if( *active_owner_id == id)
		return;
	//error : active_owner_id no matching
	return;
}
void process_equ(	char * word[], struct mot_t* mot, int m,
					struct symbol_table *symtab, FILE* opfp,
					int *LC, int* offset,int *L, int *active_owner_id, struct srtab **t_stsrt,int *srta) {
	*L = mot->m[m].len;
	int id = check_symtab(word[0],symtab);
	int reg;
	if(id == -1){
		id = symtab->symbCount;
		strcpy( symtab->s[id].symbol, word[0]);
		symtab->s[id].FRT = NULL;
	}
	symtab->s[id].defined = 1;
	symtab->s[id].seg_name = 0;
	symtab->s[id].equ = 1;
	if( strcmp(word[2],"*")==0)   // current address
		symtab->s[id].value = *offset;
	else {
		reg = reg_code(word[2]);
		if(reg != -1)   // reg mapping
			 symtab->s[id].value = reg; 
		//EQU for mem location not defined yet
	}
	symtab->s[id].size = 0;
	symtab->s[id].len = 0;
	symtab->s[id].owner = *active_owner_id;
	if(id == symtab->symbCount)
		++(symtab->symbCount);
	process_FRT(mot,symtab,id,opfp,t_stsrt,srta);
}
void process_dw(char * word[], struct mot_t* mot, int m,
				struct symbol_table *symtab, FILE* opfp,
				int *LC, int* offset,int *L, int *active_owner_id, struct srtab **t_stsrt,int *srta) {
	int id = check_symtab(word[0],symtab);
	int data;
	if(id == -1){
		id = symtab->symbCount;
		strcpy( symtab->s[id].symbol, word[0]);
		symtab->s[id].FRT = NULL;
	}
	symtab->s[id].defined = 1;
	symtab->s[id].seg_name = 0;
	symtab->s[id].equ = 0;
	symtab->s[id].value = *offset;
	symtab->s[id].size = 2;
	symtab->s[id].len = 2;
	symtab->s[id].owner = *active_owner_id;
	*L = symtab->s[id].len;
	if(*LC%2==1)
		*LC += 1;
	if(id == symtab->symbCount)
		++(symtab->symbCount);
	fprintf(opfp,"%03d %s\n",*LC,word[2]);
	process_FRT(mot,symtab,id,opfp,t_stsrt,srta);
}
void process_db(char * word[], struct mot_t* mot, int m,
				struct symbol_table *symtab, FILE* opfp,
				int *LC, int* offset,int *L, int *active_owner_id, struct srtab **t_stsrt,int *srta) {
	int id = check_symtab(word[0],symtab);
	int data;
	if(id == -1){
		id = symtab->symbCount;
		strcpy( symtab->s[id].symbol, word[0]);
		symtab->s[id].FRT = NULL;
	}
	symtab->s[id].defined = 1;
	symtab->s[id].seg_name = 0;
	symtab->s[id].equ = 0;
	symtab->s[id].value = *offset;
	symtab->s[id].size = 1;
	symtab->s[id].len = 1;
	symtab->s[id].owner = *active_owner_id;
	*L = symtab->s[id].len;
	if(id == symtab->symbCount)
		++(symtab->symbCount);
	fprintf(opfp,"%03d %s\n",*LC,word[2]);
	process_FRT(mot,symtab,id,opfp,t_stsrt,srta);
}
void process_end(char * word[], struct mot_t* mot, int m,
				struct symbol_table *symtab, FILE* opfp,
				int *LC, int* offset,int *L, int *active_owner_id, struct srtab **t_stsrt,int *srta) {
	//Allocating space for Literals
}

int check_mot(char word[],struct mot_t *tm){
	int i;
	for(i=0; i < tm->count; i++)
		if(strcmp(word,tm->m[i].mnem)==0)
			return i;
	return -1;
}

void print_symtab(struct symbol_table *symtab) {
	int i;
	printf("SYMTAB\n| symbol |defined|seg_name|equ|equ_type|value|owner|len|size|ptr to FRT|\n");
	for(i=0; i < symtab->symbCount; ++i){
		printf("|%7s | %5d |  %4d  | %d |        |%5d|%5d|%3d|%4d|ptr%x|\n",
				symtab->s[i].symbol,symtab->s[i].defined,symtab->s[i].seg_name,symtab->s[i].equ,symtab->s[i].value,symtab->s[i].owner,symtab->s[i].len,symtab->s[i].size,symtab->s[i].FRT);
		print_frt(symtab->s[i].FRT);
	}
}

void single_pass(FILE *ipfp, struct mot_t* mot, FILE* opfp) {
	struct symbol_table symtab;
	struct srtab  *stsrt=NULL,*srtabs;
	int srta=-1;
	int LC=0, offset=0, active_owner_id, L;
	int word_count, i, m;
	char line[80], *word[5];
	
	symtab.symbCount = 0; // intializing symbol_table
	
	while(fgets(line,80,ipfp) != NULL){
		word[0] = strtok(line," \n\t");
		word_count=0;
		while(word[word_count]!=NULL){
			++word_count;
			word[word_count] = strtok(NULL," \n\t");
		}
		
		if(word_count == 0)		// skips empty lines
			continue; 			//
		printf("\n>>%3d ",LC);
		for(i=0;i<word_count;++i)
			printf("%s ",word[i]);
		printf("\n");
		
		m = check_mot(word[0],mot);
		if(m != -1) { 			// instruction has no label	
			(mot->m[m].func_ptr)(word,mot,m,&symtab,opfp,&LC,&offset,&L,&active_owner_id,&stsrt,&srta);
		}
		else {
			m = check_mot(word[1],mot);	
			if(m != -1) {		// instruction has label
				if( m <= 3 ) // Imperative
					process_imperative(&word[1],mot,m,&symtab,opfp,&LC,&offset,&L,&active_owner_id,&stsrt,&srta);
				else	
					(mot->m[m].func_ptr)(word,mot,m,&symtab,opfp,&LC,&offset,&L,&active_owner_id,&stsrt,&srta);
 			}
			else {
				//error: no mnemonic found
			}
		}
		LC += L;
		offset += L;
		print_symtab(&symtab);
	}
	srtabs = stsrt;
	printf("\nSTSRT\n");
	for(int i=0;i<=srta;++i){
		printf("SRTAB[%d]\n",i);
		for(int j=0;j<4;++j)
			printf("|%2d|%2d|\n",j+4,srtabs->symtab_id[j]);
		srtabs = srtabs->next;
	}
}

void main() {
	FILE *ipfp,*opfp,*fp;
	
	struct mot_t mot;
	struct forward_reference *fr,*start=NULL;
	
	//intializing MOT
	fp = fopen("1MOT.txt","r");
	int count,i=0;
	while(!feof(fp)){
		fscanf(fp,"%s %d %d %s",mot.m[i].mnem,&(mot.m[i].opcode),&(mot.m[i].len),mot.m[i].format);
		
		if(i<=3)
			mot.m[i].func_ptr = &process_imperative;
		else if(i==4)
			mot.m[i].func_ptr = &process_segment;
		else if(i==5)
			mot.m[i].func_ptr = &process_assume;
		else if(i==6)
			mot.m[i].func_ptr = &process_ends;
		else if(i==7)
			mot.m[i].func_ptr = &process_org;
		else if(i==8)
			mot.m[i].func_ptr = &process_db;
		else if(i==9)
			mot.m[i].func_ptr = &process_dw;
		else if(i==10)
			mot.m[i].func_ptr = &process_equ;
		else if(i==11)
			mot.m[i].func_ptr = &process_end;
		
		++i;
	}
	mot.count = i;
	fclose(fp);
	
	ipfp = fopen("assembly_program.txt","r+");
	opfp = fopen("machine_code.txt","w");
	
	//printing MOT(for reference only)
	printf("MOT\n|mnemonics|opcode|len|format|func_ptr|\n");
	for(i=0;i<mot.count;++i){
		printf("| %7s |  %02d  | %1d |  %2s  |%x|\n",mot.m[i].mnem,mot.m[i].opcode,mot.m[i].len,mot.m[i].format,mot.m[i].func_ptr);
	}
	
	//printing register codes 
	printf("Register Codes\n|Register|code|\n");
	printf("|   AX   |  0 |\n");
	printf("|   BX   |  1 |\n");
	printf("|   CX   |  2 |\n");
	printf("|   DX   |  3 |\n");
	printf("|   DS   |  4 |\n");
	printf("|   CS   |  5 |\n");
	printf("|   ES   |  6 |\n");
	printf("|   SS   |  7 |\n");
	
	single_pass(ipfp,&mot,opfp);
	
}
