
#include <stdio.h>

const char *mystrstr(const char *s1,const char *s2)
{
	while(1){
		size_t iter = 0;
		while(s1[iter] && s2[iter] && s1[iter] == s2[iter])iter++;
		if(!s2[iter])return s1;
		if(!s1[iter])return NULL;
		s1++;
	}
}

main(void)
{
	fputs(mystrstr("aaaaahogeaaaa","hoge"),stdout);
	fputc('\n',stdout);
	return 0;
}
