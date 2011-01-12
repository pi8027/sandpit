
#include <stdio.h>

size_t mystrlen(const char *str)
{
	size_t iter = 0;
	while(str[iter]){
		iter++;
	}
	return iter;
}

void *mymemcpy(void *dest,const void *src,size_t n)
{
	size_t iter = 0;
	while(iter != n){
		((char*)dest)[iter] = ((char*)src)[iter];
		iter++;
	}
	return dest;
}

char *mystrcat(const char *s1,const char *s2)
{
	size_t size1 = mystrlen(s1),size2 = mystrlen(s2);
	char *result = malloc(size1+size2+1);
	if(!result){
		return NULL;
	}
	mymemcpy(result,s1,size1);
	mymemcpy(result+size1,s2,size2+1);
	return result;
}

int main(void)
{
	printf("%s\n",mystrcat("foo","bar"));
	return 0;
}
