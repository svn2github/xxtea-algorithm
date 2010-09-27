/*
 Copyright 2010 British Broadcasting Corporation and Kamaelia Contributors(1)

 (1) Kamaelia Contributors are listed in the AUTHORS file and at
     http://www.kamaelia.org/AUTHORS - please extend this file,
     not this notice.

 Licensed under the Apache License, Version 2.0 (the "License");
 you may not use this file except in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software
 distributed under the License is distributed on an "AS IS" BASIS,
 WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 See the License for the specific language governing permissions and
 limitations under the License.
 -------------------------------------------------------------------------
*/
#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include <WINSOCK2.H>
#include "keygen.h"

/*
random key where the key will be stored.
key_len : length of the key
*/
void get_key(char *random_key, unsigned key_len) {
    char tmp[11]; // max of 10 digits ( i am assuming rand returns a 32 bit number)
    unsigned key_cnt = 0;
    int i = 0;
        int tmp_len = 0;
    struct timeval tp;

    //gettimeofday(&tp, NULL);
	//localtime()
        srand((unsigned int)tp.tv_usec);

        while(key_cnt < key_len) {
        memset(tmp, 0, sizeof(tmp));
        sprintf(tmp, "%x", rand());
        tmp_len = strlen(tmp);
        for(i=0; ((i < tmp_len) && (key_cnt < key_len)); i++, key_cnt++) {
            random_key[key_cnt] = tmp[i];
         }
       }
       random_key[key_cnt] = 0;
}
/*
int main() {
        char random_key[10];
        get_key(random_key,9);
        printf("%s",random_key);
}*/