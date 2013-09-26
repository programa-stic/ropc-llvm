#ifndef __INSTRINSIC_H__
#define __INSTRINSIC_H__

void intrinsic_memcpy(char * dst, char * src, int len) {
    int i = 0;

    while (i < len) {
        *dst = *src;
        dst  = dst + 1;
        src  = src + 1;
        i    = i + 1;
    }
}

#endif /* !__INSTRINSIC_H__ */