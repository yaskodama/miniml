# miniml
* This program is translated from the MINICAML included in the Caml-light
   ver. 0.71 package and wrritten in Standard ML/NJ syntax.
   Originall copyright as follows:

------------- 
Software: Caml Light, version 0.71 of January 1996, hereinafter
referred to as "the software".

The software has been designed and produced by Xavier Leroy,
Damien Doligez, Francois Rouaix, Jerome Vouillon and Pierre Weis,
research workers for the Institut National de Recherche en Informatique et
en Automatique (INRIA) - Domaine de Voluceau - Rocquencourt - 78153 Le
Chesnay Cedex - France.

INRIA holds all ownership rights to Caml Light version 0.7.

The software has been registered at Agence pour la Protection
des Programmes (APP).

Preamble:

The software is currently being developed and INRIA desires
that it be used by the scientific community so as to test, evaluate
and develop it.  To this end, INRIA has decided to have a prototype of
the software distributed by FTP.

a- Extent of the rights granted by the INRIA to the user of the software:

INRIA freely grants the right to use, modify and integrate the
software in another software, provided that all derivative works are
distributed under the same conditions as the software.

b- Reproduction of the software:

INRIA grants any user of the software the right to reproduce it so as
to circulate it in accordance with the same purposes and conditions as
those defined at point a- above.  Any copy of the software and/or relevant
documentation must comprise reference to the ownership of INRIA and
the present file.

The user undertakes not to carry out any paying distribution of the
software. However, he is authorized to bill any person or body for the
cost of reproduction of said software. As regards any other type of
distribution, the user undertakes to apply to obtain the express
approval of INRIA.
--------------------------------------
and
--------------------------------------
All other files included in the Caml Light distribution or generated
by the Caml Light system are subject to the conditions in points a-
and b- above.
-------------------------------------

And my copyright is:

Copyright(c) 1996 by Yasushi KODAMA
and this program is subject to above conditions, then feel free to modify
and integrate this program. If you have any comments or find bugs,
please let me know. 

You can execute some examples as follows:
<< factorial >>
## let rec fac =function 0->1|x->((fac (x-1))*x);
fac : (int -> int) = <fun>
## fac 0;
- : int = 1
## fac 5;
- : int = 120
## fac 10;
- : int = 3628800
## fac 12;
- : int = 479001600

Originally, on the MINICAML included in caml-right packages, double
semicolons `;;' are used by the delimitter as the end of a line,
but on this system, single semicolon is used for this purpose.

August 1996
Thanks,
yas@is.noda.sut.ac.jp *)
