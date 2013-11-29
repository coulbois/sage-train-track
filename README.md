sage-train-track
================

Free group automorphisms and train-track representative in python/sage

To use the package just launch Sage in the repository containg the files and do

{{{
	sage: from all import *
}}

After this command, you can do

{{{
	sage: FreeGroup('abc')
	Free group over ['a', 'b', 'c']
	sage: FreeGroupAutomorphism('a->bCb,b->Bc,c->BcBa')
	Automorphism of the Free group over ['a', 'b', 'c']: a->bCb,b->Bc,c->BcBa
	sage: free_group_automorphisms.Cohen_Lustig_1_6()
	Automorphism of the Free group over ['a', 'b', 'c']: a->cccaCCC,b->CaccAbC,c->accAbccaCCBaCCAccccACCC
}}}
