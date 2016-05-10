# decomposing-montague #

This repository contains the [**Coq**](https://coq.inria.fr/) code (in the file `ConDyn.v`) associated with the paper [*Decomposing Montagovian Dynamics*](http://home.uchicago.edu/~gkobele/files/Kobele16DecomposingMontague.pdf).

The **LaTeX** source of the paper can be obtained from the **Coq** document by means of the command line utility *coqdoc*, included with **Coq**.  I used the following command:

`coqdoc --latex -g --no-index --body-only --no-lib-name -o ConDyn.tex ConDyn.v`

This generates the body of a **LaTeX** file, which is input directly into the included file `main.tex`.  (I post-processed the output `ConDyn.tex` file by stripping out the first four or so lines.)
