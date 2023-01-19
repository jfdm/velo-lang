# Velo.

[![Build Status](https://github.com/jfdm/velo-lang/actions/workflows/ci-ubuntu.yml/badge.svg)](https://github.com/jfdm/velo-lang/actions/workflows/ci-ubuntu.yml)

A tiny language to explore efficient verified implementations of functional languages in Idris2.


## Artefact

We also include scripts to generate a reproducible artefact.

Please consult the following project to generate the base virtual box image required, and how we approach the building of the artefact.

https://github.com/jfdm/packer-idris

Once you have generated the image you can generate the artefact as follows:

```bash
SOURCE_VM="<location of the base ovf>" make artefact
```

This will generate in `artefact` the following files:

1. `velo.box` :: A Virtual Box virtual machine that contains Velo's source code & test suite;
2. `velo.tar.gz` :: A copy of Velo's source code, and generated IdrisDoc;
3. `velo_doc.tar.gz` :: A copy of the IdrisDoc for the coding project;
4. `velo_html.tar.gz` :: A copy of the katla generated html showing semantically highlighted code;
4. `velo.pdf` :: A copy of the submitted paper;
