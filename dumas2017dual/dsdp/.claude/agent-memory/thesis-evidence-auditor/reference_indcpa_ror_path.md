---
name: reference_indcpa_ror_path
description: The correct relative path for indcpa_ror.v is homomorphic_encryption/indcpa_ror.v from the infotheo-itp root; matches _CoqProject
metadata:
  type: reference
---

Full path: /Users/cheng-huiweng/Projects/coq/infotheo-itp/homomorphic_encryption/indcpa_ror.v

_CoqProject entry (infotheo-itp root): `homomorphic_encryption/indcpa_ror.v`

The thesis sidenote (dsdp.tex:654) cites `\coqin{homomorphic_encryption/indcpa_ror.v}`.
This path is CORRECT relative to the project root.

The DSDP file imports via flat module name: `Require Import ... indcpa_ror.`
(The homomorphic_encryption prefix is not part of the Coq module name — it is only the
directory structure. The thesis citing the file path rather than the module name is a
valid documentation choice.)
