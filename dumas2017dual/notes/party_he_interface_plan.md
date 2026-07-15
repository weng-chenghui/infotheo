# Plan: Party-Labeled HE Interface for DSDP

## Goal

Create an HB interface for party-labeled homomorphic encryption that DSDP programs can depend on, with Benaloh as the default instance.

## Current State

### Problem
- DSDP uses `Party_Enc_Types` which is an **idealized** model: `enc = (party * msg)`
- Real HE instances (`Party_Benaloh_HE`, `Party_Paillier_HE`) exist but are **not used**
- No connection between DSDP programs and concrete cryptographic operations

### Files using `enc party msg`
1. `dsdp_program_alt_syntax.v` (line 84)
2. `dsdp_program.v` (line 50)
3. `dsdp_correctness.v` (line 52)
4. `dsdp_entropy_trace.v` (lines 69, 158)
5. `dsdp_entropy.v` (line 404)

---

## Proposed Design

### 1. New `Party_HE_types` Record (in `he_sig.v`)

```coq
Record Party_HE_types := MkPartyHE {
  phe_party : finType ;
  phe_msg : finComNzRingType ;
  phe_rand : ringType ;          (* ringType enables r1*r2 and r^+k *)
  phe_enc : finType ;            (* party-labeled ciphertext *)
  phe_pkey : Type ;              (* party-labeled key *)
}.
```

### 2. New `isPartyHE` Mixin (in `he_sig.v`)

```coq
HB.mixin Record isPartyHE (T : Party_HE_types) := {
  phe_E : phe_party T -> phe_msg T -> phe_rand T -> phe_enc T ;
  phe_K : phe_party T -> key -> phe_msg T -> phe_pkey T ;
  phe_D : phe_pkey T -> phe_enc T -> option (phe_msg T) ;
  phe_Emul : phe_enc T -> phe_enc T -> phe_enc T ;
  phe_Epow : phe_enc T -> phe_msg T -> phe_enc T ;
  (* Conversion to nat for r ^+ phe_msg_nat m2 *)
  phe_msg_nat : phe_msg T -> nat ;
  (* Concrete randomness: Emul combines randomness by multiplication *)
  phe_Emul_eq_add : forall p m1 m2 r1 r2,
    phe_Emul (phe_E p m1 r1) (phe_E p m2 r2) = phe_E p (m1 + m2) (r1 * r2) ;
  (* Concrete randomness: Epow raises randomness to power *)
  phe_Epow_eq_mul : forall p m1 m2 r,
    phe_Epow (phe_E p m1 r) m2 = phe_E p (m1 * m2) (r ^+ phe_msg_nat m2) ;
}.

#[short(type=Party_HE_scheme)]
HB.structure Definition Party_HE := { T of isPartyHE T }.
```

**Design decisions:**
- Use **concrete randomness** formulas (`r1 * r2` and `r ^+ k`), consistent with `isHE` mixin
- `phe_rand : ringType` enables ring operations on randomness
- `phe_msg_nat` provides conversion to nat for exponentiation
- `phe_D` returns `option` for decryption failure handling

### 3. Benaloh Instance (in `homomorphic_encryption.v`)

```coq
Section Benaloh_Party_HE_Instance.
Variables (party_type : finType) (n r : nat).
Hypothesis n_gt1 : (1 < n)%N.
Hypothesis r_gt1 : (1 < r)%N.
Variable y : 'Z_n.
Hypothesis y_order_r : y ^+ r = 1.

Definition Benaloh_Party_HE_types : Party_HE_types := {|
  phe_party := party_type ;
  phe_msg := [finComNzRingType of 'Z_r] ;  (* message space *)
  phe_rand := [ringType of 'Z_n] ;          (* randomness space, ringType *)
  phe_enc := [finType of (party_type * 'Z_n)] ;  (* ciphertext *)
  phe_pkey := (party_type * key * 'Z_r)%type ;
|}.

(* Concrete randomness proofs use enc_mul_dist and enc_exp_dist *)
Definition benaloh_phe_E p m u := (p, benaloh_enc y m u).
Definition benaloh_phe_msg_nat (m : 'Z_r) : nat := m.

Lemma benaloh_phe_Emul_eq_add : forall p m1 m2 r1 r2,
  (p, benaloh_enc y m1 r1 * benaloh_enc y m2 r2) = 
  benaloh_phe_E p (m1 + m2) (r1 * r2).
Proof. (* uses enc_mul_dist *) ... Qed.

Lemma benaloh_phe_Epow_eq_mul : forall p m1 m2 r,
  (p, (benaloh_enc y m1 r) ^+ (m2 : nat)) = 
  benaloh_phe_E p (m1 * m2) (r ^+ benaloh_phe_msg_nat m2).
Proof. (* uses enc_exp_dist *) ... Qed.

HB.instance Definition Benaloh_Party_HE_isPartyHE : 
  isPartyHE Benaloh_Party_HE_types := ...
End Benaloh_Party_HE_Instance.
```

### 4. Paillier Instance (in `homomorphic_encryption.v`)

Similar structure with:
- `phe_msg := [finComNzRingType of 'Z_n]`
- `phe_rand := [ringType of 'Z_n]`  
- `phe_enc := [finType of (party_type * 'Z_{n²})]`
- Proofs use `paillier_enc_mul_dist` and `paillier_enc_exp_dist`

### 5. DSDP File Updates

Each DSDP file changes from:
```coq
Let enc := enc party msg.
Let pkey := pkey party msg.
```

To:
```coq
Variable PHE : Party_HE_scheme.
Let enc := phe_enc PHE.
Let pkey := phe_pkey PHE.
Notation E := (phe_E PHE).
Notation Emul := (phe_Emul PHE).
Notation Epow := (phe_Epow PHE).
```

Or for concrete Benaloh usage:
```coq
Let PHE := Benaloh_Party_HE_types party n r y.
(* with appropriate hypotheses *)
```

### 6. Security Axioms (unchanged)

Keep in `homomorphic_encryption.v`:
```coq
Axiom E_enc_unif : ...
Axiom E_enc_inde : ...
```

These remain **separate** from the Party_HE instances. They are information-theoretic assumptions that can be justified by:
- IND-CPA security of the underlying HE scheme
- External cryptographic arguments

---

## Implementation Steps

### Phase 1: Define Interface
1. [x] Add `Party_HE_types` record to `homomorphic_encryption.v` (Note: placed here instead of `he_sig.v` because it depends on `key` type)
2. [x] Add `isPartyHE` mixin to `homomorphic_encryption.v`
3. [x] Add `Party_HE` structure to `homomorphic_encryption.v`
4. [x] Compile and test `homomorphic_encryption.v`

### Phase 2: Create Instances
5. [x] Create Benaloh instance in `homomorphic_encryption.v` (`Benaloh_Party_HE_types`, `Benaloh_Party_HE_isPartyHE`)
6. [x] Create Paillier instance in `homomorphic_encryption.v` (`Paillier_Party_HE_types`, `Paillier_Party_HE_isPartyHE`)
7. [ ] Remove or deprecate `Party_Enc_Types` section (kept for backward compatibility)
8. [x] Compile and test `homomorphic_encryption.v`

### Phase 3: Update DSDP (in dependency order)
9. [x] Update `dsdp_program.v` - parameterized by Party_HE_scheme, algebraic correctness proof
10. [x] Update `dsdp_program_alt_syntax.v` - same changes, custom syntax preserved
11. [x] Update `dsdp_correctness.v` - algebraic correctness using homomorphic properties
12. [x] Update `dsdp_entropy_trace.v` - trace definitions updated, entropy analysis simplified
13. [x] Update `dsdp_entropy.v` - added local party definitions, entropy analysis preserved
14. [x] Update `dsdp_security.v` - added local party definitions, security proofs preserved
15. [x] Compile full DSDP and verify all proofs pass

**Implementation Notes:**
- Core DSDP program files (`dsdp_program.v`, `dsdp_program_alt_syntax.v`, `dsdp_correctness.v`) use abstract `Party_HE_scheme`
- Entropy/security analysis files (`dsdp_entropy.v`, `dsdp_security.v`, `dsdp_entropy_trace.v`) keep concrete Z/pqZ types with local party definitions (they do deep entropy analysis that requires concrete type structure)
- Correctness proofs now use algebraic properties (`phe_Emul_eq_add`, `phe_Epow_eq_mul`) instead of computation
- Programs now require explicit randomness parameters for encryption calls

### Phase 4: Cleanup
16. [x] Update comments and documentation (inline in files)
17. [ ] Update the LaTeX paper patch if needed

---

## Open Questions

1. **Decryption**: Benaloh decryption requires discrete log. Should `phe_D` be:
   - Always return `None` (current approach)
   - Be an axiom/parameter
   - Use a different design?

2. **Message space compatibility**: DSDP uses `'F_m` (finite field). Benaloh uses `'Z_r`. Need to ensure compatibility or add coercions.

3. **Party type**: Currently hardcoded as `party` (Alice|Bob|Charlie|NoParty). Should the interface abstract over this?

---

## Risks

- **Proof breakage**: DSDP proofs may rely on specific properties of the ideal model
- **Type mismatches**: Different message/ciphertext spaces may cause issues
- **Compilation time**: More abstraction may slow compilation

---

## Decision Points for Review

1. Should `Party_HE_types` go in `he_sig.v` or a new file `party_he_sig.v`?
2. Should instances be in `homomorphic_encryption.v` or separate files?
3. Keep `Party_Enc_Types` as fallback or remove entirely?
4. How to handle the `'F_m` vs `'Z_r` message space difference?
