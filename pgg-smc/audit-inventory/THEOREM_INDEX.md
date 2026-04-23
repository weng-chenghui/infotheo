# pgg-smc theorem index

886 declarations across 67 in-scope files.

## `groups/` (188 decls)

### `groups/free_group_ball.v` (18)

| Line | Kind | Name | Tells us / Statement |
|---:|---|---|---|
| 53 | Lemma | `letter_inv_lt` | Lemma letter_inv_lt (i : nat) : i < alpha -> letter_inv i < alpha. |
| 56 | Lemma | `letter_invK` | Lemma letter_invK (i : nat) : i < alpha -> letter_inv (letter_inv i) = i. |
| 66 | Lemma | `letter_inv_neq` | Lemma letter_inv_neq (i : nat) : i < alpha -> letter_inv i != i. |
| 102 | Lemma | `sphere_size_0` | (* Key recurrence: each reduced word of length k extends to exactly (2r - 1) reduced words of length k+1 (all letters except the inverse of the last letter). The first letter has 2r choices. *) |
| 105 | Lemma | `sphere_size_1` | Lemma sphere_size_1 : sphere_size 1 = alpha. |
| 108 | Lemma | `sphere_size_S` | Lemma sphere_size_S (k : nat) : |
| 129 | Lemma | `ball_size_0` | Lemma ball_size_0 : ball_size 0 = 1. |
| 132 | Lemma | `ball_size_S` | Lemma ball_size_S (L : nat) : |
| 136 | Lemma | `ball_size_ge1` | Lemma ball_size_ge1 (L : nat) : 0 < ball_size L. |
| 148 | Lemma | `geom_series_nat` | (* (q - 1) * sum_{k=0}^{L} q^k = q^{L+1} - 1, for q >= 1 *) |
| 165 | Lemma | `geom_series_div` | (* Variant: sum_{k=0}^{L} q^k = (q^{L+1} - 1) / (q - 1), for q >= 2 *) |
| 189 | Lemma | `alpha_gt1` | Lemma alpha_gt1 : 1 < alpha. |
| 192 | Lemma | `q_gt0` | Lemma q_gt0 : 0 < q. |
| 196 | Lemma | `ball_size_sum` | (* ball_size r L = 1 + alpha * sum_{k=0}^{L-1} q^k *) |
| 205 | Lemma | `ball_size_formula` | (* Main formula, stated multiplicatively to avoid division: (q - 1) * (ball_size r L - 1) = alpha * (q^L - 1) *) |
| 219 | Lemma | `ball_size_div` | (* Division form for display: ball_size r L = 1 + alpha * (q^L - 1) / (q - 1) i.e., 1 + 2r * ((2r-1)^L - 1) / (2r - 2) *) |
| 230 | Lemma | `ball_size_lower` | (* Exponential lower bound: ball_size r L >= q^L = (2r-1)^L *) |
| 265 | Lemma | `search_space_exp_growth` | (* For word-eval injective generators with branching factor Tg = 2r, the search space is Tg^L by weval_inj_search_space. The ball_size gives the size when restricted to reduced words. Key insight: wo… |

### `groups/pgg_raag.v` (32)

| Line | Kind | Name | Tells us / Statement |
|---:|---|---|---|
| 94 | Lemma | `foata_depth_at_ext` | (* Extensionality: foata_nf depends only on crel values at word elements *) |
| 105 | Lemma | `foata_pairs_ext` | Lemma foata_pairs_ext comm1 comm2 prev w : |
| 123 | Lemma | `foata_nf_ext` | Lemma foata_nf_ext comm1 comm2 w : |
| 132 | Lemma | `leq_sum_sub` | Lemma leq_sum_sub (I : finType) (P Q : pred I) (f : I -> nat) : |
| 213 | Lemma | `swap_word_tnth` | Lemma swap_word_tnth L' (k : 'I_L') (w : pgg_word M L'.+1) |
| 249 | Lemma | `word_eval_adj_swap` | (* Swapping adjacent commuting generators preserves word_eval *) |
| 354 | Lemma | `word_eval_trace` | Lemma word_eval_trace L (w1 w2 : pgg_word M L) : |
| 367 | Lemma | `adj_swap_sym_sym` | (* adj_swap_sym is symmetric *) |
| 371 | Lemma | `search_space_le_traces` | (* Search space bounded by number of traces *) |
| 389 | Lemma | `raag_weval_inj_search_space` | Lemma raag_weval_inj_search_space L : |
| 414 | Lemma | `n_traces_le_words` | (* Upper bound: n_traces <= Tg^L *) |
| 421 | Lemma | `search_space_chain` | Lemma search_space_chain L : |
| 432 | Lemma | `empty_comm_adj_swap` | (* Empty comm -> n_traces = Tg^L (free case) *) |
| 444 | Lemma | `empty_comm_traces` | Lemma empty_comm_traces L : |
| 479 | Lemma | `swap_word_perm` | (* --- Helper: adj_swap preserves perm_eq --- *) |
| 505 | Lemma | `adj_swap_perm` | Lemma adj_swap_perm L (w1 w2 : pgg_word M L) : |
| 513 | Lemma | `trace_perm` | Lemma trace_perm L (w1 w2 : pgg_word M L) : |
| 526 | Lemma | `not_sorted_descent` | (* --- Helper: unsorted sequence has adjacent descent --- *) |
| 547 | Lemma | `inv_count_zero_sorted` | Lemma inv_count_zero_sorted L (w : pgg_word M L) : |
| 587 | Lemma | `inv_count_swap_lt` | (* Swapping an adjacent descent decreases inv_count *) |
| 700 | Lemma | `full_comm_connect_sorted` | (* --- Full comm: every word connects to a sorted word --- *) |
| 749 | Lemma | `full_comm_traces` | (* Full comm -> n_traces = 'C(L + Tg.-1, Tg.-1) (abelian case) *) |
| 820 | Lemma | `full_comm_trace_iff_perm` | Lemma full_comm_trace_iff_perm L (w1 w2 : pgg_word M L) : |
| 847 | Lemma | `indep_adj_swap_false` | (* Independent set lower bound on traces *) |
| 865 | Lemma | `indep_set_traces_lb` | Lemma indep_set_traces_lb (I : {set 'I_Tg}) (L : nat) : |
| 950 | Lemma | `word_eval_perm_eq` | Lemma word_eval_perm_eq L (w1 w2 : pgg_word M L) : |
| 962 | Lemma | `indep_set_singleton_traces` | (* Independent set generators have singleton trace classes: no two distinct I-words are trace-equivalent. *) |
| 996 | Lemma | `indep_set_word_eval_inj` | (* Charney's theorem (finite analog): independent set generators with raag_weval_inj give word_eval injectivity on I-words *) |
| 1019 | Lemma | `raag_weval_inj1` | Lemma raag_weval_inj1 : @weval_inj R 1. |
| 1022 | Lemma | `raag_search_space_1` | Lemma raag_search_space_1 : @search_space R 1 = Tg. |
| 1896 | Lemma | `val_tnth_nth` | Lemma val_tnth_nth n (w : n.-tuple 'I_Tg) (i : 'I_n) : |
| 2256 | Lemma | `n_traces_of_natB` | (* ------------------------------------------------------------------ *) |

### `groups/pgg_raag_clique.v` (103)

| Line | Kind | Name | Tells us / Statement |
|---:|---|---|---|
| 141 | Lemma | `star3_cc0` | (* ---- Clique counts for star K_{1,3} (4 generators) ---- *) |
| 144 | Lemma | `star3_cc1` | Lemma star3_cc1 : clique_count 4 1 (star_comm_nat 3) = 4. |
| 147 | Lemma | `star3_cc2` | Lemma star3_cc2 : clique_count 4 2 (star_comm_nat 3) = 3. |
| 150 | Lemma | `star3_cc3` | Lemma star3_cc3 : clique_count 4 3 (star_comm_nat 3) = 0. |
| 153 | Lemma | `star3_cc4` | Lemma star3_cc4 : clique_count 4 4 (star_comm_nat 3) = 0. |
| 160 | Lemma | `complete3_cc0` | (* ---- Clique counts for complete graph on 3 generators ---- *) |
| 163 | Lemma | `complete3_cc1` | Lemma complete3_cc1 : clique_count 3 1 complete_comm_nat = 3. |
| 166 | Lemma | `complete3_cc2` | Lemma complete3_cc2 : clique_count 3 2 complete_comm_nat = 3. |
| 169 | Lemma | `complete3_cc3` | Lemma complete3_cc3 : clique_count 3 3 complete_comm_nat = 1. |
| 176 | Lemma | `empty3_cc0` | (* ---- Clique counts for empty graph on 3 generators ---- *) |
| 179 | Lemma | `empty3_cc1` | Lemma empty3_cc1 : clique_count 3 1 (fun _ _ => false) = 3. |
| 182 | Lemma | `empty3_cc2` | Lemma empty3_cc2 : clique_count 3 2 (fun _ _ => false) = 0. |
| 189 | Lemma | `path3_cc0` | (* ---- Clique counts for path on 3 generators ---- *) |
| 192 | Lemma | `path3_cc1` | Lemma path3_cc1 : clique_count 3 1 path_comm_nat = 3. |
| 195 | Lemma | `path3_cc2` | Lemma path3_cc2 : clique_count 3 2 path_comm_nat = 1. |
| 198 | Lemma | `path3_cc3` | Lemma path3_cc3 : clique_count 3 3 path_comm_nat = 0. |
| 205 | Lemma | `star3_ct0` | (* ---- Trace counts: star K_{1,3} ---- *) |
| 208 | Lemma | `star3_ct1` | Lemma star3_ct1 : clique_traces 4 1 (star_comm_nat 3) = 4. |
| 211 | Lemma | `star3_ct2` | Lemma star3_ct2 : clique_traces 4 2 (star_comm_nat 3) = 13. |
| 214 | Lemma | `star3_ct3` | Lemma star3_ct3 : clique_traces 4 3 (star_comm_nat 3) = 40. |
| 218 | Lemma | `star3_ntB0` | (* Cross-check with n_traces_natB *) |
| 221 | Lemma | `star3_ntB1` | Lemma star3_ntB1 : n_traces_natB 4 1 (star_comm_nat 3) = 4. |
| 224 | Lemma | `star3_ntB2` | Lemma star3_ntB2 : n_traces_natB 4 2 (star_comm_nat 3) = 13. |
| 227 | Lemma | `star3_ntB3` | Lemma star3_ntB3 : n_traces_natB 4 3 (star_comm_nat 3) = 40. |
| 232 | Lemma | `free3_ct0` | (* ---- Trace counts: free group (3 generators) ---- *) |
| 235 | Lemma | `free3_ct1` | Lemma free3_ct1 : clique_traces 3 1 (fun _ _ => false) = 3. |
| 238 | Lemma | `free3_ct2` | Lemma free3_ct2 : clique_traces 3 2 (fun _ _ => false) = 9. |
| 241 | Lemma | `free3_ct3` | Lemma free3_ct3 : clique_traces 3 3 (fun _ _ => false) = 27. |
| 245 | Lemma | `free3_ntB2` | (* Cross-check *) |
| 250 | Lemma | `abelian3_ct0` | (* ---- Trace counts: abelian (3 generators) ---- *) |
| 253 | Lemma | `abelian3_ct1` | Lemma abelian3_ct1 : clique_traces 3 1 complete_comm_nat = 3. |
| 256 | Lemma | `abelian3_ct2` | Lemma abelian3_ct2 : clique_traces 3 2 complete_comm_nat = 6. |
| 259 | Lemma | `abelian3_ct3` | Lemma abelian3_ct3 : clique_traces 3 3 complete_comm_nat = 10. |
| 265 | Lemma | `abelian3_ntB2` | (* Cross-check *) |
| 268 | Lemma | `abelian3_ntB3` | Lemma abelian3_ntB3 : n_traces_natB 3 3 complete_comm_nat = 10. |
| 273 | Lemma | `path3_ct0` | (* ---- Trace counts: path (3 generators) ---- *) |
| 276 | Lemma | `path3_ct1` | Lemma path3_ct1 : clique_traces 3 1 path_comm_nat = 3. |
| 279 | Lemma | `path3_ct2` | Lemma path3_ct2 : clique_traces 3 2 path_comm_nat = 8. |
| 282 | Lemma | `path3_ct3` | Lemma path3_ct3 : clique_traces 3 3 path_comm_nat = 21. |
| 286 | Lemma | `path3_ntB2` | (* Cross-check *) |
| 289 | Lemma | `path3_ntB3` | Lemma path3_ntB3 : n_traces_natB 3 3 path_comm_nat = 21. |
| 298 | Lemma | `subseqs_k_size` | (* --- Helper lemma: size of elements in subseqs_k --- *) |
| 310 | Lemma | `filter_pred1T` | (* --- Empty graph: clique_count Tg 0 = 1, clique_count Tg 1 = Tg --- *) |
| 314 | Lemma | `all_pairs_comm_nil` | Lemma all_pairs_comm_nil comm : all_pairs_comm_sorted comm [::] = true. |
| 317 | Lemma | `subseqs_k0` | Lemma subseqs_k0 s : subseqs_k 0 s = [:: [::]]. |
| 320 | Lemma | `clique_count0` | Lemma clique_count0 Tg comm : clique_count Tg 0 comm = 1. |
| 326 | Lemma | `subseqs_k1` | Lemma subseqs_k1 s : subseqs_k 1 s = [seq [:: x] \| x <- s]. |
| 332 | Lemma | `empty_clique_count1` | Lemma empty_clique_count1 Tg : |
| 340 | Lemma | `subseqs_k_subseq` | Lemma subseqs_k_subseq k s t : t \in subseqs_k k s -> subseq t s. |
| 350 | Lemma | `mem_subseqs_k` | Lemma mem_subseqs_k k s t : |
| 371 | Lemma | `all_pairs_false_neq` | Lemma all_pairs_false_neq (s : seq nat) (a b : nat) : |
| 381 | Lemma | `empty_clique_countk` | Lemma empty_clique_countk Tg k : |
| 404 | Lemma | `sumn_map_0` | (* Helper: sumn of all-zero map is 0 *) |
| 413 | Lemma | `clique_step_free` | (* clique_step for empty graph = Tg * previous element *) |
| 444 | Lemma | `clique_traces_aux_inv` | (* Invariant: clique_traces_aux extends memo with powers of Tg *) |
| 472 | Lemma | `clique_traces_free` | Lemma clique_traces_free Tg L : |
| 488 | Lemma | `all_pairs_complete` | (* All distinct pairs commute in a complete graph *) |
| 497 | Lemma | `size_subseqs_k` | Lemma size_subseqs_k k s : |
| 506 | Lemma | `complete_clique_count` | Lemma complete_clique_count Tg k : |
| 534 | Lemma | `filter_iota_head_even` | Lemma filter_iota_head_even L : |
| 538 | Lemma | `filter_iota_head_odd` | Lemma filter_iota_head_odd L : |
| 542 | Lemma | `sumn_filter_map` | Lemma sumn_filter_map {A : eqType} (p : pred A) (f : A -> nat) (s : seq A) : |
| 547 | Lemma | `spos_unfold` | Lemma spos_unfold n r L : |
| 552 | Lemma | `sneg_unfold` | Lemma sneg_unfold n r L : |
| 557 | Lemma | `spos_split` | Lemma spos_split n r L : |
| 566 | Lemma | `sneg_eq_tail` | Lemma sneg_eq_tail n r L : |
| 576 | Lemma | `sumn_map_add` | Lemma sumn_map_add {A : Type} (f g : A -> nat) (s : seq A) : |
| 581 | Lemma | `sumn_map_split` | Lemma sumn_map_split (f g h : nat -> nat) m M : |
| 591 | Lemma | `sumn_map_eq` | Lemma sumn_map_eq (f g : nat -> nat) m M : |
| 600 | Lemma | `sumn_shift_even_to_odd_gen` | Lemma sumn_shift_even_to_odd_gen (g : nat -> nat) m M : |
| 608 | Lemma | `sumn_shift_odd_to_even_gen` | Lemma sumn_shift_odd_to_even_gen (g : nat -> nat) m M : |
| 616 | Lemma | `sumn_iota_map0` | Lemma sumn_iota_map0 (f : nat -> nat) m M : |
| 625 | Lemma | `spos_L0` | Lemma spos_L0 n r : spos n r 0 = 'C(r, r). |
| 628 | Lemma | `sneg_L0` | Lemma sneg_L0 n r : sneg n r 0 = 0. |
| 631 | Lemma | `spos0` | Lemma spos0 r L : spos 0 r L = 'C(L + r, r). |
| 640 | Lemma | `sneg0` | Lemma sneg0 r L : sneg 0 r L = 0. |
| 647 | Lemma | `binSn` | Lemma binSn n k : 0 < k -> |
| 653 | Lemma | `spos_pascal_core` | (* Core identity for spos_pascal: decomposes even-parity sum using Pascal's rule C(n+1,k) = C(n,k) + C(n,k-1) and reindexing. *) |
| 685 | Lemma | `sneg_pascal_core` | (* Core identity for sneg_pascal: decomposes odd-parity sum using Pascal's rule and reindexing. *) |
| 715 | Lemma | `spos_pascal` | Lemma spos_pascal n r L : |
| 722 | Lemma | `sneg_pascal` | Lemma sneg_pascal n r L : |
| 729 | Lemma | `spos_inv` | Lemma spos_inv n r L : n <= r -> |
| 758 | Lemma | `spos_eq_sneg` | Lemma spos_eq_sneg n L : |
| 766 | Lemma | `pos_eq_sneg_range` | Lemma pos_eq_sneg_range Tg r L : |
| 772 | Lemma | `neg_eq_spos_sub` | Lemma neg_eq_spos_sub Tg r L : |
| 778 | Lemma | `clique_step_abelian` | Lemma clique_step_abelian Tg memo : |
| 807 | Lemma | `clique_traces_aux_inv_abelian` | Lemma clique_traces_aux_inv_abelian Tg n memo : |
| 830 | Lemma | `clique_traces_abelian` | Lemma clique_traces_abelian Tg L : |
| 850 | Lemma | `free_growth_check` | (* Free: Tg^L *) |
| 855 | Lemma | `abelian_growth_check` | (* Abelian: C(L+Tg-1, Tg-1) for Tg=3 gives C(L+2,2) *) |
| 860 | Lemma | `star3_growth_check` | (* Star K_{1,3}: m_L = (3^{L+1}-1)/2 *) |
| 866 | Lemma | `path3_growth_check` | (* Path on 3: m_L satisfies m_L = 3*m_{L-1} - m_{L-2} *) |
| 895 | Lemma | `cartier_foata_check_free3` | (* vm_compute verification of cartier_foata for all concrete instances *) |
| 901 | Lemma | `cartier_foata_check_abelian3` | Lemma cartier_foata_check_abelian3 : |
| 907 | Lemma | `cartier_foata_check_path3` | Lemma cartier_foata_check_path3 : |
| 913 | Lemma | `cartier_foata_check_star3` | Lemma cartier_foata_check_star3 : |
| 919 | Lemma | `cartier_foata_check_abelian4` | Lemma cartier_foata_check_abelian4 : |
| 963 | Lemma | `table_T4_free` | (* Verify the T=4 comparison table *) |
| 971 | Lemma | `table_T4_path` | Lemma table_T4_path : |
| 982 | Lemma | `table_T4_star3` | (* Note: path P_4 and star K_{1,3} have the same clique polynomial P(z) = 1 - 4z + 3z^2 = (1-z)(1-3z), hence the same trace counts. By the Cartier-Foata theorem, the trace-counting generating functio… |
| 987 | Lemma | `table_T4_abelian` | Lemma table_T4_abelian : |
| 993 | Lemma | `path4_ntB_check` | (* Cross-check: n_traces_natB for path P_4 matches the clique prediction *) |
| 999 | Lemma | `star3_ntB_check` | (* Cross-check: n_traces_natB for star K_{1,3} matches *) |

### `groups/pgg_raag_path.v` (14)

| Line | Kind | Name | Tells us / Statement |
|---:|---|---|---|
| 49 | Lemma | `path_gen_tupleE` | Lemma path_gen_tupleE (i : 'I_T) : tnth path_gen_tuple i = path_gen i. |
| 54 | Lemma | `path_gen_inj` | (* --- Generator injectivity --- *) |
| 99 | Lemma | `path_comm_sym` | Lemma path_comm_sym : symmetric path_comm. |
| 102 | Lemma | `path_comm_irrefl` | Lemma path_comm_irrefl : irreflexive path_comm. |
| 105 | Lemma | `path_comm_dist2` | Lemma path_comm_dist2 (i j : 'I_T) : |
| 110 | Lemma | `path_dist_neq` | Lemma path_dist_neq (a b : nat) : (a - b) + (b - a) >= 2 -> a != b. |
| 113 | Lemma | `path_dist_neqS` | Lemma path_dist_neqS (a b : nat) : (a - b) + (b - a) >= 2 -> a != b.+1. |
| 121 | Lemma | `path_Hcomm` | Lemma path_Hcomm : forall i j : 'I_T, |
| 138 | Lemma | `path_gen_inj_sigmas` | (* --- RAAG instance wrapper lemmas --- *) |
| 142 | Lemma | `path_Hcomm_sigmas` | Lemma path_Hcomm_sigmas : forall i j : 'I_T, |
| 150 | Lemma | `path_adj_noncommute` | (* --- Non-abelianity (via generic) --- *) |
| 171 | Lemma | `path_G_nonabelian` | Lemma path_G_nonabelian : 0 < m -> |
| 186 | Lemma | `path_indep_pair` | (* --- Independent set: any adjacent pair {i, i+1} --- *) |
| 204 | Lemma | `path_traces_lb` | Lemma path_traces_lb (L : nat) : 0 < m -> |

### `groups/pgg_weval_inj.v` (21)

| Line | Kind | Name | Tells us / Statement |
|---:|---|---|---|
| 76 | Lemma | `map_uniq_injective` | Lemma map_uniq_injective (T1 T2 : eqType) (f : T1 -> T2) (xs : seq T1) (a b : T1) : |
| 92 | Lemma | `mem_all_words` | Lemma mem_all_words Tg L (w : seq nat) : |
| 122 | Lemma | `eval_foldl_agree` | (* Key lemma 1: foldl on nat matches foldl on ordinals *) |
| 130 | Lemma | `word_eval_foldl` | (* Key lemma 2: word_eval equals foldl over the tuple *) |
| 153 | Lemma | `eval_word_agree` | (* Combine: eval_word_nat agrees with word_eval *) |
| 161 | Lemma | `map_val_tuple_inj` | (* map val is injective on pgg_word *) |
| 166 | Lemma | `map_val_in_all_words` | (* map val of a pgg_word is in all_words *) |
| 175 | Lemma | `weval_inj_of_natB` | (* Main reflection lemma *) |
| 202 | Lemma | `weval_inj_inst_search_space` | Lemma weval_inj_inst_search_space : @search_space M L = m.+1 ^ L. |
| 225 | Lemma | `oc_s0K` | Lemma oc_s0K : cancel oc_s0_fun oc_s0_inv. |
| 228 | Lemma | `oc_s0E` | Lemma oc_s0E x : oc_s0 x = oc_s0_fun x. Proof. by rewrite permE. Qed. |
| 239 | Lemma | `oc_s1K` | Lemma oc_s1K : cancel oc_s1_fun oc_s1_inv. |
| 242 | Lemma | `oc_s1E` | Lemma oc_s1E x : oc_s1 x = oc_s1_fun x. Proof. by rewrite permE. Qed. |
| 245 | Lemma | `oc_sigmas_size` | (* Generator tuple *) |
| 250 | Lemma | `oc_sigmasE` | Lemma oc_sigmasE (i : 'I_2) : tnth oc_sigmas i = |
| 265 | Lemma | `oc_gens_agree` | Lemma oc_gens_agree (i : 'I_2) (x : 'I_oc_N) : |
| 273 | Lemma | `oc_s0_order3` | (* Order 3 *) |
| 279 | Lemma | `oc_s1_order3` | Lemma oc_s1_order3 : (oc_s1 ^+ 3 = 1 :> {perm 'I_oc_N})%g. |
| 286 | Lemma | `oc_noncommute` | (* Non-commutativity *) |
| 293 | Lemma | `oc_weval_inj2` | (* Word-eval injectivity via nat-level boolean decision + vm_compute *) |
| 300 | Lemma | `oc_search_space_2` | (* Search space instantiation *) |

## `instances/` (217 decls)

### `instances/abelian/abelian_word_collapse.v` (21)

| Line | Kind | Name | Tells us / Statement |
|---:|---|---|---|
| 50 | Lemma | `freq_vec_sum` | (* Sum of frequencies equals word length *) |
| 63 | Lemma | `abelian_prod_in` | (* only Monoid.law. We reprove them under a runtime abelian hypothesis. *) |
| 73 | Lemma | `abelian_bigID` | Lemma abelian_bigID (Habel : abelian G) |
| 90 | Lemma | `abelian_big_union` | Lemma abelian_big_union (Habel : abelian G) |
| 107 | Lemma | `abelian_partition_big` | Lemma abelian_partition_big (Habel : abelian G) |
| 135 | Lemma | `big_const_expg` | Lemma big_const_expg (n : nat) (P : pred 'I_n) (g : gT) : |
| 147 | Lemma | `abelian_word_eval` | (* Main theorem: abelian word evaluation depends only on frequency vector. In an abelian group, the product \prod_i sigma_{w_i} can be rearranged by collecting equal generators: sigma_j^{count of j i… |
| 165 | Lemma | `freq_vec_det` | (* Two words with the same frequency vector give the same group element *) |
| 198 | Lemma | `freq_vec_lt` | (* The frequency vector of a word, as a bounded function *) |
| 208 | Lemma | `freq_vec_ffun_val` | Lemma freq_vec_ffun_val (w : pgg_word M L) (j : 'I_Tg) : |
| 212 | Lemma | `freq_vec_ffun_in` | Lemma freq_vec_ffun_in (w : pgg_word M L) : |
| 224 | Lemma | `abelian_word_eval_freq` | Lemma abelian_word_eval_freq (w : pgg_word M L) : |
| 234 | Lemma | `abelian_achievable_sub` | (* Search space bound: achievable elements are at most the image of freq_vecs *) |
| 244 | Lemma | `abelian_search_space_le` | Lemma abelian_search_space_le : |
| 281 | Lemma | `ffun_to_tupleK` | Lemma ffun_to_tupleK : cancel ffun_to_tuple tuple_to_ffun. |
| 284 | Lemma | `tuple_to_ffunK` | Lemma tuple_to_ffunK : cancel tuple_to_ffun ffun_to_tuple. |
| 287 | Lemma | `sum_ffun_to_tuple` | Lemma sum_ffun_to_tuple (f : {ffun 'I_r.+1 -> 'I_L.+1}) : |
| 294 | Lemma | `card_compositions` | Lemma card_compositions : |
| 322 | Lemma | `freq_vecs_eq_compositions` | (* freq_vecs is exactly compositions for r = pgg_ngens' M *) |
| 326 | Lemma | `card_freq_vecs` | Lemma card_freq_vecs : |
| 333 | Theorem | `abelian_search_space_bound` | (* Combined bound *) |

### `instances/abelian/pgg_abelian.v` (16)

| Line | Kind | Name | Tells us / Statement |
|---:|---|---|---|
| 51 | Lemma | `shift_unshiftK` | Lemma shift_unshiftK : cancel shift_fun unshift_fun. |
| 58 | Lemma | `shift_fun_inj` | Lemma shift_fun_inj : injective shift_fun. |
| 63 | Lemma | `ncycleE` | Lemma ncycleE (i : 'I_N) : |
| 68 | Lemma | `ncycle_iter` | (* Iterated application of the N-cycle *) |
| 79 | Lemma | `ncycle_expN` | Lemma ncycle_expN : (ncycle ^+ N = 1 :> {perm 'I_N})%g. |
| 86 | Lemma | `ncycle_order` | (* Full order of the canonical N-cycle *) |
| 113 | Lemma | `incl_morphM` | (* Inclusion morphism: identity on the subgroup *) |
| 126 | Lemma | `tnth_cyclic_sigmas` | Lemma tnth_cyclic_sigmas (i : 'I_1) : tnth cyclic_sigmas i = sigma. |
| 129 | Lemma | `cyclic_sigmas_gen` | Lemma cyclic_sigmas_gen : |
| 142 | Lemma | `cyclic_G_abelian` | (* Key property: cyclic groups are abelian *) |
| 146 | Lemma | `cyclic_word_eval` | (* Word evaluation in the cyclic (1-generator) instance *) |
| 154 | Lemma | `cyclic_search_space_le` | (* Search space collapse: at most #[sigma] distinct elements reachable *) |
| 167 | Lemma | `cyclic_starts_2_uniq` | Lemma cyclic_starts_2_uniq : uniq cyclic_starts_2. |
| 208 | Lemma | `dt_even_lt` | Lemma dt_even_lt (i : 'I_Tg) : (val i).*2 < N. |
| 211 | Lemma | `dt_odd_lt` | Lemma dt_odd_lt (i : 'I_Tg) : (val i).*2.+1 < N. |
| 219 | Lemma | `dt_gen_tupleE` | Lemma dt_gen_tupleE (i : 'I_Tg) : tnth dt_gen_tuple i = dt_gen i. |

### `instances/abelian/rigidity_abelian_instance.v` (6)

| Line | Kind | Name | Tells us / Statement |
|---:|---|---|---|
| 72 | Lemma | `abel_s1_neq_s2` | (* Generators are distinct permutations *) |
| 80 | Lemma | `abel_sigmas_distinct` | Lemma abel_sigmas_distinct : |
| 102 | Lemma | `abel_weval_inj1` | (* Word-eval injectivity at L=1: follows from generator injectivity *) |
| 109 | Lemma | `abel_perm_endpoint_inj1` | (* Direct endpoint SecurityWitness at L=1. Epsilon = 2*(4-2)/4 = 1.0, tighter than DPI bound 44/24 ≈ 1.83. Proof: (01) and (23) have disjoint support, so they map every sheet to distinct values. *) |
| 181 | Lemma | `abel_complexity` | (* Derived properties *) |
| 185 | Lemma | `abel_tradeoff` | Lemma abel_tradeoff : |

### `instances/denboer1989/five_card_group.v` (7)

| Line | Kind | Name | Tells us / Statement |
|---:|---|---|---|
| 80 | Lemma | `fc_sigmaK` | Lemma fc_sigmaK : cancel fc_sigma_fun fc_sigma_inv. |
| 98 | Lemma | `fc_gK` | Definition fc_g_inv := fc_g_fun. (* g is its own inverse *) |
| 119 | Lemma | `fc_g_involution` | (** Involution properties *) |
| 137 | Lemma | `fc_sigmasE` | Lemma fc_sigmasE (i : 'I_1) : tnth fc_sigmas i = fc_sigma. |
| 140 | Lemma | `fc_gens_agree` | Lemma fc_gens_agree (i : 'I_1) (x : 'I_5) : |
| 149 | Lemma | `fc_weval_inj1` | (** Word-eval injectivity at L=1: trivially true since there's only 1 generator and it is not the identity. *) |
| 158 | Lemma | `fc_weval_inj4` | (** Word-eval injectivity at L=4: the 4 words [0], [0,0], [0,0,0], [0,0,0,0] evaluate to sigma, sigma^2, sigma^3, sigma^4, all distinct since sigma has order 5. *) |

### `instances/denboer1989/five_card_pismc.v` (7)

| Line | Kind | Name | Tells us / Statement |
|---:|---|---|---|
| 110 | Lemma | `fc_ts_correct` | (** Correctness: reconstruction of valid shares returns the secret. *) |
| 115 | Lemma | `fc_ts_encode_valid` | (** Canonical encoding is valid. *) |
| 149 | Lemma | `fc_witness_size` | Lemma fc_witness_size (s : bool) (i : nat) (v : bool) : |
| 156 | Lemma | `fc_witness_val` | Lemma fc_witness_val s (i : 'I_5) v : |
| 160 | Lemma | `fc_witness_valid` | Lemma fc_witness_valid s (i : 'I_5) v : |
| 167 | Lemma | `fc_witness_tnth` | Lemma fc_witness_tnth s (i : 'I_5) v : |
| 178 | Lemma | `fc_ts_private` | (** Privacy: any single card position (\|C\| < 2) can be matched by shares valid for a different secret. In the five-card trick, each individual card position is compatible with both AND=0 and AND=1, b… |

### `instances/denboer1989/five_card_program.v` (4)

| Line | Kind | Name | Tells us / Statement |
|---:|---|---|---|
| 68 | Lemma | `fc_arrange_size` | Lemma fc_arrange_size (a b : bool) : size (fc_arrange a b) = 5. |
| 100 | Lemma | `fc_correct` | (** Three consecutive hearts appear in the shuffled arrangement iff both input bits are 1. Proved by exhaustive computation over 4 (bool x bool) * 5 (shift) = 20 cases. *) |
| 108 | Lemma | `fc_arrange_size_proof` | (******************************************************************************) |
| 117 | Lemma | `fc_sigma_funE` | (** [fc_sigma] applied to an ordinal equals the plain function [fc_sigma_fun] from [five_card_group.v]. *) |

### `instances/denboer1989/five_card_security.v` (22)

| Line | Kind | Name | Tells us / Statement |
|---:|---|---|---|
| 56 | Lemma | `fc_sigma_perm` | (******************************************************************************) |
| 60 | Lemma | `fc_sigma5` | (** sigma^5 = 1 by direct computation *) |
| 68 | Lemma | `fc_sigma_in_G` | (** sigma is in G *) |
| 76 | Lemma | `fc_sigma_pow_in_G` | (** All powers of sigma are in G *) |
| 85 | Lemma | `fc_pow0` | (** We compute sigma^k(s) for k=0..4 and all s by direct expansion. *) |
| 88 | Lemma | `fc_pow1` | Lemma fc_pow1 (s : 'I_5) : val ((sigma ^+ 1) s) = (val s).+1 %% 5. |
| 95 | Lemma | `fc_reach` | (** For each target x, we exhibit the power of sigma that maps s to x. *) |
| 115 | Lemma | `fc_G_pos` | (******************************************************************************) |
| 122 | Lemma | `fc_orbit_full` | (******************************************************************************) |
| 138 | Lemma | `fc_pow_fix_zero` | (** Helper: sigma^k fixes any sheet s implies k is a multiple of 5. *) |
| 150 | Lemma | `fc_fix_imp_id` | (** Key: any element of G that fixes a sheet must be the identity. *) |
| 167 | Lemma | `fc_eval_inj` | Lemma fc_eval_inj (s : 'I_5) : |
| 184 | Lemma | `fc_rho_id` | (** For Gen_PGGTypes, pgg_rho = gen_incl_morph = id on {perm 'I_5}. So the image rhoG = G, and all G-level properties lift to rhoG. *) |
| 189 | Lemma | `fc_rhoG_eq` | Lemma fc_rhoG_eq : [set rho x \| x in G] = G. |
| 200 | Lemma | `fc_rhoG_pos` | (******************************************************************************) |
| 203 | Lemma | `fc_rhoG_regular` | Lemma fc_rhoG_regular (s : 'I_5) : |
| 210 | Lemma | `fc_rhoG_trans` | Lemma fc_rhoG_trans (s : 'I_5) : |
| 223 | Lemma | `fc_eps_zero` | Lemma fc_eps_zero : sw_bound_eps fc_security_uniform = GRing.zero. |
| 245 | Lemma | `fc_HN5` | (* Sheet count for FiveCard_M: 5 sheets (pgg_N' = 4). Verified definitionally since FiveCard_M = Gen_PGGTypes 0 3 fc_sigmas, so pgg_N' = 4. *) |
| 265 | Lemma | `fc_genus0_automorphism` | (** fc_genus0_automorphism — discharges [genus0_automorphism_bound] for the FiveCard instance by reducing to the concrete PGL bound [fc_genus0_pgl]. Kind: helper. Why: required to instantiate [fc_thr… |
| 278 | Lemma | `fc_tradeoff` | (* Verify tradeoff: genus-0 regime with T = k *) |
| 294 | Lemma | `fc_ts_recon_correct` | (** Protocol reconstruction correctness: named instance-level re-export of [ar_protocol_correct]. *) |

### `instances/denboer1989/five_card_session_types.v` (3)

| Line | Kind | Name | Tells us / Statement |
|---:|---|---|---|
| 46 | Lemma | `fc_dtype_eqP` | Lemma fc_dtype_eqP : Equality.axiom fc_dtype_eqb. |
| 71 | Lemma | `from_card_FC_card` | Lemma from_card_FC_card (v : bool) : |
| 75 | Lemma | `from_commit_FC_commit` | Lemma from_commit_FC_commit (cs : seq bool) : |

### `instances/kim2025/five_card_kim.v` (20)

| Line | Kind | Name | Tells us / Statement |
|---:|---|---|---|
| 118 | Lemma | `fc_kim_sigmasE` | (** Each generator sigma^k acts as expected *) |
| 163 | Lemma | `kim_weight_gt0` | Lemma kim_weight_gt0 (k : 'I_5) : 0 < kim_weight_fun k. |
| 177 | Lemma | `kim_weight_ge0` | Lemma kim_weight_ge0 : forall k : 'I_5, 0 <= kim_weight_fun k. |
| 180 | Lemma | `kim_weight_sum1` | Lemma kim_weight_sum1 : \sum_(k in 'I_5) kim_weight_fun k = 1. |
| 217 | Lemma | `kim_weight_distE` | Lemma kim_weight_distE (k : 'I_5) : |
| 254 | Lemma | `fc_kim_schreier_diag` | (** Diagonal entries: Q(x,x) = W(0) = 1/5 - eps *) |
| 270 | Lemma | `fc_kim_row_stochastic` | (** Row stochastic: inherited from generic Schreier lemma *) |
| 275 | Lemma | `fc_kim_col_stochastic` | (** Column stochastic: for circulant matrices, column sums = row sums *) |
| 296 | Lemma | `fc_kim_schreier_offdiag` | (** Off-diagonal entries: Q(x,y) = W(y-x mod 5) = 1/5 + eps/4 for x != y *) |
| 312 | Lemma | `fc_kim_doubly_stochastic` | (** Doubly stochastic *) |
| 351 | Lemma | `kim_slev_ge0` | Lemma kim_slev_ge0 : 0 <= kim_slev. |
| 354 | Lemma | `kim_slev_lt1` | Lemma kim_slev_lt1 : kim_slev < 1. |
| 367 | Lemma | `kim_spectral_gap_pos` | Lemma kim_spectral_gap_pos : 0 < kim_spectral_gap. |
| 370 | Lemma | `kim_spectral_gap_le1` | Lemma kim_spectral_gap_le1 : kim_spectral_gap <= 1. |
| 379 | Lemma | `kim_spectral_convergence` | (** Spectral convergence bound. Proved via the uniform-off-diagonal convergence theorem (unif_offdiag_convergence from pgg_schreier_weighted.v): Kim's circulant Schreier matrix has constant diagonal … |
| 425 | Lemma | `kim_var_dist_exact` | (** Exact variation distance via the uniform-off-diagonal identity. The proof mirrors kim_spectral_convergence but calls unif_offdiag_var_dist (equality) instead of unif_offdiag_convergence (inequali… |
| 477 | Lemma | `kim_slev_at_zero` | (** When eps = 0, the bias disappears and we recover the uniform case *) |
| 480 | Lemma | `kim_bound_at_zero` | Lemma kim_bound_at_zero (L : nat) : |
| 486 | Lemma | `kim_security_at_zero` | Lemma kim_security_at_zero (L : nat) : |
| 515 | Lemma | `fc_kim_security_bound` | (** The security bound for L shuffles: var_dist <= sqrt(5) * ((5/4)*\|eps\|)^L *) |

### `instances/kim2025/rigidity_kim_instance.v` (5)

| Line | Kind | Name | Tells us / Statement |
|---:|---|---|---|
| 66 | Lemma | `kim_HN5` | (* Sheet count for M_kim: 5 sheets (pgg_N' = 4). Verified definitionally since M_kim = Gen_PGGTypes 4 3 fc_kim_sigmas, so pgg_N' = 4. *) |
| 85 | Lemma | `kim_genus0_automorphism` | (** kim_genus0_automorphism — discharges [genus0_automorphism_bound] for the Kim 2025 instance by reducing to the concrete PGL bound [kim_genus0_pgl]. Kind: helper. Why: required to instantiate [kim_… |
| 99 | Lemma | `kim_complexity` | (* Derived properties *) |
| 103 | Lemma | `kim_tradeoff` | Lemma kim_tradeoff (L : nat) : |
| 119 | Lemma | `kim_ts_recon_correct` | (** Protocol reconstruction correctness: named instance-level re-export of [ar_protocol_correct]. *) |

### `instances/s5/pgg_raag_s5.v` (5)

| Line | Kind | Name | Tells us / Statement |
|---:|---|---|---|
| 42 | Lemma | `s5_gens_agree` | Lemma s5_gens_agree (i : 'I_4) (x : 'I_5) : |
| 51 | Lemma | `s5_weval_inj1` | (* Word-eval injectivity via nat-level boolean check + vm_compute *) |
| 60 | Lemma | `s5_nt_L1` | (* N=5, Tg=4, comm = path (\|i-j\| >= 2) *) |
| 63 | Lemma | `s5_nt_L2` | Lemma s5_nt_L2 : n_traces_natB 4 2 path_comm_nat = 13. |
| 66 | Lemma | `s5_nt_L3` | Lemma s5_nt_L3 : n_traces_natB 4 3 path_comm_nat = 40. |

### `instances/s5/rigidity_s5_instance.v` (9)

| Line | Kind | Name | Tells us / Statement |
|---:|---|---|---|
| 83 | Lemma | `s5_endpoint_bound_fiber` | (* Fiber-counted endpoint bound: for each sheet s in 'I_5, var_dist(fdistmap perm_endpoint (rho_from_words 1 path_gen_tuple_3), uniform) <= 6/5. Achievable(1) = {(01),(12),(23),(34)} (4 adjacent tran… |
| 228 | Lemma | `s5_HN5_crypto` | (* Sheet count: 5 sheets (pgg_N' = 4) — definitionally true. *) |
| 232 | Lemma | `s5_genus0_pgl_crypto` | (* PGL bound: \|pgg_G R_s5\| <= \|{perm 'I_5}\| = 5! = 120 = pgl_bound R_s5. *) |
| 274 | Lemma | `s5_HN5` | (* Sheet count for R_s5: 5 sheets (pgg_N' = 4). Verified definitionally since R_s5 = Gen_PGGTypes 3 3 (path_gen_tuple 3), so pgg_N' = 4. *) |
| 291 | Lemma | `s5_genus0_automorphism` | (** s5_genus0_automorphism — discharges [genus0_automorphism_bound] for the S_5 instance by reducing to the concrete PGL bound [s5_genus0_pgl]. Kind: helper. Why: required to instantiate [s5_threshol… |
| 305 | Lemma | `s5_complexity` | (* Derived properties *) |
| 311 | Lemma | `s5_search_chain` | Lemma s5_search_chain (L : nat) : |
| 316 | Lemma | `s5_tradeoff` | Lemma s5_tradeoff : |
| 332 | Lemma | `s5_ts_recon_correct` | (** Protocol reconstruction correctness: named instance-level re-export of [ar_protocol_correct]. Takes a [PGGInterface] as a parameter since the S5 instance is parameterised over the starting-card c… |

### `instances/s5/s5_mixing.v` (10)

| Line | Kind | Name | Tells us / Statement |
|---:|---|---|---|
| 55 | Lemma | `s5_alpha_R_ge0` | Lemma s5_alpha_R_ge0 (R : realType) : 0 <= s5_alpha_R R. |
| 61 | Lemma | `s5_alpha_R_le1` | Lemma s5_alpha_R_le1 (R : realType) : s5_alpha_R R <= 1. |
| 67 | Lemma | `s5_alpha_R_lt1` | Lemma s5_alpha_R_lt1 (R : realType) : s5_alpha_R R < 1. |
| 77 | Lemma | `path_gen_tuple_3_invol` | (******************************************************************************) |
| 160 | Lemma | `s5_sos_diagonal_nonneg` | (** s5_sos_diagonal_nonneg — every entry of [s5_sos_diagonal] is nonneg in [rat]. Kind: helper. Why: discharges the D-nonnegativity premise needed when the SoS certificate is consumed to prove a Rayl… |
| 184 | Lemma | `s5_spectral_convergence_proved` | (******************************************************************************) |
| 209 | Lemma | `s5_gap_R_pos` | Lemma s5_gap_R_pos (R : realType) : 0 < s5_gap_R R. |
| 215 | Lemma | `s5_gap_R_le1` | Lemma s5_gap_R_le1 (R : realType) : s5_gap_R R <= 1. |
| 221 | Lemma | `s5_gap_R_one_minus` | Lemma s5_gap_R_one_minus (R : realType) : 1 - s5_gap_R R = s5_alpha_R R. |
| 224 | Lemma | `s5_spectral_convergence_gap` | Lemma s5_spectral_convergence_gap |

### `instances/s5x5/pgg_s5x5.v` (4)

| Line | Kind | Name | Tells us / Statement |
|---:|---|---|---|
| 86 | Lemma | `s5x5_gens_agree` | (******************************************************************************) |
| 105 | Lemma | `s5x5_weval_inj1` | (******************************************************************************) |
| 136 | Lemma | `s5x5_nt_L1` | (******************************************************************************) |
| 139 | Lemma | `s5x5_nt_L2` | Lemma s5x5_nt_L2 : n_traces_natB 8 2 s5x5_comm_nat = 42. |

### `instances/s5x5/rigidity_s5x5_instance.v` (12)

| Line | Kind | Name | Tells us / Statement |
|---:|---|---|---|
| 87 | Lemma | `s5x5_endpoint_bound_fiber` | Lemma s5x5_endpoint_bound_fiber : |
| 282 | Lemma | `s5x5_hurwitz` | (* Riemann-Hurwitz: 2*3 + 2*\|G\| = \|G\|*(2*0) + ramif + 2 6 + 2*14400 = 28804 + 2 = 28806 *) |
| 295 | Lemma | `s5x5_n_branch_le` | (** s5x5_n_branch_le — 6 <= 28804, the concrete branch-count-vs-total-ramif inequality for the S_5 x S_5 instance. Kind: helper. Why: discharges the [cd_ramif_ge_n_branch] field required when buildin… |
| 312 | Lemma | `s5x5_cs_gap` | (* Gap: ts_T <= ts_k + 2 * genus = 5 + 6 = 11 >= 10 *) |
| 317 | Lemma | `s5x5_preserves_pile1` | (* Pile preservation: the monodromy of S_5 × S_5 preserves {0..4} *) |
| 322 | Lemma | `s5x5_perm_compatible` | Lemma s5x5_perm_compatible : |
| 341 | Lemma | `s5x5_genus0_pgl` | (* genus = 3 ≠ 0 → the PGL hypothesis is vacuously true *) |
| 352 | Lemma | `s5x5_genus0_automorphism` | (** s5x5_genus0_automorphism — discharges [genus0_automorphism_bound] for the S_5 x S_5 instance. Because the genus is 3, the genus-0 branch is vacuous and the obligation is discharged by [s5x5_genus… |
| 373 | Lemma | `s5x5_complexity` | (* --- Derived properties --- *) |
| 377 | Lemma | `s5x5_tradeoff` | Lemma s5x5_tradeoff : |
| 390 | Lemma | `s5x5_large_group` | (* The main point: genus > 0 is forced by \|G\| > pgl_bound *) |
| 396 | Lemma | `s5x5_ts_recon_correct` | (** Protocol reconstruction correctness: named instance-level re-export of [ar_protocol_correct]. Takes a [PGGInterface] as a parameter. *) |

### `instances/s5x5/s5x5_mixing.v` (64)

| Line | Kind | Name | Tells us / Statement |
|---:|---|---|---|
| 58 | Lemma | `s5_lazy_gen_invol` | Lemma s5_lazy_gen_invol : |
| 101 | Lemma | `s5_lazy_tnth_0` | (* tnth values of s5_lazy_gen_tuple at the 8 indices. The first 4 are path transpositions on 'I_5, the last 4 are identities. *) |
| 103 | Lemma | `s5_lazy_tnth_1` | Lemma s5_lazy_tnth_1 : tnth s5_lazy_gen_tuple (Ordinal (n:=8) (m:=1) erefl) = tperm o1 o2. |
| 105 | Lemma | `s5_lazy_tnth_2` | Lemma s5_lazy_tnth_2 : tnth s5_lazy_gen_tuple (Ordinal (n:=8) (m:=2) erefl) = tperm o2 o3. |
| 107 | Lemma | `s5_lazy_tnth_3` | Lemma s5_lazy_tnth_3 : tnth s5_lazy_gen_tuple (Ordinal (n:=8) (m:=3) erefl) = tperm o3 o4. |
| 109 | Lemma | `s5_lazy_tnth_4` | Lemma s5_lazy_tnth_4 : tnth s5_lazy_gen_tuple (Ordinal (n:=8) (m:=4) erefl) = 1%g. |
| 111 | Lemma | `s5_lazy_tnth_5` | Lemma s5_lazy_tnth_5 : tnth s5_lazy_gen_tuple (Ordinal (n:=8) (m:=5) erefl) = 1%g. |
| 113 | Lemma | `s5_lazy_tnth_6` | Lemma s5_lazy_tnth_6 : tnth s5_lazy_gen_tuple (Ordinal (n:=8) (m:=6) erefl) = 1%g. |
| 115 | Lemma | `s5_lazy_tnth_7` | Lemma s5_lazy_tnth_7 : tnth s5_lazy_gen_tuple (Ordinal (n:=8) (m:=7) erefl) = 1%g. |
| 119 | Lemma | `path_gen_3_tnth_0` | (* Path generator tuple at the 4 indices. *) |
| 125 | Lemma | `path_gen_3_tnth_1` | Lemma path_gen_3_tnth_1 : |
| 131 | Lemma | `path_gen_3_tnth_2` | Lemma path_gen_3_tnth_2 : |
| 137 | Lemma | `path_gen_3_tnth_3` | Lemma path_gen_3_tnth_3 : |
| 146 | Lemma | `schreier_gen_count_eq_sum` | (* For any generator tuple, we can express schreier_gen_count via a sum using sum1dep_card. *) |
| 156 | Lemma | `sum_8_enum` | (* Enumerate sum over 'I_8, right-associative form (matches big_ord_recl output). *) |
| 173 | Lemma | `sum_4_enum` | (* Enumerate sum over 'I_4, right-associative form. *) |
| 186 | Lemma | `s5_lazy_count_eq` | (* Lazy generator count = path generator count + (4 if i=j else 0). *) |
| 202 | Lemma | `s5_lazy_Q_eq` | (* The Q matrix formula: Q_lazy = (Q_s5 + I) / 2. *) |
| 231 | Lemma | `s5_lazy_alpha_R_ge0` | Lemma s5_lazy_alpha_R_ge0 : 0 <= s5_lazy_alpha_R. |
| 238 | Lemma | `s5_lazy_alpha_R_le1` | Lemma s5_lazy_alpha_R_le1 : s5_lazy_alpha_R <= 1. |
| 247 | Lemma | `var_dist_le_2` | (* var_dist <= 2 trivial bound, used as fallback *) |
| 261 | Lemma | `var_dist_fdistmap_inj` | (* fdistmap with injective f preserves var_dist exactly. *) |
| 296 | Lemma | `Q_lazy_eq_matrix` | (* === Matrix-level Q_lazy facts === *) |
| 306 | Lemma | `Q_lazy_mul_v` | Lemma Q_lazy_mul_v (v : 'cV[R]_5) : |
| 314 | Lemma | `Q_lazy_symm` | Lemma Q_lazy_symm : Q_lazy^T = Q_lazy. |
| 317 | Lemma | `Q_s5_symm` | Lemma Q_s5_symm : Q_s5^T = Q_s5. |
| 321 | Lemma | `cV_innerDl_5` | (* === Bilinearity of cV_inner === *) |
| 329 | Lemma | `cV_innerDr_5` | Lemma cV_innerDr_5 (u v w : 'cV[R]_5) : |
| 337 | Lemma | `cV_innerZl_5` | Lemma cV_innerZl_5 (a : R) (v w : 'cV[R]_5) : |
| 345 | Lemma | `cV_innerZr_5` | Lemma cV_innerZr_5 (a : R) (v w : 'cV[R]_5) : |
| 354 | Lemma | `cV_cauchy_schwarz` | (* === Cauchy-Schwarz on cV_inner === *) |
| 359 | Lemma | `s5_inner_v_Qv_bound` | (* === Signed Cauchy-Schwarz: <v, Q_s5 v> <= alpha * <v, v> === *) |
| 384 | Lemma | `s5_lazy_alpha_sq_eq` | (* === Algebraic identity for the lazy alpha squared === *) |
| 400 | Lemma | `s5_lazy_rayleigh_Qsq_R` | (* === Main theorem: Rayleigh bound for Q_lazy^2 === *) |
| 466 | Lemma | `s5_lazy_alpha_R_lt1` | (* Strict bound: lazy_alpha < 1 *) |
| 484 | Lemma | `s5_lazy_TV_bound` | Lemma s5_lazy_TV_bound (L : nat) (s : 'I_5) : |
| 508 | Lemma | `widen5to10_inj` | Lemma widen5to10_inj : injective widen5to10. |
| 516 | Lemma | `s5x5_gen_pile1_action` | (* Per-step equivalence: each generator k acts identically on pile-1. *) |
| 536 | Lemma | `word_eval_pile1` | (* Word-level equivalence: word_eval s5x5 w (widen s) = widen (word_eval s5_lazy w s) *) |
| 562 | Lemma | `s5x5_rho_pile1_eq` | (* Distribution equivalence *) |
| 585 | Lemma | `rshift5_lt10` | (******************************************************************************) |
| 590 | Lemma | `rshift5to10_inj` | Lemma rshift5to10_inj : injective rshift5to10. |
| 614 | Lemma | `s5x5_gen_pile2_action` | (* Pile-2 per-step equivalence: generators k act on rshift5to10 s. *) |
| 634 | Lemma | `word_eval_pile2` | (* Word-level equivalence for pile-2 *) |
| 659 | Lemma | `s5x5_rho_pile2_eq` | Lemma s5x5_rho_pile2_eq (L : nat) (s : 'I_5) : |
| 689 | Lemma | `fdist_uniform_pile1E` | Lemma fdist_uniform_pile1E (i : 'I_10) : |
| 710 | Lemma | `fdist_uniform_pile2E` | Lemma fdist_uniform_pile2E (i : 'I_10) : |
| 734 | Lemma | `var_dist_uniform_pile1_uniform10` | Lemma var_dist_uniform_pile1_uniform10 : |
| 758 | Lemma | `var_dist_uniform_pile2_uniform10` | Lemma var_dist_uniform_pile2_uniform10 : |
| 790 | Lemma | `s5_lazy_gen_invol'` | (******************************************************************************) |
| 800 | Lemma | `s5_lazy_tnth'_0` | Lemma s5_lazy_tnth'_0 : |
| 803 | Lemma | `s5_lazy_tnth'_1` | Lemma s5_lazy_tnth'_1 : |
| 806 | Lemma | `s5_lazy_tnth'_2` | Lemma s5_lazy_tnth'_2 : |
| 809 | Lemma | `s5_lazy_tnth'_3` | Lemma s5_lazy_tnth'_3 : |
| 812 | Lemma | `s5_lazy_tnth'_4` | Lemma s5_lazy_tnth'_4 : |
| 816 | Lemma | `s5_lazy_tnth'_5` | Lemma s5_lazy_tnth'_5 : |
| 820 | Lemma | `s5_lazy_tnth'_6` | Lemma s5_lazy_tnth'_6 : |
| 824 | Lemma | `s5_lazy_tnth'_7` | Lemma s5_lazy_tnth'_7 : |
| 829 | Lemma | `s5_lazy_count_eq'` | Lemma s5_lazy_count_eq' (i j : 'I_5) : |
| 846 | Lemma | `s5_lazy_Q_eq_swap` | Lemma s5_lazy_Q_eq_swap (R : realType) : |
| 862 | Lemma | `s5_lazy_TV_bound'` | (******************************************************************************) |
| 892 | Lemma | `s5x5_pile1_TV_bound` | (* Pile-1 TV bound: distance to uniform_pile1 decays exponentially. *) |
| 911 | Lemma | `s5x5_pile2_TV_bound` | (* Pile-2 TV bound: distance to uniform_pile2 decays exponentially. *) |
| 930 | Lemma | `s5x5_spectral_TV_bound` | (* Final triangle bound: combines the pile bound with the gap to uniform_10. *) |

### `instances/s5x5/s5x5_pile.v` (2)

| Line | Kind | Name | Tells us / Statement |
|---:|---|---|---|
| 38 | Lemma | `s5x5_preserves_pile1_proved` | (******************************************************************************) |
| 72 | Lemma | `s5x5_preserves_pile2_proved` | (** s5x5_preserves_pile2_proved — every [g \in pgg_G] preserves the upper half of [`I_10] (indices >= 5) setwise under the [pgg_rho] action. Kind: helper. Why: companion to [s5x5_preserves_pile1]; to… |

## `lib/` (19 decls)

### `lib/perm_uniform.v` (19)

| Line | Kind | Name | Tells us / Statement |
|---:|---|---|---|
| 37 | Lemma | `prescribedP` | Lemma prescribedP k (s v : 'I_k -> 'I_N) (sigma : {perm 'I_N}) : |
| 43 | Lemma | `prescribed0` | Lemma prescribed0 (s v : 'I_0 -> 'I_N) : prescribed s v = [set: {perm 'I_N}]. |
| 51 | Lemma | `Sn_k_transitive` | (* Lemma 1: S_N acts k-transitively: given injective s and v, there exists sigma with sigma(s_i) = v_i for all i *) |
| 85 | Lemma | `prescribed_coset` | (* Lemma 2: prescribed k s v is a right coset of Sym(~: im s) *) |
| 110 | Lemma | `card_prescribed` | (* Lemma 3: \|prescribed k s v\| = (N - k)! *) |
| 154 | Lemma | `s_ext_inj` | Lemma s_ext_inj (s_new : 'I_N) : |
| 169 | Lemma | `v_ext_inj` | Lemma v_ext_inj (v_new : 'I_N) : |
| 186 | Lemma | `prescribed_extend` | (* The set of sigma in prescribed(s,v) with sigma(s_new) = v_new equals prescribed(s',v') with k+1 constraints *) |
| 209 | Lemma | `prescribed_value_count` | (* Lemma 4: counting prescribed values *) |
| 223 | Lemma | `prescribed_ratio` | (* Corollary: ratio gives 1/(N-k) *) |
| 248 | Lemma | `N_pos` | Lemma N_pos : (0 < N)%N. Proof. by []. Qed. |
| 251 | Lemma | `card_permT_N` | (* Cardinality of S_N *) |
| 271 | Lemma | `Pr_prescribed` | (* Probability of the prescribed event *) |
| 281 | Lemma | `Pr_prescribed_ne0` | Lemma Pr_prescribed_ne0 : Pr perm_fdist obs_set != (0 : R)%R. |
| 289 | Lemma | `perm_cond_uniform` | (* Main result: conditional probability *) |
| 320 | Lemma | `perm_cond_zero` | (* Conditional probability is zero for already-assigned values *) |
| 343 | Lemma | `card_remaining` | Lemma card_remaining : #\|remaining_values\| = (N - k)%N. |
| 352 | Lemma | `collusion_uniform` | Lemma collusion_uniform (s_new : 'I_N) (v_new : 'I_N) : |
| 362 | Lemma | `collusion_zero` | Lemma collusion_zero (s_new : 'I_N) (v_new : 'I_N) : |

## `protocol/` (47 decls)

### `protocol/card_exchange_pismc.v` (17)

| Line | Kind | Name | Tells us / Statement |
|---:|---|---|---|
| 287 | Lemma | `id_perm_morphM` | (* Identity morphism on permutation group *) |
| 313 | Lemma | `test_starts_2_uniq` | Lemma test_starts_2_uniq : uniq test_starts_2. |
| 342 | Lemma | `dealer_player0_dual_2` | (* 4-process duality: all 6 pairs *) |
| 345 | Lemma | `dealer_player1_dual_2` | Lemma dealer_player1_dual_2 : channels_dual ap_dealer_2 ap_player1_2. |
| 348 | Lemma | `dealer_verifier_dual_2` | Lemma dealer_verifier_dual_2 : channels_dual ap_dealer_2 ap_verifier_2. |
| 351 | Lemma | `player0_player1_dual_2` | Lemma player0_player1_dual_2 : channels_dual ap_player0_2 ap_player1_2. |
| 354 | Lemma | `player0_verifier_dual_2` | Lemma player0_verifier_dual_2 : channels_dual ap_player0_2 ap_verifier_2. |
| 357 | Lemma | `player1_verifier_dual_2` | Lemma player1_verifier_dual_2 : channels_dual ap_player1_2 ap_verifier_2. |
| 393 | Lemma | `dealer_player0_dual_gen` | Lemma dealer_player0_dual_gen : channels_dual ap_dealer_gen ap_player0_gen. |
| 396 | Lemma | `dealer_player1_dual_gen` | Lemma dealer_player1_dual_gen : channels_dual ap_dealer_gen ap_player1_gen. |
| 399 | Lemma | `dealer_verifier_dual_gen` | Lemma dealer_verifier_dual_gen : channels_dual ap_dealer_gen ap_verifier_gen. |
| 402 | Lemma | `player0_player1_dual_gen` | Lemma player0_player1_dual_gen : channels_dual ap_player0_gen ap_player1_gen. |
| 405 | Lemma | `player0_verifier_dual_gen` | Lemma player0_verifier_dual_gen : channels_dual ap_player0_gen ap_verifier_gen. |
| 408 | Lemma | `player1_verifier_dual_gen` | Lemma player1_verifier_dual_gen : channels_dual ap_player1_gen ap_verifier_gen. |
| 467 | Lemma | `star_4_le_N` | Lemma star_4_le_N : 4 <= m.+3. |
| 498 | Lemma | `oc_4_le_N` | Lemma oc_4_le_N : 4 <= (k + p).+3. |
| 550 | Lemma | `abel_4_le_N` | Lemma abel_4_le_N : 4 <= m.+1.*2. |

### `protocol/pgg_interface.v` (30)

| Line | Kind | Name | Tells us / Statement |
|---:|---|---|---|
| 88 | Lemma | `endpointM` | Lemma endpointM (g h : gT) (s : 'I_N) : |
| 93 | Lemma | `endpoint1` | Lemma endpoint1 (s : 'I_N) : endpoint 1 s = s. |
| 96 | Lemma | `endpoint_inj` | Lemma endpoint_inj (g : gT) : injective (endpoint g). |
| 99 | Lemma | `endpointV` | Lemma endpointV (g : gT) (s : 'I_N) : |
| 153 | Lemma | `sigmas_in_G` | (* Upper bound: achievable ⊆ G *) |
| 161 | Lemma | `achievable_sub` | Lemma achievable_sub (L : nat) : achievable L \subset G. |
| 169 | Lemma | `search_space_leG` | (* Upper bound: search space ≤ \|G\| *) |
| 176 | Lemma | `search_space_le_words` | (* Upper bound: search space ≤ T^L (number of words) *) |
| 188 | Lemma | `weval_inj_search_space` | (* Word-eval injective generators achieve the maximal search space T^L *) |
| 199 | Lemma | `weval_injP` | Lemma weval_injP (L : nat) : reflect (weval_inj L) (weval_injB L). |
| 216 | Lemma | `gen_inj_weval_inj1` | Lemma gen_inj_weval_inj1 : |
| 227 | Lemma | `gen_inj_weval_inj1_search_space` | Lemma gen_inj_weval_inj1_search_space : |
| 248 | Lemma | `pgg_dtype_eqP` | Lemma pgg_dtype_eqP : Equality.axiom pgg_dtype_eqb. |
| 282 | Lemma | `from_sheet_PGG_sheet` | Lemma from_sheet_PGG_sheet {N} (i : 'I_N) : |
| 286 | Lemma | `from_hand_PGG_hand` | Lemma from_hand_PGG_hand {N} (s : seq ('I_N)) : |
| 290 | Lemma | `from_idx_PGG_idx` | Lemma from_idx_PGG_idx {N} (n : nat) : |
| 327 | Lemma | `start_sheet_inj` | Lemma start_sheet_inj : injective start_sheet. |
| 341 | Lemma | `card_start_sheets` | Lemma card_start_sheets : #\|start_sheets\| = T. |
| 359 | Lemma | `compute_in_dealt_hand` | Lemma compute_in_dealt_hand (W : seq gT) (P : gT) (i : 'I_T) : |
| 366 | Lemma | `endpointsE` | Lemma endpointsE (P : gT) (i : 'I_T) : |
| 370 | Lemma | `endpoint_starts_uniq` | Lemma endpoint_starts_uniq (g : gT) : |
| 402 | Lemma | `gen_incl_morphM` | (* Inclusion morphism: identity on the subgroup *) |
| 413 | Lemma | `gen_sigmas_gen` | Lemma gen_sigmas_gen : |
| 425 | Lemma | `gen_starts_2_uniq` | Lemma gen_starts_2_uniq : uniq gen_starts_2. |
| 445 | Lemma | `gen_starts_T_size` | Lemma gen_starts_T_size : size (map (widen_ord HT) (enum 'I_T)) == T. |
| 450 | Lemma | `gen_starts_T_uniq` | Lemma gen_starts_T_uniq : uniq gen_starts_T. |
| 471 | Lemma | `gen_map_size` | Lemma gen_map_size : size (map gen (enum 'I_T.+1)) == T.+1. |
| 476 | Lemma | `gen_tuple_ofE` | Lemma gen_tuple_ofE (i : 'I_T.+1) : tnth gen_tuple_of i = gen i. |
| 491 | Lemma | `tperm_disjoint_comm` | Lemma tperm_disjoint_comm (fT : finType) (a b c d : fT) : |
| 511 | Lemma | `gen_nonabelian` | (* Non-abelianity from a non-commuting generator pair *) |

## `reconstruct/` (252 decls)

### `reconstruct/ag_code.v` (8)

| Line | Kind | Name | Tells us / Statement |
|---:|---|---|---|
| 43 | Lemma | `ag_code_eval` | Lemma ag_code_eval (m : 'rV[F]_k) : m *m ev \in ag_code. |
| 49 | Lemma | `ag_code_memP` | Lemma ag_code_memP (c : 'rV[F]_n) : |
| 57 | Lemma | `dim_ag_code` | Lemma dim_ag_code : \rank ev = k -> \dim ag_code = k. |
| 87 | Lemma | `ag_mulmx_inj` | Lemma ag_mulmx_inj : forall m1 m2 : 'rV[F]_k, |
| 95 | Lemma | `ag_mulmx_neq0` | Lemma ag_mulmx_neq0 (m : 'rV[F]_k) : m != 0 -> m *m ev != 0. |
| 102 | Lemma | `ag_not_trivial` | Lemma ag_not_trivial : not_trivial (ag_code ev). |
| 114 | Lemma | `ag_min_dist_lb` | Lemma ag_min_dist_lb : n - (k + g - 1) <= min_dist ag_not_trivial. |
| 125 | Lemma | `ag_min_dist_ge2` | Lemma ag_min_dist_ge2 : k + g < n -> 1 < min_dist ag_not_trivial. |

### `reconstruct/ag_massey_bridge.v` (3)

| Line | Kind | Name | Tells us / Statement |
|---:|---|---|---|
| 66 | Lemma | `d_perp_eq` | (* d_perp'.+2 = (k - g).+1 when g < k *) |
| 73 | Lemma | `ag_massey_gap` | Lemma ag_massey_gap : ts_T ag_massey <= ts_k ag_massey + 2 * g. |
| 97 | Lemma | `ag_genus_gap` | Lemma ag_genus_gap : |

### `reconstruct/ag_multiplicative.v` (4)

| Line | Kind | Name | Tells us / Statement |
|---:|---|---|---|
| 45 | Lemma | `hadamard_comm` | Lemma hadamard_comm (c1 c2 : 'rV[F]_n) : |
| 49 | Lemma | `hadamardE` | Lemma hadamardE (c1 c2 : 'rV[F]_n) (i : 'I_n) : |
| 123 | Lemma | `hadamard_massey_codeword` | Lemma hadamard_massey_codeword (s1 s2 : F) |
| 198 | Lemma | `ag_massey_mult` | (* Core: multiplying valid base shares gives valid doubled shares. Proof: the Hadamard product of two massey_codewords is a massey_codeword with secret = product (hadamard_massey_codeword), and ag_mu… |

### `reconstruct/algebraic_rigidity.v` (7)

| Line | Kind | Name | Tells us / Statement |
|---:|---|---|---|
| 297 | Lemma | `ar_complexity` | (** Complexity: search space is bounded by \|G\| *) |
| 301 | Lemma | `ar_tradeoff` | (** Tradeoff: either genus-0 with bounded \|G\|, or positive genus with gap *) |
| 317 | Lemma | `ar_search_gap_tradeoff` | (** Search-gap tradeoff: search space bounded or threshold has gap *) |
| 332 | Lemma | `ar_large_group_forces_gap` | (** Large groups force positive genus *) |
| 344 | Lemma | `ar_gap_bound` | (** Gap bound: threshold gap is bounded by twice the genus *) |
| 350 | Lemma | `ar_protocol_correct` | (** Protocol correctness: perm-compatible scheme + valid shares + G-stable starts *) |
| 383 | Lemma | `ar_search_space_chain` | (** Search space chain: search_space <= n_traces <= Tg^L (RAAG-specific) *) |

### `reconstruct/coord_perm_compatible.v` (10)

| Line | Kind | Name | Tells us / Statement |
|---:|---|---|---|
| 58 | Lemma | `coord_perm_compatible_id` | (** coord_perm_compatible_id — the identity permutation is coord-perm compatible with every linear code [C : Lcode0.t F n], because [col_perm 1%g c = c]. Kind: helper. Why: trivial-sigma base case fo… |
| 74 | Lemma | `sigma_lift_neq0` | Lemma sigma_lift_neq0 (j : 'I_n'.+1) : sigma (lift ord0 j) != ord0. |
| 85 | Lemma | `restrict_perm0_funE` | Lemma restrict_perm0_funE (j : 'I_n'.+1) : |
| 94 | Lemma | `restrict_perm0_inj` | Lemma restrict_perm0_inj : injective restrict_perm0_fun. |
| 106 | Lemma | `restrict_perm0_valE` | Lemma restrict_perm0_valE (j : 'I_n'.+1) : |
| 134 | Lemma | `massey_codeword_col_perm` | Lemma massey_codeword_col_perm (s : F) (shares : 'rV[F]_n'.+1) : |
| 158 | Lemma | `massey_recon_col_perm` | Lemma massey_recon_col_perm (s : F) (shares : 'rV[F]_n'.+1) : |
| 208 | Lemma | `massey_share_permE` | Lemma massey_share_permE (g : gT) (gG : g \in G) : |
| 216 | Lemma | `massey_perm_compatible` | Lemma massey_perm_compatible : |
| 254 | Lemma | `transport_perm_compatible` | Lemma transport_perm_compatible : |

### `reconstruct/cover_genus0.v` (5)

| Line | Kind | Name | Tells us / Statement |
|---:|---|---|---|
| 70 | Lemma | `genus0_hurwitz` | Lemma genus0_hurwitz : |
| 86 | Lemma | `genus0_ramif_ge_nbr` | (** genus0_ramif_ge_nbr — lower bound [2 <= ramif0], where [ramif0] is the total ramification in the genus-0 case. Kind: helper. Why: fills the [cd_ramif_ge_n_branch] field when assembling the genus-… |
| 141 | Lemma | `ts0_perm_compatible` | Lemma ts0_perm_compatible : |
| 162 | Lemma | `shamir_exact` | (* Exact threshold for genus-0 covering *) |
| 168 | Lemma | `genus0_secret_invariant` | (* Protocol integration: reconstruction recovers the secret (requires G-stable starts hypothesis) *) |

### `reconstruct/cover_genus1.v` (7)

| Line | Kind | Name | Tells us / Statement |
|---:|---|---|---|
| 66 | Lemma | `genus1_hurwitz` | Lemma genus1_hurwitz : |
| 79 | Lemma | `genus1_ramif_ge_nbr` | (** genus1_ramif_ge_nbr — lower bound [3 <= ramif1] for the total ramification [ramif1] of the genus-1 cover. Kind: helper. Why: fills the [cd_ramif_ge_n_branch] field when assembling the genus-1 [Co… |
| 238 | Lemma | `ts1_perm_compatible` | Lemma ts1_perm_compatible : |
| 257 | Lemma | `elliptic_gap` | (* Quasi-(k, k+2) threshold *) |
| 262 | Lemma | `genus1_vs_genus0` | (* The gap is strictly wider than genus-0 (when ts_T > ts_k) *) |
| 429 | Lemma | `ts_g_perm_compatible` | Lemma ts_g_perm_compatible : |
| 447 | Lemma | `higher_genus_gap_bound` | Lemma higher_genus_gap_bound : |

### `reconstruct/cover_genus2.v` (5)

| Line | Kind | Name | Tells us / Statement |
|---:|---|---|---|
| 68 | Lemma | `genus2_hurwitz` | Lemma genus2_hurwitz : |
| 81 | Lemma | `genus2_ramif_ge_nbr` | (** genus2_ramif_ge_nbr — lower bound [5 <= ramif2] for the total ramification [ramif2] of the genus-2 hyperelliptic cover. Kind: helper. Why: fills the [cd_ramif_ge_n_branch] field when assembling t… |
| 241 | Lemma | `ts2_perm_compatible` | Lemma ts2_perm_compatible : |
| 260 | Lemma | `genus2_gap` | (* Quasi-(k, k+4) threshold *) |
| 265 | Lemma | `genus2_vs_genus1` | (* The gap is strictly wider than genus-1 *) |

### `reconstruct/cover_tradeoff.v` (8)

| Line | Kind | Name | Tells us / Statement |
|---:|---|---|---|
| 55 | Lemma | `genus0_forces_ramif` | (* For base P^1 (genus 0): 2g(C) + 2\|G\| = R + 2 So R = 2g(C) + 2\|G\| - 2 >= 2\|G\| - 2 And g(C) = (R + 2 - 2\|G\|) / 2 *) |
| 65 | Lemma | `more_ramif_more_genus` | (* More ramification -> higher genus *) |
| 90 | Lemma | `search_space_le_group` | (* Search space is bounded by \|G\| *) |
| 121 | Theorem | `security_threshold_tradeoff` | (* THE MAIN TRADEOFF THEOREM: Either the anonymity entropy is bounded (genus 0, \|G\| <= PGL bound) or the threshold has a gap (genus > 0). Both regimes are information-theoretically secure. The genus0… |
| 143 | Lemma | `large_group_forces_gap` | (* Contrapositive: large group forces threshold gap *) |
| 156 | Lemma | `group_genus_monotone` | (* Monotonicity: larger group -> more ramification needed -> higher genus *) |
| 169 | Theorem | `search_gap_tradeoff` | (* Combined statement: anonymity set size vs threshold gap *) |
| 204 | Lemma | `pgl_bound_eq_pgl_card` | (** pgl_bound_eq_pgl_card — equational bridge [pgl_bound M = pgl_card (pgg_N' M).+1] for any [GeneratedMonodromyReprType] [M]. Kind: helper. Why: rewrites the abstract [pgl_bound] accessor into the c… |

### `reconstruct/covering_scheme.v` (7)

| Line | Kind | Name | Tells us / Statement |
|---:|---|---|---|
| 91 | Lemma | `genus_from_hurwitz` | (* Genus is determined by \|G\|, base genus, and ramification *) |
| 144 | Lemma | `genus0_exact` | (* Genus 0 implies exact threshold (gap = 0) *) |
| 154 | Lemma | `higher_genus_wider_gap` | (* Higher genus allows a wider threshold gap *) |
| 161 | Lemma | `gap_bound` | (* The threshold gap is bounded by twice the genus *) |
| 179 | Lemma | `hurwitz_base0` | (* When base = P^1 (genus 0), Riemann-Hurwitz simplifies: 2g(C) + 2\|G\| = R + 2 i.e., 2g(C) = R + 2 - 2\|G\| *) |
| 188 | Lemma | `genus0_ramif` | (* Genus 0 with base = P^1 forces ramification = 2\|G\| - 2 *) |
| 199 | Lemma | `ramif_forces_genus` | (* Ramification exceeding 2\|G\|-2 forces positive genus *) |

### `reconstruct/hyperelliptic_code.v` (12)

| Line | Kind | Name | Tells us / Statement |
|---:|---|---|---|
| 47 | Lemma | `size_sqr` | Lemma size_sqr (p : {poly R}) : p != 0 -> size (p ^+ 2) = (size p).*2.-1. |
| 58 | Lemma | `double_pred_odd` | (* Odd-even parity contradiction: used for the resultant argument *) |
| 63 | Lemma | `parity_size_neq` | (* Key parity lemma: (2a-1) cannot equal (2b-1 + (2k+2)) - 1 = 2b + 2k because the LHS is odd and the RHS is even. *) |
| 132 | Lemma | `hyp_resultant_deg` | (* Degree bound on the resultant. Key arithmetic: - size(A^2) = 2*size(A) - 1 <= 2*floor(m/2) + 1 <= m + 1 - size(B^2*f) = 2*size(B) - 1 + (2g+1) + 1 - 1 = 2*size(B) + 2g <= 2*floor((m-2g-1)/2) + 2g … |
| 172 | Lemma | `hyp_resultant_neq0` | (* Parity argument: R = A^2 - B^2*f != 0 when (A,B) != (0,0). size(A^2) is odd, size(B^2*f) is even, so they cannot be equal. *) |
| 215 | Lemma | `hyp_zero_to_root` | (* Zero-to-root mapping *) |
| 240 | Lemma | `hyp_multiplicity` | (* Multiplicity: if (X-x0) \| A and (X-x0) \| B, then (X-x0)^2 \| R *) |
| 272 | Theorem | `hyp_goppa_wt_mdeg` | (* Goppa bound: nonzero codewords have Hamming weight >= n - m_deg. Proved from resultant argument + max_poly_roots. *) |
| 312 | Theorem | `hyp_goppa_wt` | Theorem hyp_goppa_wt : |
| 347 | Theorem | `dual_root_poly` | (* Proved from dual_ev_encode using resultant machinery *) |
| 365 | Theorem | `dual_min_dist` | Theorem dual_min_dist : |
| 405 | Theorem | `hyp_priv_surj` | (* Privacy: for small coalitions S, the projection is surjective *) |

### `reconstruct/lagrange.v` (9)

| Line | Kind | Name | Tells us / Statement |
|---:|---|---|---|
| 57 | Lemma | `lagrange_denom_neq0` | (* The denominator is nonzero when points are distinct *) |
| 67 | Lemma | `lagrange_numer_eval_neq` | (* Numerator evaluated at pts_j when j != i contains a zero factor *) |
| 76 | Lemma | `lagrange_numer_eval_eq` | (* Numerator evaluated at pts_i equals the denominator *) |
| 84 | Lemma | `lagrange_basis_eval` | (* KEY LEMMA: Lagrange basis evaluation *) |
| 97 | Lemma | `size_lagrange_numer` | (* Size of the numerator polynomial *) |
| 111 | Lemma | `size_lagrange_basis` | (* Size of Lagrange basis polynomial *) |
| 139 | Lemma | `lagrange_interp_eval` | (* KEY LEMMA: Interpolation matches the given values *) |
| 151 | Lemma | `lagrange_interp_size` | (* Interpolation polynomial has size at most n *) |
| 175 | Lemma | `lagrange_interp_unique` | (* Two polynomials of size <= n agreeing on n distinct points are equal *) |

### `reconstruct/massey.v` (21)

| Line | Kind | Name | Tells us / Statement |
|---:|---|---|---|
| 49 | Lemma | `rV_to_tupleK` | Lemma rV_to_tupleK (v : 'rV[F]_m) : tuple_to_rV (rV_to_tuple v) = v. |
| 52 | Lemma | `tuple_to_rVK` | Lemma tuple_to_rVK (t : m.-tuple F) : rV_to_tuple (tuple_to_rV t) = t. |
| 58 | Lemma | `tuple_to_rV_tnth` | Lemma tuple_to_rV_tnth (t : m.-tuple F) (i : 'I_m) : |
| 85 | Lemma | `massey_codeword0` | Lemma massey_codeword0 (s : F) (shares : 'rV[F]_n'.+1) : |
| 90 | Lemma | `lift_inord` | (* Ordinal helper: lift ord0 (inord i.-1) = i when i != 0 *) |
| 99 | Lemma | `massey_codewordS` | Lemma massey_codewordS (s : F) (shares : 'rV[F]_n'.+1) (j : 'I_n'.+1) : |
| 107 | Lemma | `massey_codeword_decompose` | (* Any row vector decomposes as massey_codeword of its parts *) |
| 117 | Lemma | `massey_secret_unique` | (* Key uniqueness: if d >= 2, the secret is determined by the shares *) |
| 148 | Lemma | `massey_reconstruct_correct` | Lemma massey_reconstruct_correct (s : F) (shares : 'rV[F]_n'.+1) : |
| 177 | Lemma | `vproj_coord_eq` | (* Helper: extract coordinates from vproj equality *) |
| 191 | Lemma | `lift_share_inj` | Lemma lift_share_inj : injective lift_share. |
| 194 | Lemma | `lift_coalition_card` | Lemma lift_coalition_card (coal : {set 'I_n'.+1}) : |
| 198 | Lemma | `ord0_notin_lift` | Lemma ord0_notin_lift (coal : {set 'I_n'.+1}) : |
| 206 | Lemma | `card_S_bound` | Lemma card_S_bound (coal : {set 'I_n'.+1}) : |
| 216 | Lemma | `massey_private` | (* Main privacy lemma *) |
| 250 | Lemma | `first_coord_surj` | (* First coordinate projection is surjective: for every s, there exists c in C with c_0 = s. By privacy_surj with S = {ord0}, since \|S\| = 1 < d_perp. *) |
| 266 | Lemma | `massey_encode_codeword` | Lemma massey_encode_codeword (s : F) : |
| 286 | Lemma | `massey_correct_tuple` | Lemma massey_correct_tuple (s : F) (shares : n'.+1.-tuple F) : |
| 291 | Lemma | `massey_private_tuple` | Lemma massey_private_tuple (s1 s2 : F) (shares : n'.+1.-tuple F) |
| 311 | Lemma | `massey_encode_valid` | Lemma massey_encode_valid (s : F) : |
| 344 | Lemma | `mds_min_dist_eq` | (* For MDS codes: d = n - k + 1 (Singleton bound with equality). The dual of an MDS code is MDS with d_perp = k + 1. Proving d_perp = k + 1 from HMDS requires the dual code theory (currently WIP in l… |

### `reconstruct/pgg_assignment.v` (19)

| Line | Kind | Name | Tells us / Statement |
|---:|---|---|---|
| 33 | Lemma | `succ_mod_neq` | (* Helper lemmas for modular arithmetic, proved before ring_scope to avoid scope conflicts with ssrnat rewrite lemmas. *) |
| 48 | Lemma | `succ_mod_cycle2_ord` | Lemma succ_mod_cycle2_ord (T : nat) (i j : 'I_T.+1) : |
| 140 | Lemma | `covered_mono` | Lemma covered_mono (C C' : {set 'I_T}) : |
| 150 | Lemma | `covered_full` | Lemma covered_full (C : {set 'I_T}) : |
| 157 | Lemma | `secure_subset` | Lemma secure_subset (C : {set 'I_T}) : |
| 161 | Lemma | `covered_secure_partition` | Lemma covered_secure_partition (C : {set 'I_T}) : |
| 169 | Lemma | `secure_singleton` | Lemma secure_singleton (C : {set 'I_T}) : |
| 181 | Lemma | `covered_edges0` | Lemma covered_edges0 : covered_edges G set0 = set0. |
| 206 | Lemma | `cycle_sym` | Lemma cycle_sym (i j : 'I_T) : |
| 210 | Lemma | `cycle_irrefl` | Lemma cycle_irrefl (i : 'I_T) : (i, i) \notin cycle_edge_set. |
| 227 | Lemma | `cycle_edge_set_union` | Lemma cycle_edge_set_union : cycle_edge_set = fwd_edges :\|: bwd_edges. |
| 242 | Lemma | `fwd_card` | Lemma fwd_card : #\|fwd_edges\| = T. |
| 248 | Lemma | `bwd_card` | Lemma bwd_card : #\|bwd_edges\| = T. |
| 254 | Lemma | `fwd_bwd_disjoint` | Lemma fwd_bwd_disjoint : (1 < T')%N -> [disjoint fwd_edges & bwd_edges]. |
| 268 | Lemma | `cycle_edges_count` | Lemma cycle_edges_count : (1 < T')%N -> #\|ag_edges cycle_graph\| = 2 * T. |
| 288 | Lemma | `complete_sym` | Lemma complete_sym (i j : 'I_T) : |
| 292 | Lemma | `complete_irrefl` | Lemma complete_irrefl (i : 'I_T) : (i, i) \notin complete_edge_set. |
| 298 | Lemma | `complete_edges_count` | Lemma complete_edges_count : |
| 321 | Lemma | `complete_covered_full` | Lemma complete_covered_full (C : {set 'I_T}) : |

### `reconstruct/pgg_covering_correctness.v` (4)

| Line | Kind | Name | Tells us / Statement |
|---:|---|---|---|
| 52 | Theorem | `pgg_covering_correct` | (* Main correctness theorem: CoveringScheme + PGGInterface + G-stable starts -> reconstruction recovers the hidden value. Uses pgg_hidden_invariant_perm with cs_perm_compatible. *) |
| 67 | Lemma | `covering_gap_bound` | (* The threshold gap is bounded by twice the covering genus *) |
| 90 | Theorem | `pgg_covering_tradeoff` | (* The security-threshold tradeoff, restated for the capstone: Either the covering has genus 0 (exact threshold, bounded group) or genus > 0 (threshold gap proportional to genus). *) |
| 113 | Theorem | `pgg_multiplicative_correct` | (* Multiplying shares locally computes the product secret in the doubled scheme. This is the key property enabling secure multiplication gates in arithmetic circuits over secret-shared data. *) |

### `reconstruct/pgg_dealer_bridge.v` (3)

| Line | Kind | Name | Tells us / Statement |
|---:|---|---|---|
| 52 | Theorem | `dealer_words_correct` | Theorem dealer_words_correct |
| 64 | Lemma | `dealer_words_epsilon_bound` | Lemma dealer_words_epsilon_bound (s : 'I_N) : |
| 73 | Theorem | `dealer_encode_correct` | (* When the dealer uses ts_encode to produce the starting shares, the ts_valid hypothesis is automatically satisfied. *) |

### `reconstruct/pgg_deck_pairing.v` (9)

| Line | Kind | Name | Tells us / Statement |
|---:|---|---|---|
| 59 | Lemma | `involution_partner` | (** An fpf involution pairs each element with a distinct partner. *) |
| 67 | Lemma | `fpf_involution_partner_neq` | Lemma fpf_involution_partner_neq (g : {perm 'I_N}) (x : 'I_N) : |
| 93 | Lemma | `decode_encode_bit1` | (** Decoding the encoding of bit 1 yields true. *) |
| 98 | Lemma | `decode_encode_bit0` | (** Decoding the encoding of bit 0 yields false, provided g is fpf. *) |
| 120 | Lemma | `equivariant_commute` | (** Key equivariance property: if sigma commutes with g (in the group sense), then sigma preserves the action of g pointwise. Proof sketch: commute g sigma means (g * sigma = sigma * g)%g. Evaluating… |
| 133 | Theorem | `decode_encode_1` | (** Reconstruction correctness for bit 1: After encoding bit 1 as (s, g(s)) and applying a commuting permutation sigma, the pair becomes (sigma(s), sigma(g(s))). Decoding recovers true because g(sigm… |
| 146 | Theorem | `decode_encode_0` | (** Reconstruction correctness for bit 0: After encoding bit 0 as (s, s) and applying sigma, the pair becomes (sigma(s), sigma(s)). Decoding recovers false because g is fpf, so g(sigma(s)) != sigma(s… |
| 157 | Theorem | `decode_encode_correct` | (** Equivariance extends to the full encoding: applying a commuting permutation to an encoded bit preserves the decoded value. *) |
| 195 | Theorem | `multi_decode_encode_correct` | (** Reconstruction correctness for multi-bit encoding: if every involution commutes with sigma and is fpf, then decoding after applying sigma recovers the original bits. *) |

### `reconstruct/pgg_landscape_demo.v` (12)

| Line | Kind | Name | Tells us / Statement |
|---:|---|---|---|
| 81 | Lemma | `monster_security_demo` | (* A: For every sheet s, var_dist <= epsilon ~ 0. *) |
| 92 | Lemma | `monster_tradeoff_demo` | (* A: One of two branches — and large \|G\| forces the right branch. *) |
| 105 | Lemma | `monster_genus_forced_demo` | (* A: No — \|G\| > PGL forces genus > 0. *) |
| 113 | Lemma | `monster_genus1_demo` | (* A: At most 2 — one extra share beyond k. *) |
| 121 | Lemma | `monster_hurwitz_demo` | (* A: Hurwitz forces \|G\| <= 84*(g-1), so g >= \|G\|/84 + 1 ~ 10^51. *) |
| 133 | Lemma | `monster_entropy_demo` | (* A: H(P_s) <= log N — near-maximum for the Monster. *) |
| 139 | Lemma | `monster_entropy_gap_demo` | (* A: D(P_s \|\| U_N) = log N - H(P_s), the KL divergence. *) |
| 148 | Lemma | `monster_pinsker_demo` | (* A: Yes — Pinsker gives var_dist <= sqrt(2 * entropy_gap). *) |
| 211 | Lemma | `oc_security_demo` | (* A: eps = 1 (fiber-counted). Weaker than Monster but exact threshold. *) |
| 220 | Lemma | `oc_entropy_demo` | (* A: H(P_s) <= log 4 = 2 bits. *) |
| 228 | Lemma | `oc_tradeoff_demo` | (* A: Genus 0, so T <= k (exact threshold, no gap). *) |
| 241 | Lemma | `oc_genus0_demo` | (* A: Exact: T <= k. *) |

### `reconstruct/pgg_protocol_landscape.v` (23)

| Line | Kind | Name | Tells us / Statement |
|---:|---|---|---|
| 119 | Lemma | `security_per_position` | Lemma security_per_position (sw : SecurityWitness R M) (s : 'I_N) : |
| 124 | Lemma | `complexity_from_group` | Lemma complexity_from_group (L : nat) : (@search_space M L <= #\|G\|)%N. |
| 139 | Theorem | `genus0_option` | Theorem genus0_option (cs : CoveringScheme M) : |
| 144 | Theorem | `genus1_universal_option` | Theorem genus1_universal_option (cs : CoveringScheme M) : |
| 153 | Theorem | `gap_from_genus` | Theorem gap_from_genus (cs : CoveringScheme M) : |
| 169 | Lemma | `genus0_requires_small_group` | Lemma genus0_requires_small_group (cs : CoveringScheme M) |
| 175 | Corollary | `large_group_minimum_gap` | Corollary large_group_minimum_gap (cs : CoveringScheme M) |
| 185 | Theorem | `landscape_tradeoff` | Theorem landscape_tradeoff (cs : CoveringScheme M) |
| 215 | Lemma | `group_forces_minimum_genus` | Lemma group_forces_minimum_genus (cs : CoveringScheme M) (g : nat) : |
| 229 | Theorem | `higher_genus_landscape` | Theorem higher_genus_landscape (cs : CoveringScheme M) : |
| 254 | Lemma | `protocol_correct_unbundled` | Lemma protocol_correct_unbundled |
| 296 | Lemma | `ar_security_per_position` | Lemma ar_security_per_position (s : 'I_N) : |
| 303 | Lemma | `ar_genus0_exact` | Lemma ar_genus0_exact : |
| 308 | Lemma | `ar_genus1_gap2` | Lemma ar_genus1_gap2 : |
| 316 | Lemma | `ar_hurwitz` | Lemma ar_hurwitz : |
| 323 | Lemma | `ar_large_group_forces_genus` | Lemma ar_large_group_forces_genus : |
| 371 | Lemma | `discovery_eps_monotone` | (* Envelope monotonicity — re-exported for landscape visibility *) |
| 378 | Lemma | `discovery_to_certification` | (* SecurityWitness construction from discovery — re-exported *) |
| 416 | Lemma | `ar_entropy_le_logN` | (* Entropy is at most log N (maximum = uniform) *) |
| 427 | Lemma | `ar_entropy_gap` | (* The entropy deficit equals the KL divergence (leakage in bits). D(P_s \|\| U_N) = log N - H(P_s). *) |
| 448 | Lemma | `ar_var_dist_from_entropy` | (* Pinsker bridge: var_dist bounded by entropy gap. var_dist(P_s, U_N) <= sqrt(2 * (log N - H(P_s))) *) |
| 491 | Lemma | `ar_covering_decomposition` | (* The covering decomposition: security and threshold from one algebraic choice. The SecurityWitness gives the endpoint bound (security side), and the CoveringScheme gives the gap bound (threshold si… |
| 501 | Lemma | `ar_genus0_shamir` | (* Genus-0 specialization: when the covering has genus 0, the threshold is exact (T <= k), recovering Shamir's (k,k)-threshold. *) |

### `reconstruct/pgg_sharing_framework.v` (6)

| Line | Kind | Name | Tells us / Statement |
|---:|---|---|---|
| 75 | Lemma | `ts_recon_encode` | Lemma ts_recon_encode {sT shT : Type} (ts : ThresholdScheme sT shT) (s : sT) : |
| 130 | Lemma | `sum_mod_scheme_correct` | Lemma sum_mod_scheme_correct (s : 'I_N) (shares : T.-tuple 'I_N) : |
| 138 | Lemma | `sum_mod_scheme_private` | Lemma sum_mod_scheme_private (s1 s2 : 'I_N) |
| 158 | Lemma | `sum_mod_encode_valid` | Lemma sum_mod_encode_valid (s : 'I_N) : |
| 193 | Lemma | `tnth_cast_tuple` | Lemma tnth_cast_tuple {A : Type} {n m : nat} (H : n = m) |
| 227 | Lemma | `pgg_hidden_invariant_perm` | (* Main theorem: coordinate-permutation compatible scheme + G-stable starts + valid starting shares ⟹ reconstruction of endpoints recovers the secret *) |

### `reconstruct/pgg_sum_mod.v` (9)

| Line | Kind | Name | Tells us / Statement |
|---:|---|---|---|
| 64 | Lemma | `sum_mod_checkP` | (* sum_mod_check is decidable and reflects sum_mod_valid *) |
| 82 | Lemma | `sum_mod_single_sheet` | Lemma sum_mod_single_sheet : |
| 124 | Theorem | `reconstruct_correct` | (* Main correctness theorem: if sigma preserves sum mod N, then the reconstruction recovers the original message *) |
| 137 | Lemma | `id_preserves_sum_mod` | (* The identity permutation preserves sum mod N *) |
| 144 | Lemma | `comp_preserves_sum_mod` | (* Composition of sum-preserving permutations preserves sum mod N *) |
| 194 | Lemma | `pgg_reconstruct_correct` | (* If rho(P) preserves sum mod N, reconstruction recovers the encoded message *) |
| 205 | Lemma | `pgg_reconstruct_id` | (* The identity group element always preserves reconstruction *) |
| 245 | Lemma | `partial_sum_full` | (* Full sum: the coalition is all parties *) |
| 258 | Lemma | `partial_sum_no_info` | (* Partial sums of strict subsets do not determine m. Informally: knowing sum_{i in C} e_i mod N does not reveal m when \|C\| < T, because the remaining T - \|C\| unknown sheets can sum to any residue mo… |

### `reconstruct/pgg_threshold.v` (14)

| Line | Kind | Name | Tells us / Statement |
|---:|---|---|---|
| 69 | Theorem | `ramp_threshold` | (** The main ramp threshold theorem: three-part characterization of coalition power in terms of edge coverage. *) |
| 90 | Corollary | `recoverable_mono` | (** Derived: the number of recoverable bits is monotone in coalition size. *) |
| 102 | Corollary | `singleton_no_info` | (** A singleton coalition recovers nothing. *) |
| 111 | Corollary | `empty_no_info` | (** The empty coalition recovers nothing. *) |
| 118 | Lemma | `ramp_partition` | (** Secure edges and covered edges partition the edge set. *) |
| 123 | Lemma | `secure_antimono` | (** Secure edges decrease as coalition grows. *) |
| 147 | Lemma | `cycle_ramp_loss` | (** In the cycle graph, losing any party from the full coalition leaves at least some edges uncovered (secure). *) |
| 169 | Lemma | `cycle_full_recovery` | (** The full coalition on the cycle recovers all edges. *) |
| 183 | Lemma | `complete_ramp_max` | (** On the complete graph, the full coalition recovers the maximum number of bits: every pair of distinct parties contributes. *) |
| 216 | Lemma | `secure_edge_witness` | (** For each secure edge, at least one endpoint is not in C. *) |
| 235 | Theorem | `secure_edge_bound` | (** For each secure edge, the adversary cannot distinguish the encoded bit from random. The var_dist bound from the collusion bound applies per component via DPI. This is a structural statement: the … |
| 252 | Theorem | `ramp_security_reconstruction` | (** Summary: the ramp scheme provides both reconstruction and security. - For covered edges: the coalition can reconstruct the encoded bits (via decode_encode_correct from pgg_deck_pairing) - For sec… |
| 286 | Theorem | `ramp_config_threshold` | Theorem ramp_config_threshold (C : {set 'I_T}) : |
| 293 | Theorem | `ramp_config_mono` | Theorem ramp_config_mono (C C' : {set 'I_T}) : |

### `reconstruct/pgl_bound.v` (12)

| Line | Kind | Name | Tells us / Statement |
|---:|---|---|---|
| 56 | Lemma | `card_gl2` | (* GL(2,q) cardinality: q * (q-1)^2 * (q+1) *) |
| 77 | Lemma | `scalar_pred_group_set` | Lemma scalar_pred_group_set : group_set [set u : {'GL_2[F]} \| scalar_pred u]. |
| 94 | Lemma | `scalar_gl2_subset_center` | (* Scalar matrices commute with everything, so scalar_gl2 is in the center *) |
| 107 | Lemma | `scalar_gl2_normal` | (* Scalar matrices are normal in GL(2,F) — they commute with everything *) |
| 117 | Lemma | `scalar_unit_in_gl` | (* Key helper: scalar matrix of a unit is in GL *) |
| 125 | Lemma | `card_scalar_gl2` | (* Cardinality of the scalar subgroup equals q-1 = \|F^*\| *) |
| 164 | Lemma | `card_pgl2` | (* Cardinality of PGL(2,q) *) |
| 193 | Lemma | `pgl2_card_formula` | (* The combinatorial formula q * (q^2 - 1) matches the pgl_bound definition from cover_tradeoff.v *) |
| 211 | Lemma | `pgl_card_eq` | (** pgl_card_eq — equational identity [#\|pgl2 F\| = pgl_card #\|F\|] for any [finFieldType] [F]. Kind: helper. Why: repackages [pgl2_card_formula] as a definitional rewrite lemma so later instance proof… |
| 219 | Lemma | `pgl_card_5` | (** pgl_card_5 — numerical instance [pgl_card 5 = 120]. Definitionally true. Kind: helper. Why: used in combination with [card_set_S5] to identify the PGL(2,F_5) order with the order of [S_5], which … |
| 229 | Lemma | `card_set_S5` | (** card_set_S5 — [#\|[set: 'S_5]\| = 120], i.e. the order of the symmetric group on five letters. Kind: helper. Why: standard cardinality fact expressed in the [{set: _}] form so it can be chained wit… |
| 240 | Lemma | `pgl2_5_eq_s5` | (** pgl2_5_eq_s5 — bridge equation [pgl_card 5 = #\|[set: 'S_5]\|]; identifies the PGL(2,F_5) cardinality with the order of S_5. Kind: helper. Why: exposes the PGL(2,F_5)-vs-S_5 isomorphism at the card… |

### `reconstruct/product_threshold.v` (13)

| Line | Kind | Name | Tells us / Statement |
|---:|---|---|---|
| 41 | Lemma | `addn_leq_muln` | (* N1, N2 >= 2 implies N1 + N2 <= N1 * N2 *) |
| 54 | Lemma | `divn_lt_N2` | (* s div N1 < N2 for any s < N *) |
| 69 | Lemma | `combine_splitK` | Lemma combine_splitK (s : 'I_N) : |
| 77 | Lemma | `split_combineK` | (* Partial cancel: holds when s1 + N1 * s2 < N *) |
| 120 | Lemma | `embed_pile2_proof` | Lemma embed_pile2_proof (x : 'I_N2) : N1 + val x < N. |
| 135 | Lemma | `pile1_idx_lt` | (* Index embedding: pile-1 party index i < T1 -> product index i < T *) |
| 139 | Lemma | `pile2_idx_lt` | (* Index embedding: pile-2 party index i < T2 -> product index T1+i < T *) |
| 173 | Lemma | `product_correct` | (* --- Correctness --- *) |
| 187 | Lemma | `product_private` | (* Both parts have cardinality bounded by \|C\| *) |
| 288 | Lemma | `product_encode_valid` | (* --- Encode validity --- *) |
| 324 | Lemma | `T_gt1` | (* T >= 2 since T1, T2 >= 1 *) |
| 328 | Lemma | `k_gt0` | (* k >= 1 since k1, k2 >= 1 *) |
| 380 | Lemma | `product_sum_mod_perm_compatible` | (* When T1 + T2 = N (parties = sheets), perm_compatible holds because: 1. sigma preserves piles (preserves_pile1) 2. permuting shares within a pile preserves the pile sum 3. sum_mod_recon only depend… |

### `reconstruct/rs_code_5sheets.v` (11)

| Line | Kind | Name | Tells us / Statement |
|---:|---|---|---|
| 29 | Lemma | `prime5` | (******************************************************************************) |
| 31 | Lemma | `char_GF5` | Lemma char_GF5 : (5%:R : GF 0 prime5) = 0. |
| 34 | Lemma | `card_GF5` | Lemma card_GF5 : #\|GF 0 prime5\| = 5. |
| 38 | Lemma | `nat_inj_GF5_neq0` | (* Identity helper: for 0 < n < 5, n%:R != 0 in GF(5). *) |
| 45 | Lemma | `expr_2_mod_5` | (* Powers of 2 reduce mod 5. *) |
| 55 | Lemma | `small_nat_neq0_GF5` | (* Helper: if n is in {1,2,3,4} (i.e., 1 <= n < 5), then n%:R != 0 in GF(5). *) |
| 64 | Lemma | `nat_minus1_neq0_GF5` | (* in GF(5). *) |
| 75 | Lemma | `prim_root_prim4_GF5` | Lemma prim_root_prim4_GF5 : 4.-primitive_root (2%:R : GF 0 prime5). |
| 105 | Lemma | `qn5_4` | Lemma qn5_4 : ~~ (5 %\| 4)%N. Proof. by []. Qed. |
| 113 | Lemma | `trivial_sigma_fix0` | Lemma trivial_sigma_fix0 (M : MonodromyReprType) : |
| 123 | Lemma | `trivial_sigma_auto` | Lemma trivial_sigma_auto (M : MonodromyReprType) : |

### `reconstruct/rs_massey_bridge.v` (8)

| Line | Kind | Name | Tells us / Statement |
|---:|---|---|---|
| 54 | Lemma | `transport_correct` | Lemma transport_correct (s : B) (shares : T'.+1.-tuple B) : |
| 61 | Lemma | `transport_private` | Lemma transport_private (s1 s2 : B) (shares : T'.+1.-tuple B) |
| 90 | Lemma | `transport_encode_valid` | Lemma transport_encode_valid (s : B) : |
| 106 | Lemma | `transport_exact` | Lemma transport_exact : |
| 149 | Lemma | `rs_massey_exact` | (* With d = 1 and the strong privacy bound, ts_T' = ts_k' = n''.+1 *) |
| 177 | Lemma | `ofFK` | Lemma ofFK : cancel ofF toF. |
| 180 | Lemma | `toFK` | Lemma toFK : cancel toF ofF. |
| 187 | Lemma | `rs_genus0_exact` | Lemma rs_genus0_exact : |

### `reconstruct/rs_privacy.v` (3)

| Line | Kind | Name | Tells us / Statement |
|---:|---|---|---|
| 56 | Lemma | `poly_eval_in_code` | (* An evaluation vector of a polynomial of degree < n-d is a codeword *) |
| 129 | Lemma | `rs_privacy_surj` | (* Main result: privacy surjectivity for RS codes. For any set S with \|S\| < (n-d)+1 (= dim(C)+1) and any target vector, there exists a codeword agreeing with target on S. Proof strategy: 1. Extract t… |
| 167 | Lemma | `rs_privacy_surj_massey` | (* Corollary: instantiate massey_scheme for RS codes *) |

## `security/` (163 decls)

### `security/pgg_abelian_collapse.v` (4)

| Line | Kind | Name | Tells us / Statement |
|---:|---|---|---|
| 48 | Lemma | `one_eval_determines_perm` | Lemma one_eval_determines_perm (g1 g2 : gT) (s : 'I_N) : |
| 78 | Lemma | `word_eval_in_G` | (* Helper: word_eval produces elements of G *) |
| 87 | Lemma | `abelian_adversary_full_recovery` | (* Item 4: Adversary seeing one endpoint determines the group element. For words w1, w2: if endpoint(word_eval w1)(s) = endpoint(word_eval w2)(s), then word_eval w1 = word_eval w2. *) |
| 95 | Theorem | `abelian_security_collapse` | (* Security collapse: search space bounded by frequency vector count *) |

### `security/pgg_collusion_bound.v` (32)

| Line | Kind | Name | Tells us / Statement |
|---:|---|---|---|
| 40 | Lemma | `var_dist_triangle` | Lemma var_dist_triangle (P Q M : R.-fdist A) : |
| 69 | Lemma | `var_dist_fdistmap` | (* endpoint bounds from group-level spectral analysis. *) |
| 102 | Lemma | `var_dist_uniform_supp` | Lemma var_dist_uniform_supp : |
| 189 | Lemma | `ideal_marginal_uniform` | (* Key lemma: the pushforward of uniform(S_N) through evaluation is uniform(I_N) *) |
| 227 | Theorem | `collusion_bound_unconditional` | (* Main unconditional bound: var_dist(adv, uniform) <= epsilon *) |
| 239 | Theorem | `collusion_bound` | (* The stronger statement including the 2(T-1)/N term from conditioning. When the adversary conditions on T-1 observed values, the ideal conditional distribution is uniform over N-(T-1) remaining val… |
| 293 | Lemma | `Hcard_remaining` | Lemma Hcard_remaining : #\|remaining\| = (N - T')%N. |
| 296 | Theorem | `collusion_bound_conditional` | Theorem collusion_bound_conditional : |
| 325 | Lemma | `fdistmap_eval_uniform` | Lemma fdistmap_eval_uniform (s : 'I_N) : |
| 388 | Lemma | `fdistmap_inj_uniform` | Lemma fdistmap_inj_uniform : |
| 445 | Lemma | `card_word_L` | (* Cardinality of word space *) |
| 460 | Lemma | `achievable_pos` | (* achievable(L) has positive cardinality *) |
| 469 | Lemma | `rho_from_words_uniform_supp` | (* Key: rho_from_words is uniform_supp over achievable(L) *) |
| 521 | Lemma | `card_word_L'` | Lemma card_word_L' : |
| 534 | Lemma | `fiber_prob` | (* The probability of g under rho_from_words equals \|fiber g\| / Tg^L *) |
| 547 | Lemma | `weval_inj_fiber_le1` | (* Under word-eval injectivity, each fiber has at most one element *) |
| 556 | Lemma | `weval_inj_fiber_card1` | (* Under word-eval injectivity, fibers of achievable elements are singletons *) |
| 614 | Theorem | `collusion_bound_k` | (* Main theorem: DPI gives the bound for joint observations *) |
| 646 | Lemma | `fdistmap_uniform_supp_inj` | (* When f is injective on C, the pushforward of uniform_supp(C) through f is uniform_supp(f(C)). This is the key lemma for direct endpoint epsilon. *) |
| 711 | Lemma | `direct_eps_ge0` | Lemma direct_eps_ge0 : 0 <= direct_eps. |
| 718 | Lemma | `achievable_card_TgL` | Lemma achievable_card_TgL : #\|@achievable M L\| = (Tg ^ L)%N. |
| 724 | Lemma | `achievable_pos'` | Lemma achievable_pos' : (0 < #\|@achievable M L\|)%N. |
| 728 | Lemma | `perm_endpoint_image_card` | (* The image of achievable through eval_at s has cardinality Tg^L *) |
| 738 | Lemma | `perm_endpoint_image_pos` | Lemma perm_endpoint_image_pos (s : 'I_N) : |
| 742 | Lemma | `TgL_leq_N` | Lemma TgL_leq_N : (Tg ^ L <= N)%N. |
| 752 | Theorem | `var_dist_endpoint_direct` | (* Direct endpoint bound: for each sheet s, the marginal endpoint distribution is at distance 2*(N-Tg^L)/N from uniform. This is TIGHTER than the DPI bound 2*(N!-Tg^L)/N!. *) |
| 802 | Lemma | `var_dist_fdistmap_balanced` | (* The balanced-case var_dist formula. When \|C\| = \|B\|, fibers partition C into \|B\| groups summing to \|C\| = \|B\|. The var_dist only depends on how many groups are empty (= \|B\| - \|image\|). *) |
| 893 | Lemma | `var_dist_fdistmap_unbalanced` | Lemma var_dist_fdistmap_unbalanced : |
| 988 | Lemma | `var_dist_endpoint_unbalanced` | Lemma var_dist_endpoint_unbalanced |
| 1003 | Lemma | `var_dist_endpoint_image_bound_unbalanced` | Lemma var_dist_endpoint_image_bound_unbalanced |
| 1042 | Lemma | `var_dist_endpoint_balanced` | (* When Tg^L = N (balanced), the fiber-counted var_dist reduces to the image-size formula 2*(N - \|image_s\|)/N. *) |
| 1057 | Lemma | `var_dist_endpoint_image_bound` | (* The key corollary: bound var_dist by bounding \|image_s\| from below *) |

### `security/pgg_entropy_security.v` (13)

| Line | Kind | Name | Tells us / Statement |
|---:|---|---|---|
| 161 | Lemma | `entropy_uniform_supp` | Lemma entropy_uniform_supp : |
| 194 | Lemma | `entropy_fdistmap_uniform_supp` | Lemma entropy_fdistmap_uniform_supp : |
| 294 | Lemma | `fiber_entropy_general` | (* General fiber entropy formula (works for ALL groups with weval_inj): H(P_s) = log(Tg^L) - (Tg^L)^{-1} sum_{x in img_s} c_x log c_x where c_x = \|{sigma in achievable : sigma(s) = x}\|. Injective cas… |
| 317 | Lemma | `fiber_entropy_injective` | (* When weval_inj AND perm_endpoint is injective on achievable(L): H(P_s) = log(Tg^L). Proof sketch: weval_inj -> rho_from_words = uniform_supp(achievable), pe_inj -> pushforward is uniform_supp(imag… |
| 335 | Lemma | `fiber_entropy_perfect` | (* Perfect security: H(P_s) = log N (maximum entropy, zero leakage). Requires weval_inj + pe_inj + the saturation condition Tg^L = N. When Tg^L = N, the achievable permutations cover all N sheets inj… |
| 344 | Lemma | `fiber_entropy_le_logN` | (* Upper bound: H(P_s) <= log N always holds (entropy_max). *) |
| 388 | Lemma | `fiber_entropy_gap` | (* Fundamental identity: the entropy gap equals the KL divergence from the uniform distribution. This is the standard D(P\|\|U) = log\|X\| - H(P) identity, specialized to the endpoint distribution P_s. *) |
| 441 | Lemma | `var_dist_from_fiber_entropy` | (* Pinsker bridge: entropy bound -> var_dist bound. Combines fiber_entropy_gap (D = log N - H) with Pinsker's inequality (var_dist <= sqrt(2*D)) to get var_dist <= sqrt(2*(log N - H)). *) |
| 491 | Lemma | `Endpoint_RV_entropy` | (* The entropy of Endpoint_RV equals fiber_entropy: both compute H(fdistmap (sigma \|-> sigma(s)) rho_from_words), just via different factorizations of the word -> permutation -> endpoint pipeline. *) |
| 684 | Lemma | `joint_entropy_le_log_words` | (* Upper bound: H(joint) <= log(Tg^L). The joint distribution is a pushforward of a distribution on Tg^L words, so its support has at most Tg^L elements. *) |
| 714 | Lemma | `joint_entropy_le_T_logN` | (* Trivial upper bound: H(joint) <= T * log N. Each coordinate has entropy at most log N, and H(X_1,...,X_T) <= sum H(X_i) by subadditivity. *) |
| 725 | Lemma | `joint_entropy_single` | (* Single-party consistency: when T = 1, joint_fiber_entropy reduces to fiber_entropy at the single party's sheet. *) |
| 761 | Lemma | `joint_entropy_full` | (* Maximum entropy: H = log(Tg^L) when weval_inj AND T-fold endpoint injectivity both hold. - weval_inj ensures rho_from_words = uniform on achievable (Tg^L elements) - T-fold injectivity ensures joi… |

### `security/pgg_entropy_security_demo.v` (12)

| Line | Kind | Name | Tells us / Statement |
|---:|---|---|---|
| 55 | Lemma | `monster_entropy_perfect` | (* Perfect entropy: H(P_s) = log N at every sheet *) |
| 68 | Lemma | `monster_entropy_eps_perfect` | (* eps = 0 under saturation *) |
| 93 | Lemma | `monster_entropy_short_L` | (* H(P_s) = log(2^L) at every sheet when pe_inj holds *) |
| 98 | Lemma | `monster_leakage_short_L` | (* Leakage = D(P_s \|\| U_N) *) |
| 154 | Lemma | `oc_one_le_two_log2` | (* 1 <= 2 * (log 4 - log 2). In base-2 logarithm: log 2 = 1, log 4 = 2, so 2 * (2 - 1) = 2 >= 1. *) |
| 160 | Lemma | `oc_combinatorial_eps` | (* sw_bound_eps(oc_security_witness_2) = 1 by definition of security_witness_fiber applied to oc_endpoint_bound_fiber (eps=1). *) |
| 181 | Lemma | `oc_entropy_bound` | (* Entropy lower bound from axiom *) |
| 199 | Lemma | `oc_entropy_vs_combinatorial` | (* Combinatorial bound (eps=1) is tighter than entropy bound (eps=sqrt 2). eps_combinatorial = 1, eps_entropy = sqrt(2*(log 4 - log 2)) = sqrt 2. Since 1 <= sqrt 2, the combinatorial bound is tighter… |
| 239 | Lemma | `oc_convergence_perfect` | (* When H_min reaches log N = log 4, perfect security *) |
| 263 | Lemma | `entropy_security_eps` | (* Extract the epsilon formula *) |
| 269 | Lemma | `entropy_security_perfect` | (* Perfect security when H = log N *) |
| 275 | Lemma | `entropy_security_monotone` | (* Monotonicity: larger H_min -> smaller eps *) |

### `security/pgg_mixing.v` (27)

| Line | Kind | Name | Tells us / Statement |
|---:|---|---|---|
| 63 | Lemma | `cauchy_schwarz_bigR` | (* Lagrange identity route: A * C - B^2 = (1/2) * sum_{i,j} (v_i w_j - v_j w_i)^2 >= 0. *) |
| 112 | Lemma | `var_dist_le_sqrtN_norm2` | (* For any two distributions P, Q over a finite set of size N, var_dist(P, Q) = sum_a \|P a - Q a\| <= sqrt(N) * sqrt(sum_a (P a - Q a)^2) by Cauchy-Schwarz applied to constant 1 against \|P - Q\|. *) |
| 153 | Lemma | `cV_innerE` | Lemma cV_innerE (v w : 'cV[R]_N) : |
| 157 | Lemma | `cV_inner_sym` | Lemma cV_inner_sym (v w : 'cV[R]_N) : cV_inner v w = cV_inner w v. |
| 163 | Lemma | `cV_inner_ge0` | Lemma cV_inner_ge0 (v : 'cV[R]_N) : 0 <= cV_inner v v. |
| 166 | Lemma | `cV_inner_self_sum` | Lemma cV_inner_self_sum (v : 'cV[R]_N) : |
| 171 | Lemma | `cV_inner_Qv_Qv` | (* \|\|Q v\|\|^2 = <Q v, Q v> = v^T Q^T Q v. When Q^T = Q this equals v^T Q^2 v. *) |
| 178 | Lemma | `cV_inner_Qv_Qv_symm` | Lemma cV_inner_Qv_Qv_symm (Q : 'M[R]_N) (v : 'cV[R]_N) : |
| 202 | Lemma | `sum_Qv_zero` | (* For a sum-zero column vector v (i.e. sum_i v_i = 0), Q *m v also has sum zero. *) |
| 228 | Lemma | `symm_ds_step_norm_sq_bound` | (* Step 1: <Q v, Q v> <= alpha^2 * <v, v> for v in 1-perp. *) |
| 238 | Lemma | `symm_ds_power_norm_sq_bound` | (* Iterated power: <Q^L v, Q^L v> <= alpha^{2L} * <v, v> for v in 1-perp. *) |
| 314 | Lemma | `Q_fixes_uniform` | (* Q takes uniform to uniform (Q is row-stochastic => Q * 1 = 1 => Q U = U). *) |
| 327 | Lemma | `e_cV_sum` | Lemma e_cV_sum (s : 'I_N) : \sum_i (e_cV s) i ord0 = 1. |
| 334 | Lemma | `uniform_cV_sum` | Lemma uniform_cV_sum : \sum_i uniform_cV i ord0 = 1. |
| 343 | Lemma | `es_minus_U_sum_zero` | (* The centred vector v_s := e_s - U has sum zero. *) |
| 356 | Lemma | `es_minus_U_norm_sq` | (* <e_s - U, e_s - U> = 1 - 1/N. *) |
| 379 | Lemma | `es_minus_U_norm_sq_le1` | Lemma es_minus_U_norm_sq_le1 (s : 'I_N) : |
| 389 | Lemma | `vec_norm2_ge0` | Lemma vec_norm2_ge0 (v : 'cV[R]_N) : 0 <= vec_norm2 v. |
| 393 | Lemma | `symm_ds_power_norm2_bound` | (* Task 1: sqrt of the power norm bound. *) |
| 414 | Lemma | `Q_power_fixes_uniform` | (* Q^L also fixes the uniform vector. *) |
| 423 | Lemma | `cV_l1_le_sqrtN_norm2` | (* L^1 to L^2 bridge for column vectors. *) |
| 450 | Lemma | `es_minus_U_norm2_le1` | (* The L^2 norm of e_s - U is at most 1. *) |
| 462 | Lemma | `symm_ds_TV_bound_cV` | (* Task 2 (column-vector form): the main TV bound, in vector form. Combines L1-to-L2 bridge, the sqrt'd power bound, and \|\|e_s - U\|\|_2 <= 1. *) |
| 512 | Lemma | `schreier_transition_symm` | (* Task 3: under self-inverse generators, the Schreier transition is symmetric. *) |
| 535 | Lemma | `schreier_transition_doubly_stochastic_col` | (* Task 4: column sum equals 1, completing doubly stochastic. *) |
| 552 | Lemma | `schreier_endpoint_eq_Q_power` | (* Task 5: bridge from fdistmap-of-rho to the (Q^L *m e_s) column entry. *) |
| 597 | Lemma | `symm_ds_TV_bound` | Lemma symm_ds_TV_bound (alpha : R) (L : nat) (s : 'I_N) : |

### `security/pgg_schreier.v` (10)

| Line | Kind | Name | Tells us / Statement |
|---:|---|---|---|
| 182 | Lemma | `schreier_transition_entry_ge0` | (* All entries are non-negative *) |
| 193 | Lemma | `schreier_transition_stochastic` | (* Each row sums to 1 (row-stochastic). Proof: for each generator sigma_k and sheet x, there is exactly one y such that sigma_k(x) = y (namely y = sigma_k(x)). So the total count across all y is Tg. … |
| 305 | Lemma | `convergence_rate_ge0` | Lemma convergence_rate_ge0 (sc : SchreierCertificate) : |
| 312 | Lemma | `convergence_rate_lt1` | Lemma convergence_rate_lt1 (sc : SchreierCertificate) : |
| 351 | Lemma | `schreier_epsilon_ge0` | (* Epsilon is non-negative *) |
| 371 | Lemma | `schreier_epsilon_decreasing` | (* The UPPER BOUND schreier_epsilon is monotonically decreasing in L. sqrt(N) * r^L2 <= sqrt(N) * r^L1 when 0 <= r < 1, L1 <= L2. Follows from r^(a+b) = r^a * r^b and r^b <= 1 for 0 <= r <= 1. IMPORT… |
| 385 | Lemma | `security_monotone` | (* Monotone security: if secure at L1, at least as secure at L2 >= L1 *) |
| 432 | Lemma | `word_eval_cons` | Lemma word_eval_cons (L : nat) (i : 'I_Tg) (w : L.-tuple 'I_Tg) : |
| 442 | Lemma | `word_eval_cons_endpoint` | Lemma word_eval_cons_endpoint (L : nat) (i : 'I_Tg) (w : L.-tuple 'I_Tg) |
| 448 | Lemma | `schreier_walk_eq_endpoint` | Lemma schreier_walk_eq_endpoint : forall (L : nat) |

### `security/pgg_schreier_weighted.v` (17)

| Line | Kind | Name | Tells us / Statement |
|---:|---|---|---|
| 78 | Lemma | `schreier_weighted_entry_ge0` | (* All entries are non-negative *) |
| 89 | Lemma | `schreier_weighted_stochastic` | (* Each row sums to 1 (row-stochastic). Proof: partition generators by target sheet, then use FDist.f1. For each generator i, there is exactly one y = sigma_i(x), so sum_y sum_{i:sigma_i(x)=y} W(i) =… |
| 102 | Lemma | `schreier_weighted_uniform` | (* When W is uniform (W(i) = 1/Tg for all i), the weighted transition matrix recovers the original schreier_transition. *) |
| 163 | Lemma | `weighted_convergence_rate_ge0` | Lemma weighted_convergence_rate_ge0 (wsc : WeightedSchreierCertificate) : |
| 170 | Lemma | `weighted_convergence_rate_lt1` | Lemma weighted_convergence_rate_lt1 (wsc : WeightedSchreierCertificate) : |
| 183 | Lemma | `weighted_schreier_epsilon_ge0` | (* Epsilon is non-negative *) |
| 193 | Lemma | `weighted_schreier_epsilon_decreasing` | (* Epsilon is monotonically decreasing in L *) |
| 209 | Lemma | `weighted_security_monotone` | (* Monotone security: if secure at L1, at least as secure at L2 >= L1 *) |
| 254 | Lemma | `schreier_weighted_bridge` | Lemma schreier_weighted_bridge : forall (L : nat) (s x : 'I_N), |
| 380 | Lemma | `unif_offdiag_row_sum` | (** Row stochastic follows from column stochastic + uniform-off-diagonal: a + (N-1)*b = 1. We derive this rather than assuming it. *) |
| 390 | Lemma | `unif_offdiag_ab` | (** a - b = 1 - N * b *) |
| 400 | Lemma | `unif_offdiag_key_identity` | (** Key identity: (a - b) / N + b = 1/N *) |
| 408 | Lemma | `doubly_stochastic_power` | (** Column sums of Q^L are 1 (doubly stochastic is preserved under powers) *) |
| 424 | Lemma | `unif_offdiag_power_entry` | (** Q^L entries for uniform-off-diagonal matrices *) |
| 451 | Lemma | `unif_offdiag_var_dist` | (** Exact variation distance formula *) |
| 474 | Lemma | `two_Nm1_div_N_le_sqrtN` | (** The prefactor 2*(N-1)/N is at most sqrt(N) for N >= 2 *) |
| 498 | Lemma | `unif_offdiag_convergence` | (** Convergence bound *) |

### `security/pgg_security.v` (13)

| Line | Kind | Name | Tells us / Statement |
|---:|---|---|---|
| 29 | Lemma | `isqrt_aux_lower` | (* --- auxiliary lemmas on isqrt_aux --- *) |
| 36 | Lemma | `isqrt_aux_ge` | Lemma isqrt_aux_ge fuel k n : k <= isqrt_aux fuel k n. |
| 43 | Lemma | `isqrt_aux_upper` | Lemma isqrt_aux_upper fuel k n : |
| 55 | Lemma | `isqrt_aux_largest` | Lemma isqrt_aux_largest fuel k n m : |
| 79 | Lemma | `isqrt_lower` | (* --- main properties of isqrt --- *) |
| 82 | Lemma | `isqrt_upper` | Lemma isqrt_upper n : n < (isqrt n).+1 ^ 2. |
| 85 | Lemma | `isqrt_monotone` | Lemma isqrt_monotone m n : m <= n -> isqrt m <= isqrt n. |
| 98 | Lemma | `isqrt_expn` | Lemma isqrt_expn k : k <= isqrt (k ^ 2). |
| 116 | Lemma | `kappa_gt0` | Lemma kappa_gt0 : 0 < kappa. |
| 125 | Lemma | `kappa_sq_L` | (* ========================================================================== *) |
| 128 | Theorem | `grover_mitigation` | Theorem grover_mitigation (L : nat) : |
| 144 | Theorem | `security_exponential` | (* ========================================================================== *) |
| 153 | Theorem | `security_storage_match` | (* Combined: security and storage grow as Theta(kappa^L) *) |

### `security/pgg_security_solver.v` (4)

| Line | Kind | Name | Tells us / Statement |
|---:|---|---|---|
| 104 | Lemma | `epsilon_endpoint_rat_consistent` | (******************************************************************************) |
| 109 | Lemma | `epsilon_endpoint_rat_sp_consistent` | Lemma epsilon_endpoint_rat_sp_consistent Tg N L : |
| 122 | Lemma | `sp_consistent_endpoint` | Lemma sp_consistent_endpoint Tg N L : |
| 134 | Lemma | `solve_consistent` | Lemma solve_consistent c p : solve c = Some p -> sp_consistent p. |

### `security/pgg_uniform_security.v` (8)

| Line | Kind | Name | Tells us / Statement |
|---:|---|---|---|
| 58 | Lemma | `fdist_uniform_supp_setT` | Lemma fdist_uniform_supp_setT : |
| 77 | Lemma | `var_dist_self` | Lemma var_dist_self (P : R.-fdist A) : var_dist P P = 0. |
| 124 | Lemma | `img_pos` | Lemma img_pos (s : 'I_N) : (0 < #\|img s\|)%N. |
| 132 | Lemma | `img_setT` | (* Key: the image is all of 'I_N *) |
| 136 | Lemma | `eval_pushforward` | (* The pushforward of uniform(rhoG) through eval_at s is uniform(img s) *) |
| 145 | Lemma | `eval_pushforward_uniform` | (* The pushforward equals fdist_uniform *) |
| 155 | Lemma | `endpoint_bound` | (* The endpoint bound: var_dist = 0 <= 0 *) |
| 164 | Lemma | `endpoint_exact` | (* The exact endpoint equality: var_dist = 0 *) |

### `security/pgg_weighted_entropy.v` (2)

| Line | Kind | Name | Tells us / Statement |
|---:|---|---|---|
| 57 | Lemma | `KL_div_uniform` | Lemma KL_div_uniform : |
| 113 | Lemma | `var_dist_from_weighted_entropy` | Lemma var_dist_from_weighted_entropy (s : 'I_N) : |

### `security/pgg_weighted_words.v` (4)

| Line | Kind | Name | Tells us / Statement |
|---:|---|---|---|
| 72 | Lemma | `word_weightedE` | (* Probability of each word under the weighted distribution *) |
| 88 | Lemma | `fiber_prob_weighted` | (* The probability of g under the weighted distribution *) |
| 129 | Lemma | `word_weighted_is_uniform` | (* When W is uniform, each word gets probability (1/Tg)^L = 1/Tg^L, which is the uniform distribution on L-tuples. *) |
| 139 | Lemma | `rho_weighted_is_uniform` | Lemma rho_weighted_is_uniform : |

### `security/pgg_word_analysis.v` (17)

| Line | Kind | Name | Tells us / Statement |
|---:|---|---|---|
| 62 | Lemma | `comm_pair_count_bound` | (* Upper bound: at most L-1 adjacent pairs *) |
| 76 | Lemma | `edge_count_sym` | Lemma edge_count_sym : edge_count = |
| 89 | Lemma | `edge_count_even` | (* edge_count is even: the swap involution (i,j) <-> (j,i) has no fixed points on commuting pairs (since comm is irreflexive), so the set partitions into pairs. *) |
| 131 | Lemma | `adj_swap_symmetric` | (* Helper: adj_swap w' w implies adj_swap w w' (adj_swap is symmetric). If w = swap_word k w', then w' = swap_word k w, and the commutation condition at positions k,k+1 is preserved (by comm_sym and … |
| 170 | Lemma | `comm_pair_count_zero_adj_swap` | (* If no adjacent generators in w commute, then no adjacent swap is possible, so the trace class of w is the singleton {w}. *) |
| 185 | Lemma | `comm_pair_count_zero_adj_swap_sym` | (* The symmetric closure of adj_swap is also false when comm_pair_count = 0 *) |
| 196 | Lemma | `comm_pair_count_zero_root` | (* Words with zero commuting pairs are their own trace roots *) |
| 217 | Lemma | `comm_pair_count_zero_singleton` | (* The trace equivalence class of a zero-count word is a singleton *) |
| 237 | Lemma | `comm_pair_count_full_comm` | (* When all distinct generators commute and L >= 2, we have comm_pair_count w = L.-1 (every adjacent pair commutes, unless two adjacent generators happen to be equal, in which case comm is false by i… |
| 260 | Lemma | `adj_swap_comm_pair_diff` | (* An adjacent swap at position k changes comm_pair_count by at most 2 (one pair created/destroyed at k, and adjacent pairs at k-1 and k+1 may be affected). This is a structural observation. *) |
| 343 | Lemma | `card_pgg_word` | (* Total number of words of length L *) |
| 347 | Lemma | `card_pgg_word_pos` | (* For fdist_uniform, we need the (n.+1) form *) |
| 351 | Lemma | `card_pgg_word_succ` | Lemma card_pgg_word_succ (L : nat) : |
| 415 | Lemma | `fiber_count_card` | Lemma fiber_count_card (a b : T) : |
| 450 | Lemma | `total_comm_pairs` | (* The total number of (word, commuting-position) pairs. For each position k < L-1, the pair (w_k, w_{k+1}) is drawn from Tg * Tg generators, and there are Tg^(L-2) choices for the remaining position… |
| 521 | Lemma | `zero_comm_pair_traces` | (* Number of trace classes containing words with zero commuting pairs *) |
| 534 | Lemma | `zero_comm_words_are_traces` | (* Lower bound: words with no commuting adjacent pairs contribute directly to trace count *) |

