From mathcomp Require Import all_ssreflect ssralg.

Import GRing.Theory.

Local Open Scope ring_scope.

Section RSS_Mult_Identity.

Variable R : comRingType.

(** rss_mul_cross_E — cross-term identity for 3-party RSS multiplication.

    Each party Pi locally computes its additive share of x*y as
       z_i = x_i * y_i + x_i * y_{i+1} + x_{i+1} * y_i    (indices mod 3).
    Sum_i z_i = (x_1 + x_2 + x_3) * (y_1 + y_2 + y_3).

    Kind: main.
    Why: multiplication-correctness backbone of the RSS protocol from
    dumas2017dual/notes/20260428-3party-it-secure-scalar-product-rss.md. *)
Lemma rss_mul_cross_E (x1 x2 x3 y1 y2 y3 : R) :
  (x1 * y1 + x1 * y2 + x2 * y1) +
  (x2 * y2 + x2 * y3 + x3 * y2) +
  (x3 * y3 + x3 * y1 + x1 * y3) =
  (x1 + x2 + x3) * (y1 + y2 + y3).
Proof. by rewrite !mulrDl !mulrDr; ring. Qed.

End RSS_Mult_Identity.
