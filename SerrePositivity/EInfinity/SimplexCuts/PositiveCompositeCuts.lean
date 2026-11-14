module

public import SerrePositivity.EInfinity.SimplexCuts.SignedTerms
public import SerrePositivity.EInfinity.Surjection.CompositeBasis
public import SerrePositivity.EInfinity.Surjection.CompositionSigns

/-!
# 正の内側 arity の合成語の一段切断

Berger–Fresse §1.2.4–5・§2.2.6、M14 L12a の合成側の添字と値。
元の重なる分割と合成基底語を使い、同じ全次数へ移した切断項に元の合成符号を掛ける。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.SimplexCuts
open CategoryTheory
open SerrePositivity.TensorPowers
open scoped Simplicial

/-- 元の重なる分割と、元の合成語の一段切断の全添字（BF §1.2.4・§2.2.6）。 -/
abbrev PositiveCompositeCutIndex {m n d e : ℕ} (u : Surjection.BasisWord (m + 1) d)
    (_v : Surjection.BasisWord (n + 1) e) (k : Fin (m + 1)) (q : ℕ) :=
  Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) ((n + 1) + e) ×
    Cut (m + n + (d + e)) q

/-- 同じ合成基底語の長さを、切断区間の数として読む（BF §1.2.4）。 -/
def positiveCompositeCutWord {m n d e : ℕ} (u : Surjection.BasisWord (m + 1) d)
    (v : Surjection.BasisWord (n + 1) e) (k : Fin (m + 1))
    (r : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) ((n + 1) + e)) :
    Surjection.Word (m + (n + 1)) ((m + n + (d + e)) + 1) :=
  Eq.mp (congrArg (fun l => Surjection.Word (m + (n + 1)) l)
    (by omega : (m + (n + 1)) + (d + e) = (m + n + (d + e)) + 1))
    (Surjection.compositeBasisWord u v k r (by omega))

/-- C345：同じ語長の移送では、元の文字のリストは変わらない（BF §1.2.1）。 -/
lemma word_eq_mp_ofFn {r l l' : ℕ} (h : l = l') (v : Surjection.Word r l) :
    List.ofFn (Eq.mp (congrArg (fun k => Surjection.Word r k) h) v).val =
      List.ofFn v.val := by
  subst l'
  rfl

/-- C346：合成切断が使う語は、指定された元のcompositeWordそのもの（BF §1.2.4）。 -/
lemma positiveCompositeCutWord_list {m n d e : ℕ} (u : Surjection.BasisWord (m + 1) d)
    (v : Surjection.BasisWord (n + 1) e) (k : Fin (m + 1))
    (r : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) ((n + 1) + e)) :
    List.ofFn (positiveCompositeCutWord u v k r).val = Surjection.compositeWord u v k r := by
  unfold positiveCompositeCutWord
  rw [word_eq_mp_ofFn, Surjection.compositeBasisWord_list]
  omega

variable (A : Type u) [CommRing A]

/-- 合成側の同じ符号付き項を、元の総次数で読む（BF §1.2.5・§2.2.6）。 -/
def positiveCompositeCutTerm {m n d e q : ℕ} (S : SSet.{0})
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q) (x : S _⦋q⦌) :
    (power (chains A S) (m + (n + 1))).X (-((d + e + q : ℕ) : ℤ)) :=
  Surjection.compositionSign u v k c.1 •
    (eqToHom (congrArg (fun z : ℤ => (power (chains A S) (m + (n + 1))).X z)
      (by congr 1; congr 1; omega :
        -((m + n + (d + e) + q + 1 - (m + (n + 1)) : ℕ) : ℤ) =
          -((d + e + q : ℕ) : ℤ)))).hom
      (cutTerm A S c.2 (positiveCompositeCutWord u v k c.1) x)

/-- C347：退化した同じ面の項は、合成側の実際の値域でも零（BF §2.2.6）。 -/
lemma positiveCompositeCutTerm_eq_zero {m n d e q : ℕ} (S : SSet.{0})
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q) (x : S _⦋q⦌)
    (h : ¬Nondegenerate c.2 (positiveCompositeCutWord u v k c.1).val) :
    positiveCompositeCutTerm A S u v k c x = 0 := by
  unfold positiveCompositeCutTerm
  rw [cutTerm_eq_zero A S c.2 (positiveCompositeCutWord u v k c.1) h x,
    map_zero, smul_zero]

end SerrePositivity.EInfinity.SimplexCuts
