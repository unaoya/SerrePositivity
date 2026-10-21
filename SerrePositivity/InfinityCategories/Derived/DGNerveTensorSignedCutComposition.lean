module
public import SerrePositivity.InfinityCategories.Derived.DGTensorGradedComposition
public import SerrePositivity.InfinityCategories.Derived.DGNerveTensorNativeCutSigns
/-!
概要：実切断の符号付き tensor 合成を元の HA の指数へ接続する。
方針：任意の斉次合成の Koszul 符号と有限交差の計算を照合する。
規約：元の実切断集合と cochain を使う。使われ方：全次元 tensor 候補の HA の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (B : Type v) (C : Type w) [DGCategory R B] [DGCategory R C]
/-- 同じ実切断の符号と有限和の添字の比較。 -/
lemma dgTensorElement_signed_compose {x y z : DGTensorCategory R B C} {p q r s n : ℤ}
    (f₁ : GradedHom R x.1 y.1 p) (f₂ : GradedHom R x.2 y.2 q)
    (g₁ : GradedHom R y.1 z.1 r) (g₂ : GradedHom R y.2 z.2 s)
    (hn : (p + q) + (r + s) = n) (e d base el er : ℤ)
    (he : e + d = base + el + er + p * s) :
    (e + d).negOnePow • dgTensorElement R
      (compose R g₁ f₁ rfl) (compose R g₂ f₂ rfl) (by omega) =
      base.negOnePow • compose R
        (er.negOnePow • dgTensorElement R g₁ g₂ rfl)
        (el.negOnePow • dgTensorElement R f₁ f₂ rfl) hn := by
  rw [compose_units_smul_left, compose_units_smul_right, dgTensorElement_compose R B C]
  simp only [smul_smul, ← Int.negOnePow_add]
  rw [he]
  congr 2
  ring
/-- 同じ実切断の符号と有限和の添字の比較。 -/
lemma dgNerveTensorCut_signed_compose {n : ℕ} (I S : Finset (Fin (n + 1)))
    (a b j : Fin (n + 1)) (hS : S ⊆ (I.erase a).erase b) (hj : j ∈ S)
    (hb : b ∈ I) (haj : a < j) (hjb : j < b)
    {x y z : DGTensorCategory R B C}
    (f₁ : GradedHom R x.1 y.1 (-((S.filter (· < j)).card : ℤ)))
    (f₂ : GradedHom R x.2 y.2
      (2 - ((I.filter (· ≤ j)).card : ℤ) + ((S.filter (· < j)).card : ℤ)))
    (g₁ : GradedHom R y.1 z.1 (-((S.filter (j < ·)).card : ℤ)))
    (g₂ : GradedHom R y.2 z.2
      (2 - ((I.filter (j ≤ ·)).card : ℤ) + ((S.filter (j < ·)).card : ℤ)))
    (k : ℤ) (hk :
      (-((S.filter (· < j)).card : ℤ) +
        (2 - ((I.filter (· ≤ j)).card : ℤ) + ((S.filter (· < j)).card : ℤ))) +
      (-((S.filter (j < ·)).card : ℤ) +
        (2 - ((I.filter (j ≤ ·)).card : ℤ) + ((S.filter (j < ·)).card : ℤ))) = k) :
    (dgNerveTensorCutSign I a b S +
      (((insert a (insert b S)).filter (j < ·)).card : ℤ)).negOnePow •
      dgTensorElement R (compose R g₁ f₁ rfl) (compose R g₂ f₂ rfl) (by omega) =
    ((I.filter (j < ·)).card : ℤ).negOnePow • compose R
      ((dgNerveTensorCutSign (I.filter (j ≤ ·)) j b (S.filter (j < ·))).negOnePow •
        dgTensorElement R g₁ g₂ rfl)
      ((dgNerveTensorCutSign (I.filter (· ≤ j)) a j (S.filter (· < j))).negOnePow •
        dgTensorElement R f₁ f₂ rfl) hk := by
  exact dgTensorElement_signed_compose R B C f₁ f₂ g₁ g₂ hk _ _ _ _ _
    (dgNerveTensorCutSign_native_split_exponent I S a b j hS hj hb haj hjb)
/-- 同じ実切断の符号と有限和の添字の比較。 -/
lemma dgTensorElement_signed_compose_spec {x y z : DGTensorCategory R B C}
    {p q r s kl kr kf kg n : ℤ}
    (f₁ : GradedHom R x.1 y.1 p) (f₂ : GradedHom R x.2 y.2 q)
    (g₁ : GradedHom R y.1 z.1 r) (g₂ : GradedHom R y.2 z.2 s)
    (hl : p + q = kl) (hr : r + s = kr)
    (hf : p + r = kf) (hg : q + s = kg) (hn : kl + kr = n) (ht : kf + kg = n)
    (e d base el er : ℤ) (he : e + d = base + el + er + p * s) :
    (e + d).negOnePow • dgTensorElement R
      (compose R g₁ f₁ hf) (compose R g₂ f₂ hg) ht =
      base.negOnePow • compose R
        (er.negOnePow • dgTensorElement R g₁ g₂ hr)
        (el.negOnePow • dgTensorElement R f₁ f₂ hl) hn := by
  subst kl kr kf kg
  exact dgTensorElement_signed_compose R B C f₁ f₂ g₁ g₂ hn e d base el er he
end SerrePositivity.InfinityCategories
