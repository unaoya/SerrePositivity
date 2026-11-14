module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor.DGTensorGradedComposition
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor.DGNerveTensorNativeCutSigns
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (B : Type v) (C : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R B] [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
/-- 同じ実切断の符号と有限和の添字の比較。 -/
lemma dgTensorElement_signed_compose {x y z : _root_.SerrePositivity.DifferentialGraded.DGTensorCategory R B C} {p q r s n : ℤ}
    (f₁ : _root_.SerrePositivity.DifferentialGraded.GradedHom R x.1 y.1 p) (f₂ : _root_.SerrePositivity.DifferentialGraded.GradedHom R x.2 y.2 q)
    (g₁ : _root_.SerrePositivity.DifferentialGraded.GradedHom R y.1 z.1 r) (g₂ : _root_.SerrePositivity.DifferentialGraded.GradedHom R y.2 z.2 s)
    (hn : (p + q) + (r + s) = n) (e d base el er : ℤ)
    (he : e + d = base + el + er + p * s) :
    (e + d).negOnePow • _root_.SerrePositivity.DifferentialGraded.dgTensorElement R
      (_root_.SerrePositivity.DifferentialGraded.compose R g₁ f₁ rfl) (_root_.SerrePositivity.DifferentialGraded.compose R g₂ f₂ rfl) (by omega) =
      base.negOnePow • _root_.SerrePositivity.DifferentialGraded.compose R
        (er.negOnePow • _root_.SerrePositivity.DifferentialGraded.dgTensorElement R g₁ g₂ rfl)
        (el.negOnePow • _root_.SerrePositivity.DifferentialGraded.dgTensorElement R f₁ f₂ rfl) hn := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_units_smul_left, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_units_smul_right, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgTensorElement_compose R B C]
  simp only [smul_smul, ← Int.negOnePow_add]
  rw [he]
  congr 2
  ring
/-- 同じ実切断の符号と有限和の添字の比較。 -/
lemma dgNerveTensorCut_signed_compose {n : ℕ} (I S : Finset (Fin (n + 1)))
    (a b j : Fin (n + 1)) (hS : S ⊆ (I.erase a).erase b) (hj : j ∈ S)
    (hb : b ∈ I) (haj : a < j) (hjb : j < b)
    {x y z : _root_.SerrePositivity.DifferentialGraded.DGTensorCategory R B C}
    (f₁ : _root_.SerrePositivity.DifferentialGraded.GradedHom R x.1 y.1 (-((S.filter (· < j)).card : ℤ)))
    (f₂ : _root_.SerrePositivity.DifferentialGraded.GradedHom R x.2 y.2
      (2 - ((I.filter (· ≤ j)).card : ℤ) + ((S.filter (· < j)).card : ℤ)))
    (g₁ : _root_.SerrePositivity.DifferentialGraded.GradedHom R y.1 z.1 (-((S.filter (j < ·)).card : ℤ)))
    (g₂ : _root_.SerrePositivity.DifferentialGraded.GradedHom R y.2 z.2
      (2 - ((I.filter (j ≤ ·)).card : ℤ) + ((S.filter (j < ·)).card : ℤ)))
    (k : ℤ) (hk :
      (-((S.filter (· < j)).card : ℤ) +
        (2 - ((I.filter (· ≤ j)).card : ℤ) + ((S.filter (· < j)).card : ℤ))) +
      (-((S.filter (j < ·)).card : ℤ) +
        (2 - ((I.filter (j ≤ ·)).card : ℤ) + ((S.filter (j < ·)).card : ℤ))) = k) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorCutSign I a b S +
      (((insert a (insert b S)).filter (j < ·)).card : ℤ)).negOnePow •
      _root_.SerrePositivity.DifferentialGraded.dgTensorElement R (_root_.SerrePositivity.DifferentialGraded.compose R g₁ f₁ rfl) (_root_.SerrePositivity.DifferentialGraded.compose R g₂ f₂ rfl) (by omega) =
    ((I.filter (j < ·)).card : ℤ).negOnePow • _root_.SerrePositivity.DifferentialGraded.compose R
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorCutSign (I.filter (j ≤ ·)) j b (S.filter (j < ·))).negOnePow •
        _root_.SerrePositivity.DifferentialGraded.dgTensorElement R g₁ g₂ rfl)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorCutSign (I.filter (· ≤ j)) a j (S.filter (· < j))).negOnePow •
        _root_.SerrePositivity.DifferentialGraded.dgTensorElement R f₁ f₂ rfl) hk := by
  exact dgTensorElement_signed_compose R B C f₁ f₂ g₁ g₂ hk _ _ _ _ _
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorCutSign_native_split_exponent I S a b j hS hj hb haj hjb)
/-- 同じ実切断の符号と有限和の添字の比較。 -/
lemma dgTensorElement_signed_compose_spec {x y z : _root_.SerrePositivity.DifferentialGraded.DGTensorCategory R B C}
    {p q r s kl kr kf kg n : ℤ}
    (f₁ : _root_.SerrePositivity.DifferentialGraded.GradedHom R x.1 y.1 p) (f₂ : _root_.SerrePositivity.DifferentialGraded.GradedHom R x.2 y.2 q)
    (g₁ : _root_.SerrePositivity.DifferentialGraded.GradedHom R y.1 z.1 r) (g₂ : _root_.SerrePositivity.DifferentialGraded.GradedHom R y.2 z.2 s)
    (hl : p + q = kl) (hr : r + s = kr)
    (hf : p + r = kf) (hg : q + s = kg) (hn : kl + kr = n) (ht : kf + kg = n)
    (e d base el er : ℤ) (he : e + d = base + el + er + p * s) :
    (e + d).negOnePow • _root_.SerrePositivity.DifferentialGraded.dgTensorElement R
      (_root_.SerrePositivity.DifferentialGraded.compose R g₁ f₁ hf) (_root_.SerrePositivity.DifferentialGraded.compose R g₂ f₂ hg) ht =
      base.negOnePow • _root_.SerrePositivity.DifferentialGraded.compose R
        (er.negOnePow • _root_.SerrePositivity.DifferentialGraded.dgTensorElement R g₁ g₂ hr)
        (el.negOnePow • _root_.SerrePositivity.DifferentialGraded.dgTensorElement R f₁ f₂ hl) hn := by
  subst kl kr kf kg
  exact dgTensorElement_signed_compose R B C f₁ f₂ g₁ g₂ hn e d base el er he
end SerrePositivity.InfinityCategories.Project.DerivedCategories
