module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovOneRoofZeroRefinement

/-!
概要：細分した元の roof の零分子を、作用を保つ係数逆の底成分と厳密に揃える。
方針：後続段での底逆の一致と、同じ roof 細分の零分母・零分子の比較を使う。
規約：元の roof と係数逆の選択を保持。使われ方：同じ共通底への双加群逆の制限。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {i m : ℕ} {hi : i ≤ m} (c : NonpositiveInverseRoof R (f.map (postnikovFunctor R 1)) i m hi)

lemma postnikovZeroLayerInverse_common_zero_base
    (h₀ : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R 0)))
    {n : ℤ} {l : ℕ} {hj : i ≤ l} (e : PostnikovZeroLayerInverse R n f i l hj) :
    ∃ k, ∃ hm : m ≤ k, ∃ hl : l ≤ k,
      postnikovOneRoofZeroNumerator R f (postnikovOneRoofRefine R f c hm) =
        postnikovOneRoofZeroDenominator R f (postnikovOneRoofRefine R f c hm) ≫
          postnikovMap R (B.transition hl).hom 0 ≫ e.base := by
  let h := postnikovZeroLayerInverse_base_eventually_roof R f c h₀ e
  let k := h.choose
  let hm : m ≤ k := h.choose_spec.choose
  let hl : l ≤ k := h.choose_spec.choose_spec.choose
  have he : postnikovMap R (B.transition hm).hom 0 ≫ postnikovOneRoofZeroInverse R f c =
      postnikovMap R (B.transition hl).hom 0 ≫ e.base := h.choose_spec.choose_spec.choose_spec
  have hc : postnikovOneRoofZeroInverse R f (postnikovOneRoofRefine R f c hm) =
      postnikovMap R (B.transition hl).hom 0 ≫ e.base :=
    (postnikovOneRoofZeroInverse_refine R f c hm).trans he
  exact ⟨k, hm, hl,
    (postnikovOneRoofZeroInverse_denominator R f (postnikovOneRoofRefine R f c hm)).symm.trans
      (congrArg (fun t => postnikovOneRoofZeroDenominator R f
        (postnikovOneRoofRefine R f c hm) ≫ t) hc)⟩

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
