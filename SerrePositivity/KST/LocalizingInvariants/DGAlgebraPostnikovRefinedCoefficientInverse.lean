module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovOneRoofRefinement
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoRoofCoefficientInverse

/-!
概要：元の π₂ の逆を選んだ段へ roof を細分し、同じ段の共通 kernel で比較する。
方針：元の線形逆を選び、細分した全三角形付き roof の係数同型へ移す。
規約：双加群射への持ち上げは未主張。使われ方：実際に両係数へ作用する共通底。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {i m : ℕ} {hi : i ≤ m} (c : NonpositiveInverseRoof R (f.map (postnikovFunctor R 1)) i m hi)
  {k : ℕ} (hm : m ≤ k)

lemma postnikovRefinedCoefficientInverse_common
    (r : (B.obj k).obj.X.homology (-2) ⟶ (A.obj i).obj.X.homology (-2))
    (hr : r ≫ homologyMap (f.app i).hom.hom (-2) =
      homologyMap (B.transition (hi.trans hm)).hom.hom (-2)) :
    postnikovTwoRoofCoefficientInverseMap R f (postnikovOneRoofRefine R f c hm) k r ≫
      homologyMap (postnikovTwoRoofNumeratorCommonKernel R f
        (postnikovOneRoofRefine R f c hm)) (-2) =
    (postnikovTwoRoofDenominatorKernelHomologyIso R f (postnikovOneRoofRefine R f c hm)).inv ≫
      homologyMap (postnikovTwoRoofDenominatorCommonKernel R f
        (postnikovOneRoofRefine R f c hm)) (-2) := by
  have he := postnikovTwoRoofCoefficientInverseMap_common R f
    (postnikovOneRoofRefine R f c hm) (le_refl k) r hr
  have hb : (B.transition (le_refl k)).hom.hom = 𝟙 (B.obj k).obj.X :=
    congrArg (fun t => t.hom.hom) (B.transition_self k)
  have ht : homologyMap (B.transition (le_refl k)).hom.hom (-2) = 𝟙 _ := by
    rw [hb, homologyMap_id]
  let e := (postnikovTwoRoofDenominatorKernelHomologyIso R f
    (postnikovOneRoofRefine R f c hm)).inv
  let b := homologyMap (postnikovTwoRoofDenominatorCommonKernel R f
    (postnikovOneRoofRefine R f c hm)) (-2)
  exact he.trans (congrArg (fun t => t ≫ b)
    ((congrArg (fun t => t ≫ e) ht).trans (Category.id_comp e)))

lemma exists_postnikovRefinedCoefficientInverse
    (hf : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R 2))) :
    ∃ k, ∃ hm : m ≤ k,
      ∃ r : (B.obj k).obj.X.homology (-2) ⟶ (A.obj i).obj.X.homology (-2),
      homologyMap (f.app k).hom.hom (-2) ≫ r =
        homologyMap (A.transition (hi.trans hm)).hom.hom (-2) ∧
      r ≫ homologyMap (f.app i).hom.hom (-2) =
        homologyMap (B.transition (hi.trans hm)).hom.hom (-2) ∧
      postnikovTwoRoofCoefficientInverseMap R f (postnikovOneRoofRefine R f c hm) k r ≫
        homologyMap (postnikovTwoRoofNumeratorCommonKernel R f
          (postnikovOneRoofRefine R f c hm)) (-2) =
      (postnikovTwoRoofDenominatorKernelHomologyIso R f (postnikovOneRoofRefine R f c hm)).inv ≫
        homologyMap (postnikovTwoRoofDenominatorCommonKernel R f
          (postnikovOneRoofRefine R f c hm)) (-2) := by
  let h := exists_nonpositiveHomologyInverse_after R f 2 hf i m
  let k := h.choose
  let hk : i ≤ k := h.choose_spec.choose
  have hs : m ≤ k ∧ ∃ r : (B.obj k).obj.X.homology (-2) ⟶ (A.obj i).obj.X.homology (-2),
      homologyMap (f.app k).hom.hom (-2) ≫ r = homologyMap (A.transition hk).hom.hom (-2) ∧
      r ≫ homologyMap (f.app i).hom.hom (-2) = homologyMap (B.transition hk).hom.hom (-2) :=
    h.choose_spec.choose_spec
  let r := hs.2.choose
  exact ⟨k, hs.1, r, hs.2.choose_spec.1, hs.2.choose_spec.2,
    postnikovRefinedCoefficientInverse_common R f c hs.1 r hs.2.choose_spec.2⟩

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
