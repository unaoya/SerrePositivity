module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoRoofCommonCoefficients
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraHomologyInverseAfter
public import SerrePositivity.KST.LocalizingInvariants.ModuleCoefficientInverse

/-!
概要：元の π₂ の pro 逆を、選んだ roof の共通 kernel 係数へ移す。
方針：roof の段以降の実線形逆を選び、指定した元の係数同型で両三角形を運ぶ。
規約：双加群射・実代数射への持ち上げは未主張。使われ方：class の逆の貼合せ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {i m : ℕ} {hi : i ≤ m} (c : NonpositiveInverseRoof R (f.map (postnikovFunctor R 1)) i m hi)

def postnikovTwoRoofCoefficientInverseMap (k : ℕ)
    (r : (B.obj k).obj.X.homology (-2) ⟶ (A.obj i).obj.X.homology (-2)) :
    (B.obj k).obj.X.homology (-2) ⟶
      (kernel (postnikovExtensionBaseChangeBase R (A.obj i).obj 1
        c.roof.numerator).hom).homology (-2) :=
  r ≫ (postnikovBaseChangedKernelHomologyIso R (A.obj i).obj 1 c.roof.numerator).inv

lemma postnikovTwoRoofCoefficientInverseMap_left {k : ℕ} (hm : m ≤ k)
    (r : (B.obj k).obj.X.homology (-2) ⟶ (A.obj i).obj.X.homology (-2))
    (hl : homologyMap (f.app k).hom.hom (-2) ≫ r =
      homologyMap (A.transition (hi.trans hm)).hom.hom (-2)) :
    homologyMap (f.app k).hom.hom (-2) ≫ postnikovTwoRoofCoefficientInverseMap R f c k r =
      homologyMap (A.transition (hi.trans hm)).hom.hom (-2) ≫
        (postnikovBaseChangedKernelHomologyIso R (A.obj i).obj 1 c.roof.numerator).inv :=
  (Category.assoc _ _ _).symm.trans
    (congrArg (fun t => t ≫
      (postnikovBaseChangedKernelHomologyIso R (A.obj i).obj 1 c.roof.numerator).inv) hl)

lemma postnikovTwoRoofCoefficientInverseMap_common {k : ℕ} (hm : m ≤ k)
    (r : (B.obj k).obj.X.homology (-2) ⟶ (A.obj i).obj.X.homology (-2))
    (hr : r ≫ homologyMap (f.app i).hom.hom (-2) =
      homologyMap (B.transition (hi.trans hm)).hom.hom (-2)) :
    postnikovTwoRoofCoefficientInverseMap R f c k r ≫
      homologyMap (postnikovTwoRoofNumeratorCommonKernel R f c) (-2) =
    (homologyMap (B.transition hm).hom.hom (-2) ≫
      (postnikovTwoRoofDenominatorKernelHomologyIso R f c).inv) ≫
        homologyMap (postnikovTwoRoofDenominatorCommonKernel R f c) (-2) := by
  let eA := postnikovBaseChangedKernelHomologyIso R (A.obj i).obj 1 c.roof.numerator
  let eB := postnikovTwoRoofDenominatorKernelHomologyIso R f c
  let eC := postnikovTwoRoofCommonKernelHomologyIso R f c
  have hc : (B.transition hm).hom.hom ≫ (B.transition hi).hom.hom =
      (B.transition (hi.trans hm)).hom.hom :=
    congrArg (fun t => t.hom.hom) (B.transition_comp hm hi)
  have ht : homologyMap (B.transition hm).hom.hom (-2) ≫
      homologyMap (B.transition hi).hom.hom (-2) =
        homologyMap (B.transition (hi.trans hm)).hom.hom (-2) :=
    (homologyMap_comp (B.transition hm).hom.hom (B.transition hi).hom.hom (-2)).symm.trans
      (congrArg (fun t => homologyMap t (-2)) hc)
  exact moduleCoefficientInverse_triangle eA eB eC
    (homologyMap (f.app i).hom.hom (-2)) (homologyMap (B.transition hi).hom.hom (-2))
    (homologyMap (postnikovTwoRoofNumeratorCommonKernel R f c) (-2))
    (homologyMap (postnikovTwoRoofDenominatorCommonKernel R f c) (-2))
    (postnikovTwoRoofNumeratorCommonKernel_original R f c)
    (postnikovTwoRoofDenominatorCommonKernel_original R f c)
    r (homologyMap (B.transition hm).hom.hom (-2)) (hr.trans ht.symm)

lemma exists_postnikovTwoRoofCoefficientInverse
    (hf : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R 2))) :
    ∃ k, ∃ hm : m ≤ k,
      ∃ r : (B.obj k).obj.X.homology (-2) ⟶
        (kernel (postnikovExtensionBaseChangeBase R (A.obj i).obj 1
          c.roof.numerator).hom).homology (-2),
      homologyMap (f.app k).hom.hom (-2) ≫ r =
        homologyMap (A.transition (hi.trans hm)).hom.hom (-2) ≫
          (postnikovBaseChangedKernelHomologyIso R (A.obj i).obj 1 c.roof.numerator).inv ∧
      r ≫ homologyMap (postnikovTwoRoofNumeratorCommonKernel R f c) (-2) =
        (homologyMap (B.transition hm).hom.hom (-2) ≫
          (postnikovTwoRoofDenominatorKernelHomologyIso R f c).inv) ≫
            homologyMap (postnikovTwoRoofDenominatorCommonKernel R f c) (-2) := by
  let h := exists_nonpositiveHomologyInverse_after R f 2 hf i m
  let k := h.choose
  let hk : i ≤ k := h.choose_spec.choose
  have hs : m ≤ k ∧ ∃ r : (B.obj k).obj.X.homology (-2) ⟶ (A.obj i).obj.X.homology (-2),
      homologyMap (f.app k).hom.hom (-2) ≫ r = homologyMap (A.transition hk).hom.hom (-2) ∧
      r ≫ homologyMap (f.app i).hom.hom (-2) = homologyMap (B.transition hk).hom.hom (-2) :=
    h.choose_spec.choose_spec
  let r := hs.2.choose
  exact ⟨k, hs.1, postnikovTwoRoofCoefficientInverseMap R f c k r,
    postnikovTwoRoofCoefficientInverseMap_left R f c hs.1 r hs.2.choose_spec.1,
    postnikovTwoRoofCoefficientInverseMap_common R f c hs.1 r hs.2.choose_spec.2⟩

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
