module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPathIdentityPullback
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraHomotopyPullbackMiddleMap

/-!
概要：経路の両端と底の全経路を同時に保持する実境界比較射。
方針：恒等 cospan の経路同型と中央だけを変える cospan 比較を合成する。
規約：p の次数全射性・準同型性を別々に反映。使われ方：指定底経路の厳密持ち上げ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.Path
variable (R : Type u) [CommRing R] {C B : Mon (Complex R)} (p : C ⟶ B)

def boundaryMap : algebra R C ⟶ HomotopyPullbackModel.algebra R p p :=
  (identityPullbackIso R C).hom ≫ HomotopyPullbackModel.middleMap R p

lemma boundaryMap_source : boundaryMap R p ≫ HomotopyPullbackModel.left R p p = source R C := by
  rw [boundaryMap, Category.assoc, HomotopyPullbackModel.middleMap_left]
  exact toIdentityPullback_left R C

lemma boundaryMap_target : boundaryMap R p ≫ HomotopyPullbackModel.right R p p = target R C := by
  rw [boundaryMap, Category.assoc, HomotopyPullbackModel.middleMap_right]
  exact toIdentityPullback_right R C

lemma boundaryMap_path : boundaryMap R p ≫ HomotopyPullbackModel.path R p p = map R p := by
  rw [boundaryMap, Category.assoc, HomotopyPullbackModel.middleMap_path, ← Category.assoc]
  change (toIdentityPullback R C ≫ HomotopyPullbackModel.path R (𝟙 C) (𝟙 C)) ≫ _ = _
  rw [toIdentityPullback_path, Category.id_comp]

lemma boundaryMap_surjective (hs : ∀ n : ℤ, Function.Surjective (p.hom.f n)) (n : ℤ) :
    Function.Surjective ((boundaryMap R p).hom.f n) := by
  have hi : Function.Surjective (((identityPullbackIso R C).hom.hom).f n) :=
    (ModuleCat.epi_iff_surjective _).1 inferInstance
  exact (HomotopyPullbackModel.middleMap_surjective R p hs n).comp hi

lemma boundaryMap_quasiIso (hq : QuasiIso p.hom) : QuasiIso (boundaryMap R p).hom :=
  quasiIso_comp _ _ (hφ := quasiIso_of_isIso ((identityPullbackIso R C).hom.hom))
    (hφ' := HomotopyPullbackModel.middleMap_quasiIso R p hq)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.Path
