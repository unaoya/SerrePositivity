module
public import SerrePositivity.KST.SConstruction.DGModuleShiftCancellationStrict

/-!
概要：全厳密 shift 相殺の成分を元実相殺同型へ回収する。
方針：元閉射族からの比較と厳密合成の回収を使う。
規約：同じ加法・零 shift 同型を保持する。
使われ方：実逆回転全比較の相殺成分の照合。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
private lemma familyArrow {P : Type (max (u + 1) v)} [DGCategory R P]
    (F G : DGFunctor R P (RightModule R D))
    (a : ∀ x, ForgetEnrichment.of (Complex R) (F.obj x) ⟶
      ForgetEnrichment.of (Complex R) (G.obj x))
    (h : ∀ x y, F.map x y ≫
      eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) (F.obj x)) (a y) =
      G.map x y ≫ eHomWhiskerRight (Complex R) (a x)
        (ForgetEnrichment.of (Complex R) (G.obj y))) (x : P) :
    dgModuleNaturalConeArrow R D F G (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleStrictNatTransOfHomNaturality R D a h) x =
      a x := by
  change (closedHomEquiv R (RightModule R D) _ _).symm
    ((closedHomEquiv R (RightModule R D) _ _) (a x)) = _
  exact (closedHomEquiv R (RightModule R D) _ _).symm_apply_apply _

/-- 概要：元零 shift 全比較の閉射回収。方針：閉射族対応の逆律。
規約：元零 shift 同型。使われ方：指定相殺の終辺回収。 -/
lemma dgModuleShiftZeroStrictComparison_arrow (M : RightModule R D) :
    dgModuleNaturalConeArrow R D (moduleShiftDG R D 0)
      (DGFunctor.id (RightModule R D)) (dgModuleShiftZeroStrictComparison R D) M =
      (moduleShiftZeroIsoObj R D M).hom :=
  familyArrow R D (moduleShiftDG R D 0) (DGFunctor.id (RightModule R D))
    (fun N => (moduleShiftZeroIsoObj R D N).hom) (dgModuleShiftZeroHomNaturality R D) M

/-- 概要：元加法 shift 逆全比較の閉射回収。方針：閉射族対応の逆律。
規約：元加法 shift 同型。使われ方：指定相殺の始辺回収。 -/
lemma dgModuleShiftAddInvStrictComparison_arrow (s t : ℤ) (M : RightModule R D) :
    dgModuleNaturalConeArrow R D
      ((moduleShiftDG R D s).comp (moduleShiftDG R D t))
      (moduleShiftDG R D (s + t)) (dgModuleShiftAddInvStrictComparison R D s t) M =
      (moduleShiftAddIsoObj R D s t M).inv :=
  familyArrow R D ((moduleShiftDG R D s).comp (moduleShiftDG R D t))
    (moduleShiftDG R D (s + t)) (fun N => (moduleShiftAddIsoObj R D s t N).inv)
    (dgFunctorClosedComparison_inv_naturality R (moduleShiftDG R D (s + t))
      ((moduleShiftDG R D s).comp (moduleShiftDG R D t))
      (moduleShiftAddIsoObj R D s t) (dgModuleShiftAddHomNaturality R D s t)) M

end SerrePositivity.KST.SConstruction
