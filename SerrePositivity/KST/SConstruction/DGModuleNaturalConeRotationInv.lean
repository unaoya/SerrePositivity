module
public import SerrePositivity.KST.SConstruction.DGModuleNaturalConeDesc
public import SerrePositivity.KST.SConstruction.DGModuleNaturalConeConnecting
public import SerrePositivity.DifferentialGraded.Module.ConeRotation

/-!
概要：元厳密比較族の二重 cone から元第一関手の shift への実回転逆比較を全次数で束ねる。
方針：元右包含と connecting の零合成を、指定零元の cone descent へ渡す。
規約：元 connecting と同じ全 Hom 作用を保持する。
使われ方：実 connecting cone 比較を構成する回転逆の全関手族。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory HomologicalComplex CochainComplex HomComplex
open DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {P : Type w} [DGCategory R P]
  (F G : DGFunctor R P (RightModule R D)) (η : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F G)
local notation "a" => dgModuleNaturalConeArrow R D F G η
local notation "T" => dgModuleNaturalConeFunctor R D F G η
local notation "ν" => dgModuleNaturalConeInr R D F G η
local notation "δ" => dgModuleNaturalConeConnecting R D F G η
local notation "U" => dgModuleNaturalConeFunctor R D G (T) (ν)

/-- 概要：元右包含族の実閉射は同じ元 cone の標準包含。
方針：閉射・閉元対応の逆律を用いる。
規約：元包含の厳密等号。使われ方：回転逆の境界回収。 -/
lemma dgModuleNaturalConeInr_arrow (x : P) :
    dgModuleNaturalConeArrow R D G (T) (ν) x = moduleConeInr R D (a x) := by
  change (closedHomEquiv R (RightModule R D) _ _).symm
    ((closedHomEquiv R (RightModule R D) _ _) (moduleConeInr R D (a x))) = _
  exact (closedHomEquiv R (RightModule R D) _ _).symm_apply_apply _

/-- 概要：同じ右包含・connecting の合成は指定零元で零化される。
方針：元 cone の同じ零合成を使用する。
規約：元二辺を保持。使われ方：実回転逆の cone descent 境界。 -/
lemma dgModuleNaturalConeRotationInv_boundary (x : P) :
    (moduleHom R D (G.obj x) ((F.comp (moduleShiftDG R D 1)).obj x)).d (-1) 0 0 =
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R)
        (dgModuleNaturalConeArrow R D G (T) (ν) x ≫
          dgModuleNaturalConeArrow R D (T) (F.comp (moduleShiftDG R D 1)) (δ) x))).val := by
  have hi := dgModuleNaturalConeInr_arrow R D F G η x
  have hc := dgModuleNaturalConeConnecting_arrow R D F G η x
  have hz : dgModuleNaturalConeArrow R D G (T) (ν) x ≫
      dgModuleNaturalConeArrow R D (T) (F.comp (moduleShiftDG R D 1)) (δ) x = 0 :=
    (congrArg₂ (fun (r : ForgetEnrichment.of (Complex R) (G.obj x) ⟶ moduleCone R D (a x))
        (t : moduleCone R D (a x) ⟶ moduleShiftObj R D 1
          (ForgetEnrichment.of (Complex R) (F.obj x))) => r ≫ t) hi hc).trans
      (moduleConeInr_connecting_zero R D (a x))
  rw [map_zero]
  exact ((congrArg (fun t =>
    (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R) t)).val) hz).trans
      (moduleHomCycle_zero R D _ _)).symm


/-- 概要：同じ二重実 cone から元第一関手の shift への全厳密回転逆比較。
方針：全自然な connecting と指定零ホモトピーの cone descent を用いる。
規約：閉零次数だけの自然性ではない。使われ方：逆回転後合成全比較の第二因子。 -/
def dgModuleNaturalConeRotationInv : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans (U) (F.comp (moduleShiftDG R D 1)) :=
  dgModuleNaturalConeDesc R D G (T) (F.comp (moduleShiftDG R D 1)) (ν) (δ)
    (fun _ => 0) (dgModuleNaturalConeRotationInv_boundary R D F G η)
    (by
      intro x y n z
      simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_zero, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.zero_compose, smul_zero])
end SerrePositivity.KST.SConstruction
