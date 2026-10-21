module
public import SerrePositivity.InfinityCategories.Derived.DGHomTensorRestrictions
public import SerrePositivity.InfinityCategories.Derived.DGSemifreeDerivedHomInfinity
/-!
概要：半自由加群の同じ二入力 Hom を、実出力分解で D(R) 値の全 ∞ 関手へ移す。
方針：Small 性なしの Hom dg 関手を R 加群へ送り、同じ実分解の指定逆を合成する。
規約：始域は tensor dg 圏の nerve。元の二つの nerve の直積との比較は別工程。
使われ方：二変数導来 Hom の固定入力比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve Opposite
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
/-- 半自由加群の同じ二入力 Hom を R 加群値にする実 dg 関手。 -/
def dgSemifreeHomTensorModuleDG :
    DGFunctor R (DGTensorCategory R (SemifreeDGModules R D)ᵒᵖ (SemifreeDGModules R D))
      (RightModule R PUnit.{1}) :=
  (dgHomTensorFunctor R (SemifreeDGModules R D)).comp (ringConstantDG R)
/-- 固定終域への実 dg 制限は、元の同じ反変 Hom と厳密に一致。 -/
lemma dgSemifreeHomTensorModuleDG_first (Q : SemifreeDGModules R D) :
    (dgTensorIncludeFirst R (SemifreeDGModules R D)ᵒᵖ (SemifreeDGModules R D) Q).comp
      (dgSemifreeHomTensorModuleDG R D) = dgSemifreeHomSourceModuleDG R D Q := by
  apply EnrichedFunctor.ext (Complex R)
    (F := (dgTensorIncludeFirst R (SemifreeDGModules R D)ᵒᵖ
      (SemifreeDGModules R D) Q).comp (dgSemifreeHomTensorModuleDG R D))
    (G := dgSemifreeHomSourceModuleDG R D Q) (fun _ => rfl)
  intro X Y
  change (dgTensorFirstHom R (SemifreeDGModules R D)ᵒᵖ (SemifreeDGModules R D) Q X Y ≫
    dgHomTensorMap R (SemifreeDGModules R D) (X, Q) (Y, Q) ≫ _) ≫ 𝟙 _ = _
  rw [Category.comp_id, ← Category.assoc, dgHomTensorMap_first]
  rfl
/-- 固定始域への実 dg 制限は、元の同じ共変 Hom と厳密に一致。 -/
lemma dgSemifreeHomTensorModuleDG_second (P : SemifreeDGModules R D) :
    (dgTensorIncludeSecond R (SemifreeDGModules R D)ᵒᵖ (SemifreeDGModules R D) (op P)).comp
      (dgSemifreeHomTensorModuleDG R D) = dgSemifreeHomTargetModuleDG R D P := by
  apply EnrichedFunctor.ext (Complex R)
    (F := (dgTensorIncludeSecond R (SemifreeDGModules R D)ᵒᵖ
      (SemifreeDGModules R D) (op P)).comp (dgSemifreeHomTensorModuleDG R D))
    (G := dgSemifreeHomTargetModuleDG R D P) (fun _ => rfl)
  intro X Y
  change (dgTensorSecondHom R (SemifreeDGModules R D)ᵒᵖ (SemifreeDGModules R D) (op P) X Y ≫
    dgHomTensorMap R (SemifreeDGModules R D) (op P, X) (op P, Y) ≫ _) ≫ 𝟙 _ = _
  rw [Category.comp_id, ← Category.assoc, dgHomTensorMap_second]
  rfl
/-- 同じ tensor dg 圏の nerve から、実 D(R) 値への出力分解 ∞ 関手。 -/
def dgSemifreeDerivedHomTensorInfinity :
    dgNerve R (DGTensorCategory R (SemifreeDGModules R D)ᵒᵖ (SemifreeDGModules R D)) ⟶
      dgHomDerivedNerve R D :=
  dgNerve.map (dgUniverseLiftUp.{u, max (u + 1) v, u + 1} R
    (DGTensorCategory R (SemifreeDGModules R D)ᵒᵖ (SemifreeDGModules R D))) ≫
    dgModuleOutputResolutionInfinity R
      (DGTensorCategory R (SemifreeDGModules R D)ᵒᵖ (SemifreeDGModules R D))
      PUnit.{1} (dgSemifreeHomTensorModuleDG R D)
end SerrePositivity.InfinityCategories
