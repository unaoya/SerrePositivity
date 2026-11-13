module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor.DGHomTensorRestrictions
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.HomSpaces.DGSemifreeDerivedHomInfinity
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded Opposite
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
/-- 半自由加群の同じ二入力 Hom を R 加群値にする実 dg 関手。 -/
def dgSemifreeHomTensorModuleDG :
    DGFunctor R (DGTensorCategory R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D)ᵒᵖ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D))
      (_root_.SerrePositivity.DifferentialGraded.RightModule R PUnit.{1}) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTensorFunctor R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D)).comp (ringConstantDG R)
/-- 固定終域への実 dg 制限は、元の同じ反変 Hom と厳密に一致。 -/
lemma dgSemifreeHomTensorModuleDG_first (Q : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) :
    (dgTensorIncludeFirst R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D)ᵒᵖ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) Q).comp
      (dgSemifreeHomTensorModuleDG R D) = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeHomSourceModuleDG R D Q := by
  apply EnrichedFunctor.ext (_root_.SerrePositivity.DifferentialGraded.Complex R)
    (F := (dgTensorIncludeFirst R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D)ᵒᵖ
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) Q).comp (dgSemifreeHomTensorModuleDG R D))
    (G := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeHomSourceModuleDG R D Q) (fun _ => rfl)
  intro X Y
  change (dgTensorFirstHom R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D)ᵒᵖ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) Q X Y ≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTensorMap R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) (X, Q) (Y, Q) ≫ _) ≫ 𝟙 _ = _
  rw [Category.comp_id, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTensorMap_first]
  rfl
/-- 固定始域への実 dg 制限は、元の同じ共変 Hom と厳密に一致。 -/
lemma dgSemifreeHomTensorModuleDG_second (P : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) :
    (dgTensorIncludeSecond R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D)ᵒᵖ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) (_root_.Opposite.op P)).comp
      (dgSemifreeHomTensorModuleDG R D) = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeHomTargetModuleDG R D P := by
  apply EnrichedFunctor.ext (_root_.SerrePositivity.DifferentialGraded.Complex R)
    (F := (dgTensorIncludeSecond R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D)ᵒᵖ
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) (_root_.Opposite.op P)).comp (dgSemifreeHomTensorModuleDG R D))
    (G := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeHomTargetModuleDG R D P) (fun _ => rfl)
  intro X Y
  change (dgTensorSecondHom R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D)ᵒᵖ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) (_root_.Opposite.op P) X Y ≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTensorMap R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) (_root_.Opposite.op P, X) (_root_.Opposite.op P, Y) ≫ _) ≫ 𝟙 _ = _
  rw [Category.comp_id, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTensorMap_second]
  rfl
/-- 同じ tensor dg 圏の nerve から、実 D(R) 値への出力分解 ∞ 関手。 -/
def dgSemifreeDerivedHomTensorInfinity :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (DGTensorCategory R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D)ᵒᵖ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D)) ⟶
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomDerivedNerve R D :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, max (u + 1) v, u + 1} R
    (DGTensorCategory R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D)ᵒᵖ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D))) ≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolutionInfinity R
      (DGTensorCategory R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D)ᵒᵖ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D))
      PUnit.{1} (dgSemifreeHomTensorModuleDG R D)
end SerrePositivity.InfinityCategories.Project.DerivedCategories
