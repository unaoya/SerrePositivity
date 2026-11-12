module
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.RelativeJoinBaseProjection
public import Mathlib.AlgebraicTopology.SimplicialSet.FiniteProd
public import Mathlib.AlgebraicTopology.SimplicialSet.FiniteColimits

/-! # 有限写像円柱の始点包含

概要：任意の有限二対象間の射を、有限写像円柱への始点単射と射影に分ける。
方針：既存の区間付き pushout を使い、relative join への比較で始点単射性を検出する。
規約：元の射自体には単射性を要求しない。使われ方：有限対充填の一般有限図式への適用。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped _root_.Simplicial
variable {A B : SSet.{u}} (f : A ⟶ B)

/-- 区間の終端を元の射で貼った写像円柱。 -/
abbrev finiteMappingCylinder := pushout (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A) f

/-- 写像円柱の始点の指定包含。 -/
def finiteMappingCylinderSource : A ⟶ finiteMappingCylinder f :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ≫ pushout.inl _ _

/-- 元の射が単射でなくても、写像円柱の始点包含は単射。 -/
instance finiteMappingCylinderSource_mono : Mono (finiteMappingCylinderSource f) := by
  have h : finiteMappingCylinderSource f ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinCylinderComparison f ≫ pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (𝟙 B)) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal B)) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A B := by
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ≫ pushout.inl _ _) ≫ _ = _
    rw [Category.assoc, ← Category.assoc (pushout.inl _ _),
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinCylinderComparison_inl, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrism_zero,
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInl_fst]
  exact mono_of_mono_fac h

/-- 有限二対象の写像円柱は有限。 -/
instance finiteMappingCylinder_finite [A.Finite] [B.Finite] :
    (finiteMappingCylinder f).Finite := by
  apply SSet.finite_of_isColimit (pushoutIsPushout (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A) f)
  rintro (_ | (_ | _)) <;>
    simp only [span_left, span_right, span_zero] <;> infer_instance

/-- 始点包含と元の終域包含による射は、写像円柱内の実ホモトピーで結ばれる。 -/
def finiteMappingCylinderHomotopy : SSet.Homotopy
    (finiteMappingCylinderSource f) (f ≫ pushout.inr (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A) f) where
  h := (β_ A (Δ[1] : SSet.{u})).hom ≫ pushout.inl _ _
  h₀ := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ≫ pushout.inl _ _ = _
    rfl
  h₁ := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A ≫ pushout.inl _ _ = _
    exact pushout.condition
  rel := by
    ext n s
    exact False.elim s.1.property

/-- 写像円柱の始点包含を係数射影で戻すと元の射になる。 -/
lemma finiteMappingCylinderSource_projection :
    finiteMappingCylinderSource f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.mappingCylinderBaseProjection f = f := by
  rw [finiteMappingCylinderSource, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.mappingCylinderBaseProjection_inl,
    ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.prismEndpoint_snd, Category.id_comp]

end SerrePositivity.InfinityCategories.Project.DerivedCategories
