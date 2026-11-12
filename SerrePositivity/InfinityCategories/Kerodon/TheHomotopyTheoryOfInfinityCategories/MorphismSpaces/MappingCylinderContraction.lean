module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Diagrams.CylinderMaximumAction
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.RelativeJoinBaseProjection
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks

/-!
概要：写像円柱の全体から右端への自然な変形。
方針：円柱の最大値による変形と固定された右端を、直積で移した pushout で貼る。
規約：右端は変形中も厳密に固定される。
使われ方：相対 join の右端への制限の Hom 対応を得る準備。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：写像円柱の円柱部分を右端へ送り、右端を固定する変形の射。
方針：直積が保存する pushout で円柱部分の最大値作用と右端の定値族を貼る。
規約：変形の時刻は最後の因子。
使われ方：写像円柱の右端を右随伴として表す単位の構成。 -/
def mappingCylinderContraction {K C : SSet.{u}} (p : K ⟶ C) :
    pushout (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K) p ⊗ (Δ[1] : SSet.{u}) ⟶ pushout (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K) p :=
  ((IsPushout.of_hasPushout (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K) p).map (tensorRight (Δ[1] : SSet.{u}))).desc
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Diagrams.cylinderMaximumAction K ≫ pushout.inl (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K) p)
    (fst C (Δ[1] : SSet.{u}) ≫ pushout.inr (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K) p) (by
      change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K ▷ (Δ[1] : SSet.{u})) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Diagrams.cylinderMaximumAction K ≫ pushout.inl (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K) p) =
          (p ▷ (Δ[1] : SSet.{u})) ≫ (fst C Δ[1] ≫ pushout.inr (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K) p)
      rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Diagrams.cylinderMaximumAction_fixed_one, Category.assoc, pushout.condition]
      simpa only [Category.assoc] using congrArg
        (fun z ↦ z ≫ pushout.inr (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K) p) (whiskerRight_fst p Δ[1]).symm)

/-- 概要：変形の円柱部分への制限は最大値による変形。
方針：直積した pushout の第一包含への制限を使う。
規約：右端との貼り合わせ後も元の円柱部分を厳密に保つ。
使われ方：変形の両端点の計算。 -/
lemma mappingCylinderContraction_inl {K C : SSet.{u}} (p : K ⟶ C) :
    (pushout.inl (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K) p ▷ (Δ[1] : SSet.{u})) ≫
      mappingCylinderContraction p =
        _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Diagrams.cylinderMaximumAction K ≫ pushout.inl (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K) p :=
  ((IsPushout.of_hasPushout (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K) p).map
    (tensorRight (Δ[1] : SSet.{u}))).inl_desc _ _ _

/-- 概要：変形の右端への制限は右端の恒等族。
方針：直積した pushout の第二包含への制限を使う。
規約：変形の時刻によらず右端は固定する。
使われ方：単位を右端へ制限した三角恒等式。 -/
lemma mappingCylinderContraction_inr {K C : SSet.{u}} (p : K ⟶ C) :
    (pushout.inr (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K) p ▷ (Δ[1] : SSet.{u})) ≫
      mappingCylinderContraction p = fst C (Δ[1] : SSet.{u}) ≫
        pushout.inr (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K) p :=
  ((IsPushout.of_hasPushout (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K) p).map
    (tensorRight (Δ[1] : SSet.{u}))).inr_desc _ _ _

/-- 概要：写像円柱の変形の始点は恒等射。
方針：pushout の両部分で変形の零端点を計算する。
規約：円柱全体の厳密な恒等射。
使われ方：右端への変形を単位のホモトピーとする。 -/
lemma mappingCylinderContraction_zero {K C : SSet.{u}} (p : K ⟶ C) :
    SSet.ι₀ ≫ mappingCylinderContraction p = 𝟙 _ := by
  apply pushout.hom_ext
  · rw [← SSet.ι₀_comp_assoc, mappingCylinderContraction_inl, ← Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Diagrams.cylinderMaximumAction_zero, Category.id_comp, Category.comp_id]
  · rw [← SSet.ι₀_comp_assoc, mappingCylinderContraction_inr, ← Category.assoc]
    simp

/-- 概要：写像円柱の変形の終点は底への射影と右包含の合成。
方針：円柱部分は一端点へ畳み、右端では恒等射となることを確認する。
規約：係数の底への射影を用いる。
使われ方：右端への制限の大域的 Hom 対応。 -/
lemma mappingCylinderContraction_one {K C : SSet.{u}} (p : K ⟶ C) :
    SSet.ι₁ ≫ mappingCylinderContraction p =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.mappingCylinderBaseProjection p ≫ pushout.inr (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K) p := by
  apply pushout.hom_ext
  · rw [← SSet.ι₁_comp_assoc, mappingCylinderContraction_inl, ← Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Diagrams.cylinderMaximumAction_one, Category.assoc, pushout.condition]
    rw [reassoc_of% (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.mappingCylinderBaseProjection_inl p)]
  · rw [← SSet.ι₁_comp_assoc, mappingCylinderContraction_inr, ← Category.assoc,
      ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.mappingCylinderBaseProjection_inr, Category.id_comp]
    simp

/-- 概要：写像円柱の変形は係数の底への射影を固定する。
方針：直積した pushout の両部分で係数を忘れないことを確認する。
規約：変形の時刻には依存しない等式。
使われ方：右端の包含と底への射影の単位の三角恒等式。 -/
lemma mappingCylinderContraction_baseProjection {K C : SSet.{u}} (p : K ⟶ C) :
    mappingCylinderContraction p ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.mappingCylinderBaseProjection p =
      fst (pushout (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K) p) (Δ[1] : SSet.{u}) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.mappingCylinderBaseProjection p := by
  apply ((IsPushout.of_hasPushout (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K) p).map
    (tensorRight (Δ[1] : SSet.{u}))).hom_ext
  · change (pushout.inl (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K) p ▷ (Δ[1] : SSet.{u})) ≫
        (mappingCylinderContraction p ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.mappingCylinderBaseProjection p) =
      (pushout.inl (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K) p ▷ (Δ[1] : SSet.{u})) ≫
        (fst (pushout (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K) p) Δ[1] ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.mappingCylinderBaseProjection p)
    rw [reassoc_of% (mappingCylinderContraction_inl p),
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.mappingCylinderBaseProjection_inl]
    rw [reassoc_of% (whiskerRight_fst (pushout.inl (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K) p) Δ[1]),
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.mappingCylinderBaseProjection_inl]
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Diagrams.cylinderMaximumAction_snd, Category.assoc]
  · change (pushout.inr (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K) p ▷ (Δ[1] : SSet.{u})) ≫
        (mappingCylinderContraction p ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.mappingCylinderBaseProjection p) =
      (pushout.inr (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K) p ▷ (Δ[1] : SSet.{u})) ≫
        (fst (pushout (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K) p) Δ[1] ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.mappingCylinderBaseProjection p)
    rw [reassoc_of% (mappingCylinderContraction_inr p),
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.mappingCylinderBaseProjection_inr, Category.comp_id]
    rw [reassoc_of% (whiskerRight_fst (pushout.inr (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K) p) Δ[1]),
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.mappingCylinderBaseProjection_inr, Category.comp_id]

/-- 概要：写像円柱の恒等射から右端への射影の合成への自然なホモトピー。
方針：貼り合わせた変形の射に両端点の計算を添える。
規約：quasicategory 性を要求しない。
使われ方：相対 join の右端への Hom 対応の単位の代表。 -/
def mappingCylinderUnit {K C : SSet.{u}} (p : K ⟶ C) :
    SSet.Homotopy (𝟙 (pushout (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K) p))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.mappingCylinderBaseProjection p ≫ pushout.inr (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K) p) where
  h := mappingCylinderContraction p
  h₀ := mappingCylinderContraction_zero p
  h₁ := mappingCylinderContraction_one p
  rel := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro s
    exact False.elim s.1.property

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
