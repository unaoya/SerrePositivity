module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalMappingSpace
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FatJoinComparisonNaturality

/-!
概要：区間とパラメータの直積から左右の点付き join への比較射。
方針：Core の join の円柱比較に、一方の因子として標準零単体の点を補う。
規約：区間を第一因子に置き、左右の join で同じ端点の向きを使う。
使われ方：Kerodon §4.6.5（Tag 01KW）–4.6.6（Tag 04HY）、pinched 模型から区間模型への比較。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：区間とパラメータの直積から右に点を付加した join への射。
方針：区間とパラメータを交換し、右に点を補って join の円柱比較を使う。
規約：時刻零はパラメータ、時刻一は付加した点に写る。
使われ方：Kerodon §4.6.5（Tag 01KW）–4.6.6（Tag 04HY）、右 pinched 模型の区間への展開。 -/
noncomputable def rightMappingSpacePrism (A : SSet.{u}) : Δ[1] ⊗ A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A (Δ[0] : SSet.{u}) :=
  (β_ Δ[1] A).hom ≫
    lift (𝟙 (A ⊗ Δ[1])) (SSet.const (stdSimplex.obj₀Equiv.symm 0)) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinCylinderMap A Δ[0]

/-- 概要：右の join への比較の零端点は左包含。
方針：円柱の零端点の式と直積の第一射影を使う。
規約：パラメータ A の単体をそのまま保つ。
使われ方：Kerodon §4.6.5（Tag 01KW）、右模型の始点の固定条件。 -/
lemma rightMappingSpacePrism_zero (A : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ≫ rightMappingSpacePrism A = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A Δ[0] := by
  have h : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ≫ (β_ Δ[1] A).hom ≫
      lift (𝟙 (A ⊗ Δ[1])) (SSet.const (stdSimplex.obj₀Equiv.symm 0)) =
      lift (𝟙 A) (SSet.const (stdSimplex.obj₀Equiv.symm 0)) ≫
        (SSet.ι₀ (X := A) ▷ (Δ[0] : SSet.{u})) := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro a
    rfl
  unfold rightMappingSpacePrism
  rw [← Category.assoc, ← Category.assoc, Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A), h,
    Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinCylinderMap_zero, ← Category.assoc, lift_fst, Category.id_comp]

/-- 概要：右の join への比較の一端点は右の点に定値。
方針：円柱の一端点の式と直積の第二射影を使う。
規約：標準零単体の唯一の頂点を右包含で写す。
使われ方：Kerodon §4.6.5（Tag 01KW）、右模型の終点の固定条件。 -/
lemma rightMappingSpacePrism_one (A : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A ≫ rightMappingSpacePrism A =
      SSet.const (stdSimplex.obj₀Equiv.symm 0) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A Δ[0] := by
  have h : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A ≫ (β_ Δ[1] A).hom ≫
      lift (𝟙 (A ⊗ Δ[1])) (SSet.const (stdSimplex.obj₀Equiv.symm 0)) =
      lift (𝟙 A) (SSet.const (stdSimplex.obj₀Equiv.symm 0)) ≫
        (SSet.ι₁ (X := A) ▷ (Δ[0] : SSet.{u})) := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro a
    rfl
  unfold rightMappingSpacePrism
  rw [← Category.assoc, ← Category.assoc, Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A), h,
    Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinCylinderMap_one, ← Category.assoc, lift_snd]

/-- 概要：区間とパラメータの直積から左に点を付加した join への射。
方針：区間の左に点を補い、パラメータを右因子として円柱比較を使う。
規約：時刻零は付加した点、時刻一はパラメータに写る。
使われ方：Kerodon §4.6.5（Tag 01KW）–4.6.6（Tag 04HY）、左 pinched 模型の区間への展開。 -/
noncomputable def leftMappingSpacePrism (A : SSet.{u}) : Δ[1] ⊗ A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) A :=
  lift (lift (SSet.const (stdSimplex.obj₀Equiv.symm 0)) (fst Δ[1] A))
    (snd Δ[1] A) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinCylinderMap Δ[0] A

/-- 概要：左の join への比較の零端点は左の点に定値。
方針：円柱の零端点の式と直積の第一射影を使う。
規約：標準零単体の唯一の頂点を左包含で写す。
使われ方：Kerodon §4.6.5（Tag 01KW）、左模型の始点の固定条件。 -/
lemma leftMappingSpacePrism_zero (A : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ≫ leftMappingSpacePrism A =
      SSet.const (stdSimplex.obj₀Equiv.symm 0) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl Δ[0] A := by
  have h : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ≫
      lift (lift (SSet.const (stdSimplex.obj₀Equiv.symm 0)) (fst Δ[1] A)) (snd Δ[1] A) =
      lift (SSet.const (stdSimplex.obj₀Equiv.symm 0)) (𝟙 A) ≫
        (SSet.ι₀ (X := (Δ[0] : SSet.{u})) ▷ A) := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro a
    rfl
  unfold leftMappingSpacePrism
  rw [← Category.assoc, h, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinCylinderMap_zero,
    ← Category.assoc, lift_fst]

/-- 概要：左の join への比較の一端点は右包含。
方針：円柱の一端点の式と直積の第二射影を使う。
規約：パラメータ A の単体をそのまま保つ。
使われ方：Kerodon §4.6.5（Tag 01KW）、左模型の終点の固定条件。 -/
lemma leftMappingSpacePrism_one (A : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A ≫ leftMappingSpacePrism A = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[0] A := by
  have h : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A ≫
      lift (lift (SSet.const (stdSimplex.obj₀Equiv.symm 0)) (fst Δ[1] A)) (snd Δ[1] A) =
      lift (SSet.const (stdSimplex.obj₀Equiv.symm 0)) (𝟙 A) ≫
        (SSet.ι₁ (X := (Δ[0] : SSet.{u})) ▷ A) := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro a
    rfl
  unfold leftMappingSpacePrism
  rw [← Category.assoc, h, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinCylinderMap_one,
    ← Category.assoc, lift_snd, Category.id_comp]

/-- 概要：右の join への円筒比較はパラメータに自然。
方針：円柱の入力成分を比較し、join の円柱比較の自然性を使う。
規約：右の付加した点は固定する。
使われ方：Kerodon §4.6.6（Tag 04HY）、右模型の族の制限との整合性。 -/
lemma rightMappingSpacePrism_naturality {A B : SSet.{u}} (f : A ⟶ B) :
    (Δ[1] ◁ f) ≫ rightMappingSpacePrism B =
      rightMappingSpacePrism A ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (𝟙 Δ[0]) := by
  have h : (Δ[1] ◁ f) ≫ (β_ Δ[1] B).hom ≫
      lift (𝟙 (B ⊗ Δ[1])) (SSet.const (stdSimplex.obj₀Equiv.symm 0)) =
      ((β_ Δ[1] A).hom ≫
        lift (𝟙 (A ⊗ Δ[1])) (SSet.const (stdSimplex.obj₀Equiv.symm 0))) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinderMap f (𝟙 Δ[0]) := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro a
    rfl
  unfold rightMappingSpacePrism
  rw [← Category.assoc, ← Category.assoc, Category.assoc (Δ[1] ◁ f), h,
    Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinCylinderMap_naturality]
  simp only [Category.assoc]

/-- 概要：左の join への円筒比較はパラメータに自然。
方針：区間と点を保った入力を比較し、join の円柱比較の自然性を使う。
規約：左の付加した点は固定する。
使われ方：Kerodon §4.6.6（Tag 04HY）、左模型の族の制限との整合性。 -/
lemma leftMappingSpacePrism_naturality {A B : SSet.{u}} (f : A ⟶ B) :
    (Δ[1] ◁ f) ≫ leftMappingSpacePrism B =
      leftMappingSpacePrism A ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 Δ[0]) f := by
  have h : (Δ[1] ◁ f) ≫
      lift (lift (SSet.const (stdSimplex.obj₀Equiv.symm 0)) (fst Δ[1] B)) (snd Δ[1] B) =
      lift (lift (SSet.const (stdSimplex.obj₀Equiv.symm 0)) (fst Δ[1] A)) (snd Δ[1] A) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinderMap (𝟙 Δ[0]) f := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro a
    rfl
  unfold leftMappingSpacePrism
  rw [← Category.assoc, h, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinCylinderMap_naturality, ← Category.assoc]

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
