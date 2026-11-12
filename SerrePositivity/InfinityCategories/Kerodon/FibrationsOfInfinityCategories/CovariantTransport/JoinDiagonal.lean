module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FatJoinComparisonNaturality
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.HomotopyBoundaryExtension
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：単体集合の区間付き対角から二つの同じ因子の join への射。
方針：左右に同じ係数を持つ円柱を作り、既存の円柱から join への射へ合成する。
規約：区間は左因子、係数の単体集合は右因子とする。
使われ方：Kerodon Construction 5.2.3.1（Tag 0242）、relative join の引き戻しによる構成。

対応節は Kerodon 5.2（Tag 019A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport

/-- 概要：区間付き係数を左右に同じ係数を持つ join の円柱へ写す。
方針：区間と係数を入れ替えた成分と、元の係数の成分を対にする。
規約：円柱の因子の順序は (K×Δ[1])×K。
使われ方：Kerodon Construction 5.2.3.1（Tag 0242）、relative join の対角の準備。 -/
noncomputable def joinDiagonalCylinder (K : SSet.{u}) :
    (Δ[1] : SSet.{u}) ⊗ K ⟶ (K ⊗ (Δ[1] : SSet.{u})) ⊗ K :=
  lift (β_ (Δ[1] : SSet.{u}) K).hom (snd (Δ[1] : SSet.{u}) K)

/-- 概要：単体集合 K の区間付き対角を join K K へ写す。
方針：両側の係数が同じ円柱を、通常の join の円柱比較へ写す。
規約：端点零は左包含、端点一は右包含になる。
使われ方：Kerodon Construction 5.2.3.1（Tag 0242）、relative join の基底の対角射。 -/
@[kerodon 0242]
noncomputable def joinDiagonal (K : SSet.{u}) : (Δ[1] : SSet.{u}) ⊗ K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K K :=
  joinDiagonalCylinder K ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinCylinderMap K K

/-- 概要：join の区間付き対角の零端は左の包含。
方針：対角の円柱の零端を計算して円柱比較の零端の公式を使う。
規約：係数は端点で変わらない。
使われ方：Kerodon Construction 5.2.3.1（Tag 0242）、relative join の左因子の包含。 -/
lemma prismEndpoint_zero_joinDiagonal (K : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K ≫ joinDiagonal K = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K K := by
  have h : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K ≫ joinDiagonalCylinder K =
      lift (𝟙 K) (𝟙 K) ≫ (SSet.ι₀ (X := K) ▷ K) := rfl
  rw [joinDiagonal, ← Category.assoc, h, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinCylinderMap_zero,
    ← Category.assoc, lift_fst, Category.id_comp]

/-- 概要：join の区間付き対角の一端は右の包含。
方針：対角の円柱の一端を計算して円柱比較の一端の公式を使う。
規約：係数は端点で変わらない。
使われ方：Kerodon Construction 5.2.3.1（Tag 0242）、relative join の右因子の包含。 -/
lemma prismEndpoint_one_joinDiagonal (K : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K ≫ joinDiagonal K = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr K K := by
  have h : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K ≫ joinDiagonalCylinder K =
      lift (𝟙 K) (𝟙 K) ≫ (SSet.ι₁ (X := K) ▷ K) := rfl
  rw [joinDiagonal, ← Category.assoc, h, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinCylinderMap_one,
    ← Category.assoc, lift_snd, Category.id_comp]

/-- 概要：区間付き対角は係数の単体集合に自然。
方針：両側の係数を同じ射で写す円柱の自然性を使う。
規約：区間は恒等射で保つ。
使われ方：Kerodon Construction 5.2.3.1（Tag 0242）、射 X→Y の relative join の比較。 -/
lemma joinDiagonal_naturality {X Y : SSet.{u}} (f : X ⟶ Y) :
    ((Δ[1] : SSet.{u}) ◁ f) ≫ joinDiagonal Y = joinDiagonal X ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f f := by
  have h : ((Δ[1] : SSet.{u}) ◁ f) ≫ joinDiagonalCylinder Y =
      joinDiagonalCylinder X ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinderMap f f := rfl
  rw [joinDiagonal, ← Category.assoc, h, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinCylinderMap_naturality,
    ← Category.assoc]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport
