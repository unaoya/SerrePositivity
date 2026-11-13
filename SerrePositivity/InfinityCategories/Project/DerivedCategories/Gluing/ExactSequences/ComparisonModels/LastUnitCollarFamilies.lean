module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.ComparisonModels.FirstUnitCollarFamilies
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.ComparisonModels.LastUnitCollarGeometry

/-! # 全パラメーター付き終側単位補正

概要：終側の単位貼り合わせを持つ三角形 prism を、元終辺固定の三角形族へ戻す。
方針：共通の時間再添字を使い、終側補正の有限単調写像を全入力へ適用する。
規約：固定終辺・始辺・元端を全パラメーターで保持する。
使われ方：実後正規化の共有三角形を、元終辺の合成対応へ持ち上げる。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped _root_.Simplicial
lemma dgGluingLastUnitCollarFamily_last {Z K : SSet.{u}}
    (T : (Δ[1] : SSet.{u}) ⊗ (Δ[2] ⊗ K) ⟶ Z) (e : (Δ[1] : SSet.{u}) ⟶ Z)
    (hs : (Δ[1] ◁ (stdSimplex.δ (0 : Fin 3) ▷ K)) ≫ T =
      (Δ[1] ◁ fst (Δ[1] : SSet.{u}) K) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingSquareUnitCollapse 1 ≫ e) :
    (stdSimplex.δ (0 : Fin 3) ▷ (K ⊗ Δ[1])) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleTimeReindex _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLastUnitCollar ≫ T) =
      fst (Δ[1] : SSet.{u}) (K ⊗ Δ[1]) ≫ e := by
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleTimeReindex_pre, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLastUnitCollar_last,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleTimeReindex_post, Category.assoc, hs]
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleTimeReindex_forget, Category.assoc,
    ← Category.assoc _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLastUnitCollarSide (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingSquareUnitCollapse 1) e,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLastUnitCollarSide_collapse]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro a
  rfl


lemma dgGluingLastUnitCollarFamily_first {K : SSet.{u}} :
    (stdSimplex.δ (2 : Fin 3) ▷ (K ⊗ Δ[1])) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleTimeReindex _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLastUnitCollar =
    (Δ[1] ◁ fst K (Δ[1] : SSet.{u})) ≫ (stdSimplex.δ (2 : Fin 3) ▷ K) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (Δ[2] ⊗ K) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleTimeReindex_pre, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLastUnitCollar_first]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro a
  rfl
lemma dgGluingLastUnitCollarFamily_zero {K : SSet.{u}} :
    (Δ[2] ◁ (ι₀ : K ⟶ _)) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleTimeReindex _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLastUnitCollar =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0 ▷ K) ≫ (α_ (Δ[1] : SSet.{u}) Δ[1] K).hom ≫
        (Δ[1] ◁ (stdSimplex.δ (2 : Fin 3) ▷ K)) := by
  calc
    _ = ((ι₀ ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLastUnitCollar) ▷ K) ≫
        (α_ (Δ[1] : SSet.{u}) Δ[2] K).hom := by
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro a
      rfl
    _ = _ := by
      rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLastUnitCollar_zero, comp_whiskerRight, Category.assoc]
      rfl
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
