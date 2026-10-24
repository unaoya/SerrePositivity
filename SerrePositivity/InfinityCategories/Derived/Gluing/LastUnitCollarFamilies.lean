module
public import SerrePositivity.InfinityCategories.Derived.Gluing.FirstUnitCollarFamilies
public import SerrePositivity.InfinityCategories.Derived.Gluing.LastUnitCollarGeometry

/-! # 全パラメーター付き終側単位補正

概要：終側の単位貼り合わせを持つ三角形 prism を、元終辺固定の三角形族へ戻す。
方針：共通の時間再添字を使い、終側補正の有限単調写像を全入力へ適用する。
規約：固定終辺・始辺・元端を全パラメーターで保持する。
使われ方：実後正規化の共有三角形を、元終辺の合成対応へ持ち上げる。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
lemma dgGluingLastUnitCollarFamily_last {Z K : SSet.{u}}
    (T : (Δ[1] : SSet.{u}) ⊗ (Δ[2] ⊗ K) ⟶ Z) (e : (Δ[1] : SSet.{u}) ⟶ Z)
    (hs : (Δ[1] ◁ (stdSimplex.δ (0 : Fin 3) ▷ K)) ≫ T =
      (Δ[1] ◁ fst (Δ[1] : SSet.{u}) K) ≫ dgGluingSquareUnitCollapse 1 ≫ e) :
    (stdSimplex.δ (0 : Fin 3) ▷ (K ⊗ Δ[1])) ≫
      (dgGluingTriangleTimeReindex dgGluingLastUnitCollar ≫ T) =
      fst (Δ[1] : SSet.{u}) (K ⊗ Δ[1]) ≫ e := by
  rw [← Category.assoc, dgGluingTriangleTimeReindex_pre, dgGluingLastUnitCollar_last,
    dgGluingTriangleTimeReindex_post, Category.assoc, hs]
  rw [← Category.assoc, dgGluingTriangleTimeReindex_forget, Category.assoc,
    ← Category.assoc dgGluingLastUnitCollarSide (dgGluingSquareUnitCollapse 1) e,
    dgGluingLastUnitCollarSide_collapse]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro a
  rfl


lemma dgGluingLastUnitCollarFamily_first {K : SSet.{u}} :
    (stdSimplex.δ (2 : Fin 3) ▷ (K ⊗ Δ[1])) ≫
      dgGluingTriangleTimeReindex dgGluingLastUnitCollar =
    (Δ[1] ◁ fst K (Δ[1] : SSet.{u})) ≫ (stdSimplex.δ (2 : Fin 3) ▷ K) ≫
      prismEndpoint 0 (Δ[2] ⊗ K) := by
  rw [dgGluingTriangleTimeReindex_pre, dgGluingLastUnitCollar_first]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro a
  rfl
lemma dgGluingLastUnitCollarFamily_zero {K : SSet.{u}} :
    (Δ[2] ◁ (ι₀ : K ⟶ _)) ≫ dgGluingTriangleTimeReindex dgGluingLastUnitCollar =
      (squareTriangle 0 ▷ K) ≫ (α_ (Δ[1] : SSet.{u}) Δ[1] K).hom ≫
        (Δ[1] ◁ (stdSimplex.δ (2 : Fin 3) ▷ K)) := by
  calc
    _ = ((ι₀ ≫ dgGluingLastUnitCollar) ▷ K) ≫
        (α_ (Δ[1] : SSet.{u}) Δ[2] K).hom := by
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro a
      rfl
    _ = _ := by
      rw [dgGluingLastUnitCollar_zero, comp_whiskerRight, Category.assoc]
      rfl
end SerrePositivity.InfinityCategories
