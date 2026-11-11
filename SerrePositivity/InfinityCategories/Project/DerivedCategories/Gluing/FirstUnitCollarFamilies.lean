module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.FirstUnitCollarGeometry
/-! # 全パラメーター付き始側単位補正

概要：始側の単位貼り合わせを持つ三角形 prism を、元始辺固定の三角形族へ戻す。
方針：区間と入力の順序を交換し、補正の有限再添字を全入力へ適用する。
規約：固定始辺・終辺・元端を全パラメーターで保持する。
使われ方：実前正規化の三角形を元入力の fiber 内へ移す。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped _root_.Simplicial
def dgGluingTriangleTimeReindex {A B K : SSet.{u}} (W : A ⊗ Δ[1] ⟶ (Δ[1] : SSet.{u}) ⊗ B) :
    A ⊗ (K ⊗ Δ[1]) ⟶ Δ[1] ⊗ (B ⊗ K) :=
  (A ◁ (β_ K (Δ[1] : SSet.{u})).hom) ≫ (α_ A (Δ[1] : SSet.{u}) K).inv ≫
    (W ▷ K) ≫ (α_ (Δ[1] : SSet.{u}) B K).hom
lemma dgGluingTriangleTimeReindex_pre {A A' B K : SSet.{u}} (f : A' ⟶ A)
    (W : A ⊗ Δ[1] ⟶ (Δ[1] : SSet.{u}) ⊗ B) :
    (f ▷ (K ⊗ Δ[1])) ≫ dgGluingTriangleTimeReindex W =
      dgGluingTriangleTimeReindex ((f ▷ Δ[1]) ≫ W) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro a
  rfl
lemma dgGluingTriangleTimeReindex_post {A B B' K : SSet.{u}} (f : B ⟶ B')
    (W : A ⊗ Δ[1] ⟶ (Δ[1] : SSet.{u}) ⊗ B) :
    dgGluingTriangleTimeReindex (K := K) (W ≫ (Δ[1] ◁ f)) =
      dgGluingTriangleTimeReindex W ≫ (Δ[1] ◁ (f ▷ K)) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro a
  rfl
lemma dgGluingTriangleTimeReindex_forget {A B K : SSet.{u}}
    (W : A ⊗ Δ[1] ⟶ (Δ[1] : SSet.{u}) ⊗ B) :
    dgGluingTriangleTimeReindex (K := K) W ≫ (Δ[1] ◁ fst B K) =
      (A ◁ snd K (Δ[1] : SSet.{u})) ≫ W := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro a
  rfl


lemma dgGluingFirstUnitCollarFamily_first {Z K : SSet.{u}}
    (T : (Δ[1] : SSet.{u}) ⊗ (Δ[2] ⊗ K) ⟶ Z) (e : (Δ[1] : SSet.{u}) ⟶ Z)
    (hs : (Δ[1] ◁ (stdSimplex.δ (2 : Fin 3) ▷ K)) ≫ T =
      (Δ[1] ◁ fst (Δ[1] : SSet.{u}) K) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingSquareUnitCollapse 0 ≫ e) :
    (stdSimplex.δ (2 : Fin 3) ▷ (K ⊗ Δ[1])) ≫
      (dgGluingTriangleTimeReindex _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstUnitCollar ≫ T) =
      fst (Δ[1] : SSet.{u}) (K ⊗ Δ[1]) ≫ e := by
  rw [← Category.assoc, dgGluingTriangleTimeReindex_pre, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstUnitCollar_first,
    dgGluingTriangleTimeReindex_post, Category.assoc, hs]
  rw [← Category.assoc, dgGluingTriangleTimeReindex_forget, Category.assoc,
    ← Category.assoc _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstUnitCollarSide (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingSquareUnitCollapse 0) e,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstUnitCollarSide_collapse]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro a
  rfl


lemma dgGluingFirstUnitCollarFamily_last {K : SSet.{u}} :
    (stdSimplex.δ (0 : Fin 3) ▷ (K ⊗ Δ[1])) ≫
      dgGluingTriangleTimeReindex _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstUnitCollar =
    (Δ[1] ◁ fst K (Δ[1] : SSet.{u})) ≫ (stdSimplex.δ (0 : Fin 3) ▷ K) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[2] ⊗ K) := by
  rw [dgGluingTriangleTimeReindex_pre, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstUnitCollar_last]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro a
  rfl
lemma dgGluingFirstUnitCollarFamily_one {K : SSet.{u}} :
    (Δ[2] ◁ (ι₁ : K ⟶ _)) ≫ dgGluingTriangleTimeReindex _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstUnitCollar =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ▷ K) ≫ (α_ (Δ[1] : SSet.{u}) Δ[1] K).hom ≫
        (Δ[1] ◁ (stdSimplex.δ (0 : Fin 3) ▷ K)) := by
  calc
    _ = ((ι₁ ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstUnitCollar) ▷ K) ≫
        (α_ (Δ[1] : SSet.{u}) Δ[2] K).hom := by
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro a
      rfl
    _ = _ := by
      rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstUnitCollar_one, comp_whiskerRight, Category.assoc]
      rfl
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
