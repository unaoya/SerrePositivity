module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.UnitCollarDiagonalTriangleGeometry
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.FirstUnitCollarFamilies
/-! # 左右補正対角の実三角形の全入力再添字

概要：四面体上の対角三角形を全 Hom 入力へ拡張し、二つの実補正道を指定面に保つ。
方針：三角形と入力の結合を変えるだけで、有限再添字の面等式を輸送する。
規約：辺変数・時間・元入力を保持する。
使われ方：native augmentation 四面体から、補正対角の合成三角形を取り出す。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped _root_.Simplicial

def dgGluingUnitCollarDiagonalTriangleDomain (K : SSet.{u}) :
    (Δ[1] : SSet.{u}) ⊗ (Δ[2] ⊗ K) ⟶ Δ[1] ⊗ (Δ[3] ⊗ K) :=
  (α_ (Δ[1] : SSet.{u}) Δ[2] K).inv ≫
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitCollarDiagonalTriangle ▷ K) ≫ (α_ (Δ[1] : SSet.{u}) Δ[3] K).hom

lemma dgGluingUnitCollarDiagonalTriangleDomain_two (K : SSet.{u}) :
    (Δ[1] ◁ (stdSimplex.δ (2 : Fin 3) ▷ K)) ≫
        dgGluingUnitCollarDiagonalTriangleDomain K =
      (Δ[1] ◁ (β_ (Δ[1] : SSet.{u}) K).hom) ≫
        (stdSimplex.δ (1 : Fin 3) ▷ (K ⊗ Δ[1])) ≫
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleTimeReindex _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstUnitCollar ≫
            (Δ[1] ◁ (stdSimplex.δ (3 : Fin 4) ▷ K)) := by
  calc
    _ = (α_ (Δ[1] : SSet.{u}) Δ[1] K).inv ≫
        (((Δ[1] ◁ stdSimplex.δ (2 : Fin 3)) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitCollarDiagonalTriangle) ▷ K) ≫
          (α_ (Δ[1] : SSet.{u}) Δ[3] K).hom := by
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro a
      rfl
    _ = (α_ (Δ[1] : SSet.{u}) Δ[1] K).inv ≫
        (((stdSimplex.δ (1 : Fin 3) ▷ (Δ[1] : SSet.{u})) ≫
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstUnitCollar ≫ (Δ[1] ◁ stdSimplex.δ (3 : Fin 4))) ▷ K) ≫
            (α_ (Δ[1] : SSet.{u}) Δ[3] K).hom := by
      rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitCollarDiagonalTriangle_two]
    _ = _ := by
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro a
      rfl

lemma dgGluingUnitCollarDiagonalTriangleDomain_zero (K : SSet.{u}) :
    (Δ[1] ◁ (stdSimplex.δ (0 : Fin 3) ▷ K)) ≫
        dgGluingUnitCollarDiagonalTriangleDomain K =
      (Δ[1] ◁ (β_ (Δ[1] : SSet.{u}) K).hom) ≫
        (stdSimplex.δ (1 : Fin 3) ▷ (K ⊗ Δ[1])) ≫
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleTimeReindex _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLastUnitCollar ≫
            (Δ[1] ◁ (stdSimplex.δ (0 : Fin 4) ▷ K)) := by
  calc
    _ = (α_ (Δ[1] : SSet.{u}) Δ[1] K).inv ≫
        (((Δ[1] ◁ stdSimplex.δ (0 : Fin 3)) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitCollarDiagonalTriangle) ▷ K) ≫
          (α_ (Δ[1] : SSet.{u}) Δ[3] K).hom := by
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro a
      rfl
    _ = (α_ (Δ[1] : SSet.{u}) Δ[1] K).inv ≫
        (((stdSimplex.δ (1 : Fin 3) ▷ (Δ[1] : SSet.{u})) ≫
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLastUnitCollar ≫ (Δ[1] ◁ stdSimplex.δ (0 : Fin 4))) ▷ K) ≫
            (α_ (Δ[1] : SSet.{u}) Δ[3] K).hom := by
      rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitCollarDiagonalTriangle_zero]
    _ = _ := by
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro a
      rfl

lemma dgGluingUnitCollarDiagonalTriangleDomain_source_retract (K : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (Δ[2] ⊗ K) ≫ dgGluingUnitCollarDiagonalTriangleDomain K =
      (stdSimplex.σ (1 : Fin 2) ▷ K) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (Δ[1] ⊗ K) ≫
        (Δ[1] ◁ (stdSimplex.δ (2 : Fin 3) ▷ K)) ≫
          dgGluingUnitCollarDiagonalTriangleDomain K := by
  calc
    _ = ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (Δ[2] : SSet.{u}) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitCollarDiagonalTriangle) ▷ K) ≫
          (α_ (Δ[1] : SSet.{u}) Δ[3] K).hom := by
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro a
      rfl
    _ = (((stdSimplex.σ (1 : Fin 2)) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (Δ[1] : SSet.{u}) ≫
        (Δ[1] ◁ stdSimplex.δ (2 : Fin 3)) ≫
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitCollarDiagonalTriangle) ▷ K) ≫
            (α_ (Δ[1] : SSet.{u}) Δ[3] K).hom := by
      rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitCollarDiagonalTriangle_source_retract]
    _ = _ := by
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro a
      rfl

lemma dgGluingUnitCollarDiagonalTriangleDomain_target_retract (K : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[2] ⊗ K) ≫ dgGluingUnitCollarDiagonalTriangleDomain K =
      (stdSimplex.σ (0 : Fin 2) ▷ K) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[1] ⊗ K) ≫
        (Δ[1] ◁ (stdSimplex.δ (0 : Fin 3) ▷ K)) ≫
          dgGluingUnitCollarDiagonalTriangleDomain K := by
  calc
    _ = ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[2] : SSet.{u}) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitCollarDiagonalTriangle) ▷ K) ≫
          (α_ (Δ[1] : SSet.{u}) Δ[3] K).hom := by
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro a
      rfl
    _ = (((stdSimplex.σ (0 : Fin 2)) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[1] : SSet.{u}) ≫
        (Δ[1] ◁ stdSimplex.δ (0 : Fin 3)) ≫
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitCollarDiagonalTriangle) ▷ K) ≫
            (α_ (Δ[1] : SSet.{u}) Δ[3] K).hom := by
      rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitCollarDiagonalTriangle_target_retract]
    _ = _ := by
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro a
      rfl
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
