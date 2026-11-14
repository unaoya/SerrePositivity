module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.ComparisonModels.FirstUnitCollarGeometry
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.ComparisonModels.LastUnitCollarGeometry
/-! # 四面体上の左右補正対角を結ぶ実三角形

概要：始側と終側の補正対角を、同じ augmentation 四面体上の三角形へまとめる。
方針：辺変数と三角形変数の有限単調写像で再添字する。
規約：二つの補正対角をそのまま指定面に保ち、第三辺を共通補正端間の橋とする。
使われ方：選択済み変形の対角比較に使う高次貼り合わせの始側を構成する。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped _root_.Simplicial

def dgGluingUnitCollarDiagonalTriangleVertex : Fin 2 × Fin 3 →o Fin 4 where
  toFun p := if p.1 = 0 then (if p.2 = 0 then 0 else 1)
    else (if p.2 = 2 then 3 else 2)
  monotone' := by decide

def dgGluingUnitCollarDiagonalTriangle :
    (Δ[1] : SSet.{u}) ⊗ Δ[2] ⟶ Δ[1] ⊗ Δ[3] :=
  lift (fst _ _) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.stdSimplexProductMap dgGluingUnitCollarDiagonalTriangleVertex)

lemma dgGluingUnitCollarDiagonalTriangle_two :
    (Δ[1] ◁ stdSimplex.δ (2 : Fin 3)) ≫ dgGluingUnitCollarDiagonalTriangle.{u} =
      (stdSimplex.δ (1 : Fin 3) ▷ (Δ[1] : SSet.{u})) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstUnitCollar ≫ (Δ[1] ◁ stdSimplex.δ (3 : Fin 4)) := by
  apply SSet.hom_ext
  intro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro p
  apply Prod.ext
  · apply SSet.stdSimplex.ext
    intro j
    change p.1 j = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstUnitCollarPhase
      ((SimplexCategory.δ (1 : Fin 3)).toOrderHom (p.1 j), p.2 j)
    generalize h : p.1 j = e
    generalize ht : p.2 j = t
    fin_cases e <;> fin_cases t <;> rfl
  · apply SSet.stdSimplex.ext
    intro j
    change dgGluingUnitCollarDiagonalTriangleVertex
      (p.1 j, (SimplexCategory.δ (2 : Fin 3)).toOrderHom (p.2 j)) =
      (SimplexCategory.δ (3 : Fin 4)).toOrderHom
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstUnitCollarVertex
          ((SimplexCategory.δ (1 : Fin 3)).toOrderHom (p.1 j), p.2 j))
    generalize h : p.1 j = e
    generalize ht : p.2 j = t
    fin_cases e <;> fin_cases t <;> rfl

lemma dgGluingUnitCollarDiagonalTriangle_zero :
    (Δ[1] ◁ stdSimplex.δ (0 : Fin 3)) ≫ dgGluingUnitCollarDiagonalTriangle.{u} =
      (stdSimplex.δ (1 : Fin 3) ▷ (Δ[1] : SSet.{u})) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLastUnitCollar ≫ (Δ[1] ◁ stdSimplex.δ (0 : Fin 4)) := by
  apply SSet.hom_ext
  intro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro p
  apply Prod.ext
  · apply SSet.stdSimplex.ext
    intro j
    change p.1 j = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLastUnitCollarPhase
      ((SimplexCategory.δ (1 : Fin 3)).toOrderHom (p.1 j), p.2 j)
    generalize h : p.1 j = e
    generalize ht : p.2 j = t
    fin_cases e <;> fin_cases t <;> rfl
  · apply SSet.stdSimplex.ext
    intro j
    change dgGluingUnitCollarDiagonalTriangleVertex
      (p.1 j, (SimplexCategory.δ (0 : Fin 3)).toOrderHom (p.2 j)) =
      (SimplexCategory.δ (0 : Fin 4)).toOrderHom
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLastUnitCollarVertex
          ((SimplexCategory.δ (1 : Fin 3)).toOrderHom (p.1 j), p.2 j))
    generalize h : p.1 j = e
    generalize ht : p.2 j = t
    fin_cases e <;> fin_cases t <;> rfl


lemma dgGluingUnitCollarDiagonalTriangle_source_retract :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (Δ[2] : SSet.{u}) ≫ dgGluingUnitCollarDiagonalTriangle =
      stdSimplex.σ (1 : Fin 2) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (Δ[1] : SSet.{u}) ≫
        (Δ[1] ◁ stdSimplex.δ (2 : Fin 3)) ≫ dgGluingUnitCollarDiagonalTriangle := by
  apply SSet.yonedaEquiv.injective
  apply Prod.ext
  all_goals apply SSet.stdSimplex.ext
  all_goals intro j
  all_goals fin_cases j <;> rfl

lemma dgGluingUnitCollarDiagonalTriangle_target_retract :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[2] : SSet.{u}) ≫ dgGluingUnitCollarDiagonalTriangle =
      stdSimplex.σ (0 : Fin 2) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[1] : SSet.{u}) ≫
        (Δ[1] ◁ stdSimplex.δ (0 : Fin 3)) ≫ dgGluingUnitCollarDiagonalTriangle := by
  apply SSet.yonedaEquiv.injective
  apply Prod.ext
  all_goals apply SSet.stdSimplex.ext
  all_goals intro j
  all_goals fin_cases j <;> rfl
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
