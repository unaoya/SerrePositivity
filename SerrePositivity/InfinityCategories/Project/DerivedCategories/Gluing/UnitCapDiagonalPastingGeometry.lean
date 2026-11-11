module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.UnitCapGeometry
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.UnitCollarDiagonalTriangleGeometry
/-! # 係数側の単位補正を貼り合わせる六つの対角三角形

概要：二つの単位補正・正規化係数面・補正端間の橋を、同じ四面体上の六片で結ぶ。
方針：辺の両端の位相と四面体頂点を有限単調写像として同時に指定する。
規約：各片は同じ augmentation 四面体への再添字であり、共有辺を厳密に保持する。
使われ方：実補正対角の合成と係数 path を高次貼り合わせで比較する。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped _root_.Simplicial

def dgGluingUnitCapPastingPhase (i : Fin 6) : Fin 2 × Fin 3 →o Fin 2 where
  toFun p := if p.1 = 0 then
      (![![0, 1, 1], ![0, 0, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 1], ![0, 0, 0]] :
        Fin 6 → Fin 3 → Fin 2) i p.2
    else
      (![![1, 1, 1], ![1, 1, 1], ![0, 0, 1], ![0, 1, 1], ![0, 1, 1], ![1, 1, 1]] :
        Fin 6 → Fin 3 → Fin 2) i p.2
  monotone' := by fin_cases i <;> decide

def dgGluingUnitCapPastingVertex (i : Fin 6) : Fin 2 × Fin 3 →o Fin 4 where
  toFun p := if p.1 = 0 then
      (![![0, 0, 0], ![0, 0, 0], ![0, 1, 1], ![0, 0, 1], ![0, 0, 0], ![0, 0, 1]] :
        Fin 6 → Fin 3 → Fin 4) i p.2
    else
      (![![2, 2, 3], ![2, 3, 3], ![3, 3, 3], ![3, 3, 3], ![3, 3, 3], ![2, 3, 3]] :
        Fin 6 → Fin 3 → Fin 4) i p.2
  monotone' := by fin_cases i <;> decide

def dgGluingUnitCapPastingTriangle (i : Fin 6) :
    (Δ[1] : SSet.{u}) ⊗ Δ[2] ⟶ Δ[1] ⊗ Δ[3] :=
  lift (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.stdSimplexProductMap (dgGluingUnitCapPastingPhase i))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.stdSimplexProductMap (dgGluingUnitCapPastingVertex i))

lemma dgGluingUnitCapPastingTriangle_first_diagonal :
    (Δ[1] ◁ stdSimplex.δ (1 : Fin 3)) ≫ dgGluingUnitCapPastingTriangle.{u} 0 =
      (Δ[1] ◁ stdSimplex.δ (1 : Fin 3)) ≫ dgGluingUnitCapPastingTriangle 1 := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout.hom_ext
  all_goals apply SSet.yonedaEquiv.injective
  all_goals apply Prod.ext
  all_goals apply SSet.stdSimplex.ext
  all_goals intro j
  all_goals fin_cases j <;> rfl

lemma dgGluingUnitCapPastingTriangle_last_diagonal :
    (Δ[1] ◁ stdSimplex.δ (1 : Fin 3)) ≫ dgGluingUnitCapPastingTriangle.{u} 2 =
      (Δ[1] ◁ stdSimplex.δ (1 : Fin 3)) ≫ dgGluingUnitCapPastingTriangle 3 := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout.hom_ext
  all_goals apply SSet.yonedaEquiv.injective
  all_goals apply Prod.ext
  all_goals apply SSet.stdSimplex.ext
  all_goals intro j
  all_goals fin_cases j <;> rfl

lemma dgGluingUnitCapPastingTriangle_first_bridge :
    (Δ[1] ◁ stdSimplex.δ (2 : Fin 3)) ≫ dgGluingUnitCapPastingTriangle.{u} 1 =
      (Δ[1] ◁ stdSimplex.δ (2 : Fin 3)) ≫ dgGluingUnitCapPastingTriangle 5 := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout.hom_ext
  all_goals apply SSet.yonedaEquiv.injective
  all_goals apply Prod.ext
  all_goals apply SSet.stdSimplex.ext
  all_goals intro j
  all_goals fin_cases j <;> rfl

lemma dgGluingUnitCapPastingTriangle_last_bridge :
    (Δ[1] ◁ stdSimplex.δ (0 : Fin 3)) ≫ dgGluingUnitCapPastingTriangle.{u} 3 =
      (Δ[1] ◁ stdSimplex.δ (0 : Fin 3)) ≫ dgGluingUnitCapPastingTriangle 5 := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout.hom_ext
  all_goals apply SSet.yonedaEquiv.injective
  all_goals apply Prod.ext
  all_goals apply SSet.stdSimplex.ext
  all_goals intro j
  all_goals fin_cases j <;> rfl

lemma dgGluingUnitCapPastingTriangle_coefficient_first :
    (Δ[1] ◁ stdSimplex.δ (0 : Fin 3)) ≫ dgGluingUnitCapPastingTriangle.{u} 1 =
      (Δ[1] ◁ stdSimplex.δ (0 : Fin 3)) ≫ dgGluingUnitCapPastingTriangle 4 := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout.hom_ext
  all_goals apply SSet.yonedaEquiv.injective
  all_goals apply Prod.ext
  all_goals apply SSet.stdSimplex.ext
  all_goals intro j
  all_goals fin_cases j <;> rfl

lemma dgGluingUnitCapPastingTriangle_coefficient_last :
    (Δ[1] ◁ stdSimplex.δ (2 : Fin 3)) ≫ dgGluingUnitCapPastingTriangle.{u} 3 =
      (Δ[1] ◁ stdSimplex.δ (2 : Fin 3)) ≫ dgGluingUnitCapPastingTriangle 4 := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout.hom_ext
  all_goals apply SSet.yonedaEquiv.injective
  all_goals apply Prod.ext
  all_goals apply SSet.stdSimplex.ext
  all_goals intro j
  all_goals fin_cases j <;> rfl

lemma dgGluingUnitCapPastingTriangle_collar_bridge :
    (Δ[1] ◁ stdSimplex.δ (1 : Fin 3)) ≫ dgGluingUnitCapPastingTriangle.{u} 5 =
      (Δ[1] ◁ stdSimplex.δ (1 : Fin 3)) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitCollarDiagonalTriangle := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout.hom_ext
  all_goals apply SSet.yonedaEquiv.injective
  all_goals apply Prod.ext
  all_goals apply SSet.stdSimplex.ext
  all_goals intro j
  all_goals fin_cases j <;> rfl

lemma dgGluingUnitCapPastingTriangle_first_cap :
    (Δ[1] ◁ stdSimplex.δ (2 : Fin 3)) ≫ dgGluingUnitCapPastingTriangle.{u} 0 =
      (stdSimplex.δ (1 : Fin 3) ▷ (Δ[1] : SSet.{u})) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstUnitCap ≫ (Δ[1] ◁ stdSimplex.δ (3 : Fin 4)) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout.hom_ext
  all_goals apply SSet.yonedaEquiv.injective
  all_goals apply Prod.ext
  all_goals apply SSet.stdSimplex.ext
  all_goals intro j
  all_goals fin_cases j <;> rfl

lemma dgGluingUnitCapPastingTriangle_last_cap :
    (Δ[1] ◁ stdSimplex.δ (0 : Fin 3)) ≫ dgGluingUnitCapPastingTriangle.{u} 2 =
      (stdSimplex.δ (1 : Fin 3) ▷ (Δ[1] : SSet.{u})) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLastUnitCap ≫ (Δ[1] ◁ stdSimplex.δ (0 : Fin 4)) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout.hom_ext
  all_goals apply SSet.yonedaEquiv.injective
  all_goals apply Prod.ext
  all_goals apply SSet.stdSimplex.ext
  all_goals intro j
  all_goals fin_cases j <;> rfl

lemma dgGluingUnitCapPastingTriangle_coefficient_diagonal :
    (Δ[1] ◁ stdSimplex.δ (1 : Fin 3)) ≫ dgGluingUnitCapPastingTriangle.{u} 4 =
      (β_ (Δ[1] : SSet.{u}) Δ[1]).hom ≫
        (Δ[1] ◁ (stdSimplex.δ (1 : Fin 3) ≫ stdSimplex.δ (1 : Fin 4))) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout.hom_ext
  all_goals apply SSet.yonedaEquiv.injective
  all_goals apply Prod.ext
  all_goals apply SSet.stdSimplex.ext
  all_goals intro j
  all_goals fin_cases j <;> rfl

lemma dgGluingUnitCapPastingTriangle_first_unit :
    (Δ[1] ◁ stdSimplex.δ (0 : Fin 3)) ≫ dgGluingUnitCapPastingTriangle.{u} 0 =
      (stdSimplex.δ (1 : Fin 3) ▷ (Δ[1] : SSet.{u})) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLastUnitCollar ≫ snd (Δ[1] : SSet.{u}) Δ[2] ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 Δ[2] ≫ (Δ[1] ◁ stdSimplex.δ (1 : Fin 4)) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout.hom_ext
  all_goals apply SSet.yonedaEquiv.injective
  all_goals apply Prod.ext
  all_goals apply SSet.stdSimplex.ext
  all_goals intro j
  all_goals fin_cases j <;> rfl

lemma dgGluingUnitCapPastingTriangle_last_unit :
    (Δ[1] ◁ stdSimplex.δ (2 : Fin 3)) ≫ dgGluingUnitCapPastingTriangle.{u} 2 =
      (stdSimplex.δ (1 : Fin 3) ▷ (Δ[1] : SSet.{u})) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstUnitCollar ≫ snd (Δ[1] : SSet.{u}) Δ[2] ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 Δ[2] ≫ (Δ[1] ◁ stdSimplex.δ (2 : Fin 4)) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout.hom_ext
  all_goals apply SSet.yonedaEquiv.injective
  all_goals apply Prod.ext
  all_goals apply SSet.stdSimplex.ext
  all_goals intro j
  all_goals fin_cases j <;> rfl

def dgGluingUnitCapPastingSourceSide (i : Fin 6) :
    (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ Δ[1] ⊗ Δ[3] :=
  (stdSimplex.δ (1 : Fin 3) ▷ (Δ[1] : SSet.{u})) ≫
    (if i = 0 ∨ i = 1 ∨ i = 4 then _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstUnitCap else _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstUnitCollar) ≫
      (Δ[1] ◁ stdSimplex.δ (3 : Fin 4))

def dgGluingUnitCapPastingTargetSide (i : Fin 6) :
    (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ Δ[1] ⊗ Δ[3] :=
  (stdSimplex.δ (1 : Fin 3) ▷ (Δ[1] : SSet.{u})) ≫
    (if i = 2 ∨ i = 3 ∨ i = 4 then _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLastUnitCap else _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLastUnitCollar) ≫
      (Δ[1] ◁ stdSimplex.δ (0 : Fin 4))

lemma dgGluingUnitCapPastingTriangle_source_retract (i : Fin 6) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (Δ[2] : SSet.{u}) ≫ dgGluingUnitCapPastingTriangle i =
      stdSimplex.σ ((![1, 0, 1, 0, 0, 0] : Fin 6 → Fin 2) i) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (Δ[1] : SSet.{u}) ≫ dgGluingUnitCapPastingSourceSide i := by
  fin_cases i
  all_goals apply SSet.yonedaEquiv.injective
  all_goals apply Prod.ext
  all_goals apply SSet.stdSimplex.ext
  all_goals intro j
  all_goals fin_cases j <;> rfl

lemma dgGluingUnitCapPastingTriangle_target_retract (i : Fin 6) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[2] : SSet.{u}) ≫ dgGluingUnitCapPastingTriangle i =
      stdSimplex.σ ((![0, 1, 0, 1, 1, 1] : Fin 6 → Fin 2) i) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[1] : SSet.{u}) ≫ dgGluingUnitCapPastingTargetSide i := by
  fin_cases i
  all_goals apply SSet.yonedaEquiv.injective
  all_goals apply Prod.ext
  all_goals apply SSet.stdSimplex.ext
  all_goals intro j
  all_goals fin_cases j <;> rfl
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
