module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.ComparisonModels.FirstUnitCollarGeometry
/-! # 初辺単位三角形を対角の閉路として読む再添字

概要：初辺が単位である二単体を、元対角と終辺を結ぶ区間正方形へ読む。
方針：既存の始側補正の対角から位相因子を忘れる。
規約：二つの時間端は二単体の対角辺と終辺を厳密に回収する。
使われ方：相対四面体比較から残る左単位対角の零性を取り出す。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped _root_.Simplicial

def dgGluingInitialUnitCone : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ Δ[2] :=
  (stdSimplex.δ (1 : Fin 3) ▷ (Δ[1] : SSet.{u})) ≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstUnitCollar ≫ snd (Δ[1] : SSet.{u}) Δ[2]

lemma dgGluingInitialUnitCone_source :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (Δ[1] : SSet.{u}) ≫ dgGluingInitialUnitCone =
      stdSimplex.δ (2 : Fin 3) := by
  apply SSet.yonedaEquiv.injective
  apply SSet.stdSimplex.ext
  intro j
  fin_cases j <;> rfl

lemma dgGluingInitialUnitCone_target :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[1] : SSet.{u}) ≫ dgGluingInitialUnitCone =
      (SSet.const (stdSimplex.obj₀Equiv.symm 1) : (Δ[1] : SSet.{u}) ⟶ Δ[1]) ≫
        stdSimplex.δ (0 : Fin 3) := by
  apply SSet.yonedaEquiv.injective
  apply SSet.stdSimplex.ext
  intro j
  fin_cases j <;> rfl

lemma dgGluingInitialUnitCone_zero :
    (ι₀ : (Δ[1] : SSet.{u}) ⟶ _) ≫ dgGluingInitialUnitCone =
      stdSimplex.δ (1 : Fin 3) := by
  apply SSet.yonedaEquiv.injective
  apply SSet.stdSimplex.ext
  intro j
  fin_cases j <;> rfl

lemma dgGluingInitialUnitCone_one :
    (ι₁ : (Δ[1] : SSet.{u}) ⟶ _) ≫ dgGluingInitialUnitCone =
      stdSimplex.δ (0 : Fin 3) := by
  apply SSet.yonedaEquiv.injective
  apply SSet.stdSimplex.ext
  intro j
  fin_cases j <;> rfl

lemma dgGluingInitialUnitCone_collapse :
    dgGluingInitialUnitCone ≫ stdSimplex.σ (0 : Fin 2) =
      fst (Δ[1] : SSet.{u}) Δ[1] := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout.hom_ext
  all_goals apply SSet.yonedaEquiv.injective
  all_goals apply SSet.stdSimplex.ext
  all_goals intro j
  all_goals fin_cases j <;> rfl
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
