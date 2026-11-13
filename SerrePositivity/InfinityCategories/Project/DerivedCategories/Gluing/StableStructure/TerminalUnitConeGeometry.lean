module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.ComparisonModels.LastUnitCollarGeometry
/-! # 終辺単位三角形の対角閉路

概要：終辺が単位である標準二単体を、初辺と対角辺を結ぶ正方形として保持する。
方針：終側補正の対角から位相を忘れ、終辺退化の全正方形を計算する。
規約：正方形の代表を変更せず、退化後も全時間の等式を要求する。
使われ方：D の第二入力の厳密単位則から右単位閉路を消去する。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped _root_.Simplicial

def dgGluingTerminalUnitCone : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ Δ[2] :=
  (stdSimplex.δ (1 : Fin 3) ▷ (Δ[1] : SSet.{u})) ≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLastUnitCollar ≫ snd (Δ[1] : SSet.{u}) Δ[2]

lemma dgGluingTerminalUnitCone_collapse :
    dgGluingTerminalUnitCone ≫ stdSimplex.σ (1 : Fin 2) =
      fst (Δ[1] : SSet.{u}) Δ[1] := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout.hom_ext
  all_goals apply SSet.yonedaEquiv.injective
  all_goals apply SSet.stdSimplex.ext
  all_goals intro j
  all_goals fin_cases j <;> rfl
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
