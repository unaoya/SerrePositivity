module

public import SerrePositivity.InfinityCategories.F2.Presentable.PresheafBarIndex
public import SerrePositivity.InfinityCategories.F2.Presentable.PresheafSmallLeftKanExtension

/-!
概要：元の elements 図式から、一つの coherent な単体的前層図式を構成する。
方針：元の全単体の次数射影に沿う全左 Kan 延長を取る。
規約：全ての面・退化と元の指定単位を保持する。
使われ方：各次数の表現可能小余積と幾何学的実現の証明の対象。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
attribute [local instance] CategoryTheory.uliftCategory
namespace SerrePositivity.InfinityCategories.HomotopyLimits
variable {C : SSet.{u}} [Quasicategory C]
  (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u})

/-- 概要：元の bar 入力を次数に沿って延長した単体的前層図式。
方針：小さい射に沿う前層値左 Kan 延長の存在から一つを取る。
規約：値だけを選ばず、全単位付きの coherent な図式を選ぶ。
使われ方：各次数の小余積と元の前層への幾何学的実現。 -/
def presheafBarObject :
    (SSet.uliftFunctor.{u + 1, u}).obj (nerve (ULiftHom.{u} (ULift.{u} SimplexCategoryᵒᵖ))) ⟶
      PresheafInfinity C :=
  Classical.choose (presheafSmall_exists_leftKanExtension
    (nerveMap (presheafBarDegree F)) (presheafBarInputDiagram F))

/-- 概要：元の表現可能 bar 入力から同じ単体的図式への全単位。
方針：構成した左 Kan 延長に付随する単位を取る。
規約：元の次数射影との可換性を全パラメータで保つ。
使われ方：同じ次数の余積余錐と密度余錐の比較。 -/
def presheafBarUnit : SSet.Homotopy (presheafBarInputDiagram F)
    ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (presheafBarDegree F)) ≫
      presheafBarObject F) :=
  Classical.choose (Classical.choose_spec (presheafSmall_exists_leftKanExtension
    (nerveMap (presheafBarDegree F)) (presheafBarInputDiagram F)))

/-- 概要：選んだ単体的図式と同じ指定単位は全左 Kan 延長である。
方針：存在定理の選択証拠をそのまま公開する。
規約：別の単位への存在主張で代用しない。
使われ方：次数の comma の余極限と幾何学的実現の合成。 -/
lemma presheafBarUnit_isLeftKanExtension :
    IsLeftKanExtension ((SSet.uliftFunctor.{u + 1, u}).map
      (nerveMap (presheafBarDegree F))) (presheafBarInputDiagram F)
      (presheafBarObject F) (presheafBarUnit F) :=
  Classical.choose_spec (Classical.choose_spec (presheafSmall_exists_leftKanExtension
    (nerveMap (presheafBarDegree F)) (presheafBarInputDiagram F)))

end SerrePositivity.InfinityCategories.HomotopyLimits
