module

public import SerrePositivity.InfinityCategories.F1B.MappingSpaces.MappingParameters
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.IntervalComparisonMono

/-!
概要：区間模型の写像空間への関手の作用と右 pinched 比較の整合。
方針：区間の族を標的の射で後合成し、同じ端点で curry する。
規約：quasicategory 性を仮定せず、単体集合の射の等式で自然性を示す。
使われ方：Kerodon Prop 6.2.1.17 の写像空間比較の関手性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：単体集合の射が区間模型の写像空間に誘導する射。
方針：普遍区間族を後合成し、両端の像を確認して curry する。
規約：端点は指定された F の像。標的の Kan 性は不要。
使われ方：右 pinched 比較との自然性と adjunct 比較への接続。 -/
noncomputable def intervalFunctorMap {X Y : SSet.{u}} (F : X ⟶ Y) (x y : X _⦋0⦌) :
    intervalMappingSpace x y ⟶
      intervalMappingSpace (F.app (Opposite.op ⦋0⦌) x) (F.app (Opposite.op ⦋0⦌) y) :=
  intervalFamilyCurry (intervalMappingUncurry (𝟙 (intervalMappingSpace x y)) ≫ F)
    (by rw [← Category.assoc, intervalFamily_zero, SSet.const_comp])
    (by rw [← Category.assoc, intervalFamily_one, SSet.const_comp])

/-- 概要：関手の作用は任意の区間族の後合成を表す。
方針：区間模型の普遍性とパラメータ自然性を使う。
規約：パラメータ A は任意。
使われ方：区間模型と pinched 模型の比較の自然性。 -/
lemma intervalFunctorMap_uncurry {A X Y : SSet.{u}} {x y : X _⦋0⦌}
    (f : A ⟶ intervalMappingSpace x y) (F : X ⟶ Y) :
    intervalMappingUncurry (f ≫ intervalFunctorMap F x y) = intervalMappingUncurry f ≫ F := by
  rw [intervalMappingUncurry_precomp]
  unfold intervalFunctorMap
  rw [intervalFamilyUncurry_curry, ← Category.assoc,
    ← intervalMappingUncurry_precomp, Category.comp_id]

/-- 概要：右 pinched 比較は単体集合の射の作用と厳密に整合する。
方針：両辺を区間族に展開し、join の展開と後合成の自然性を使う。
規約：ホモトピーまででなく射の等式。標的の quasicategory 性も不要。
使われ方：Kerodon Prop 6.2.1.17 の模型の変更と関手の作用の接続。 -/
lemma pinchedIntervalComparison_naturality {X Y : SSet.{u}} (F : X ⟶ Y)
    (x y : X _⦋0⦌) :
    pinchedHomMap F x y ≫
        SerrePositivity.InfinityCategories.pinchedHomToIntervalMappingSpace (F.app (Opposite.op ⦋0⦌) x) (F.app (Opposite.op ⦋0⦌) y) =
      SerrePositivity.InfinityCategories.pinchedHomToIntervalMappingSpace x y ≫ intervalFunctorMap F x y := by
  apply intervalMappingUncurry_injective
  rw [SerrePositivity.InfinityCategories.pinchedHomToIntervalMappingSpace_uncurry, intervalFunctorMap_uncurry]
  have hp : pinchedHomUncurry (pinchedHomMap F x y) =
      pinchedHomUncurry (𝟙 (pinchedHom x y)) ≫ F := by
    simpa only [Category.id_comp] using pinchedHomUncurry_postcomp (𝟙 (pinchedHom x y)) F
  have hc : intervalMappingUncurry (SerrePositivity.InfinityCategories.pinchedHomToIntervalMappingSpace x y) =
      rightMappingSpacePrism (pinchedHom x y) ≫ pinchedHomUncurry (𝟙 (pinchedHom x y)) := by
    simpa only [Category.id_comp] using SerrePositivity.InfinityCategories.pinchedHomToIntervalMappingSpace_uncurry (𝟙 (pinchedHom x y))
  rw [hp, hc, Category.assoc]

end SerrePositivity.InfinityCategories
