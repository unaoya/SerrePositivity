module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.FreeHammockMapAugmentation
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.FreeHammockMapComparison
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.FreeHammockUnit

/-!
# 同じ自由 hammock の係数移送の単位・合成則

概要：Dwyer–Kan §9 の同じ自由局所化比較の係数自然性を全関手へ移す。
方針：元の各自由次数の固定端点の係数写像を回収する。
規約：既存の Hom 写像・空語の単位・連結合成を変えない。
使われ方：HA §4.2.3 の BE 加群族の指定辺の照合。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.Modules
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open SerrePositivity.EInfinity _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
open SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
variable {C D : RelativeCategory.{u}} (F : C ⟶ D)

/-- 概要：同じ自由次数の写像は元の固定端点の係数写像（Dwyer–Kan §9）。
方針：全語の余極限の写像を各包含で比較する。
規約：元の自由次数と端点。使われ方：単位・合成の保存の計算。 -/
lemma freeHammockCoefficient_fixedColimitMap (X Y : C.category) (n : SimplexCategoryᵒᵖ) :
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockMap F X Y).app n =
      Hammock.Relative.fixedColimitMap ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionMap F).app n)
        (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionMap_object F n X) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionMap_object F n Y) := by
  change colim.map _ = colim.map _
  apply congrArg colim.map
  apply NatTrans.ext
  funext w
  exact (Hammock.Relative.fixedGraphDiagramMap_app ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionMap F).app n)
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionMap_object F n X) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionMap_object F n Y) w).symm

/-- 概要：同じ自由対角の係数写像は空語の単位を保つ（Dwyer–Kan §9）。
方針：各自由次数の固定端点の単位保存を使う。
規約：原圏の恒等射の生成語に取り替えない。使われ方：全豊穣関手の単位則。 -/
lemma freeHammockCoefficient_unit (X : C.category) :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalUnit C X ≫ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalMap F X X =
      _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalUnit D (F.functor.obj X) := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro x
  cases x
  change ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockMap F X X).app n).app n
    ((colimitUnit ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolution C).obj n).weakEquivalences
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionObject C n X)).app n PUnit.unit) = _
  rw [freeHammockCoefficient_fixedColimitMap]
  exact Hammock.Relative.fixedColimitMap_unit_point _ _ n

/-- 概要：同じ自由対角の係数写像は全連結合成を保つ（Dwyer–Kan §9）。
方針：各自由次数の固定端点の合成保存を使う。
規約：全単体の写像の等式。使われ方：全豊穣関手の合成則。 -/
lemma freeHammockCoefficient_comp (X Y Z : C.category) :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalComposition C X Y Z ≫ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalMap F X Z =
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalMap F X Y ⊗ₘ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalMap F Y Z) ≫
        _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalComposition D (F.functor.obj X) (F.functor.obj Y) (F.functor.obj Z) := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro z
  change ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockMap F X Z).app n).app n
    (composePoint ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolution C).obj n).weakEquivalences
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionObject C n X) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionObject C n Y) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionObject C n Z) z.1 z.2) =
    composePoint ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolution D).obj n).weakEquivalences _ _ _
      (((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockMap F X Y).app n).app n z.1)
      (((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockMap F Y Z).app n).app n z.2)
  rw [freeHammockCoefficient_fixedColimitMap, freeHammockCoefficient_fixedColimitMap,
    freeHammockCoefficient_fixedColimitMap]
  exact Hammock.Relative.fixedColimitMap_composePoint _ _ _ _ z.1 z.2

end SerrePositivity.EInfinity.Modules
