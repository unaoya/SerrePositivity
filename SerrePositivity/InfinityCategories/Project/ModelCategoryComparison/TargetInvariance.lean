module

public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.BrownInversion
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.BoundaryTensor
public import SerrePositivity.HomotopicalAlgebra.Simplicial.MonoRightLiftingContraction

/-!
# 単体集合のモデル構造を使わない frame Hom の終域不変性

概要：Hovey §5 の frame Hom は fibrant な終域の弱同値を anodyne 局所化後に反転する。
方針：境界の右持ち上げ性で自明 fibration の像を反転し、Brown 分解を使う。
規約：値の局所化は任意、単体集合の完全なモデル構造は仮定しない。
使われ方：E 代数の導来写像空間と一般 homotopy 極限のホモトピー不変性。
-/

@[expose] public section

noncomputable section

universe u v u' v'

namespace SerrePositivity.InfinityCategories.Project.ModelCategoryComparison

open CategoryTheory Limits HomotopicalAlgebra
open _root_.SerrePositivity.Reedy _root_.SerrePositivity.HomotopyFunctionComplex

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (B : SimplexCategory ⥤ C)
  (hB : reedyLeft simplex (cofibrations C) (initial.to B))

include hB

/-- 概要：frame Hom は自明 fibration を境界の右類に移す（Hovey §5）。
方針：Reedy cofibrancy による境界の持ち上げを使う。
規約：単体集合のモデル構造ではなく実際の境界生成族で判定する。
使われ方：終域の自明 fibration の像を anodyne 局所化で反転する。 -/
lemma target_boundary_rlp {Y Z : C} (p : Y ⟶ Z) [Fibration p] [WeakEquivalence p] :
    SSet.modelCategoryQuillen.I.rlp ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom B).map p) := by
  intro X Y i hi
  obtain ⟨n⟩ := hi
  exact boundary_lifting_of_reedyCofibrant B n hB p

variable {D : Type u'} [Category.{v'} D] (L : SSet.{v} ⥤ D)
  (hL : SSet.anodyneExtensions.IsInvertedBy L)

include hL

/-- 概要：frame Hom の自明 fibration の像は anodyne 反転後に同型（Hovey §5）。
方針：すべての単射の右持ち上げ性から切断と実際の収縮を使う。
規約：単体集合の弱同値類やモデル存在は入力しない。
使われ方：Brown 分解の自明 fibration の反転の入力。 -/
lemma target_trivialFibration_isIso {Y Z : C} (p : Y ⟶ Z)
    [Fibration p] [WeakEquivalence p] : IsIso (L.map ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom B).map p)) :=
  SimplicialModel.MonoRightLiftingContraction.image_isIso _
    (SSet.rlp_monomorphisms.ge _ (target_boundary_rlp B hB p)) L hL

/-- 概要：frame Hom は fibrant な終域の弱同値を anodyne 反転後に同型へ移す（Hovey §5）。
方針：自明 fibration の反転を任意の値圏に対する Brown 分解へ渡す。
規約：終域の二つの fibrancy 以外の cofibrancy は要求しない。
使われ方：具体的な E 代数の終域に関する導来写像空間の不変性。 -/
lemma target_weakEquivalence_isIso {Y Z : C} [IsFibrant Y] [IsFibrant Z]
    (f : Y ⟶ Z) [WeakEquivalence f] : IsIso (L.map ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom B).map f)) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.map_isIso_of_fibrant (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom B ⋙ L)
  intro U V p hp
  have : Fibration p := ⟨hp.1⟩
  have : WeakEquivalence p := ⟨hp.2⟩
  exact target_trivialFibration_isIso B hB L hL p

end SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
