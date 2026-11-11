module

public import SerrePositivity.EInfinity.BarrattEccles.MappingSpace
public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.SourceInvariance

/-!
# E 代数の導来写像空間の始域・終域の不変性

概要：BM 命題 4.1・Hovey §5 の Map^h は両変数の擬同型を anodyne 反転後に同型へ移す。
方針：具体的な関手的分解の弱同値保存と、frame Hom の両側の不変性を使う。
規約：単体集合のモデル構造は不要、値圏は任意の anodyne を反転する通常の圏。
使われ方：E2a-5 の homotopy function complex と一般 homotopy 極限の不変性。
-/

@[expose] public section

noncomputable section

universe u v w

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory HomotopicalAlgebra
open SerrePositivity.Reedy SerrePositivity.HomotopyFunctionComplex

variable (A : Type u) [CommRing A]
  {D : Type w} [Category.{v} D] (L : SSet.{u} ⥤ D)
  (hL : SSet.anodyneExtensions.IsInvertedBy L)

include hL

/-- 概要：E 代数の終域の擬同型は Map^h で anodyne 反転後に同型（Hovey §5）。
方針：fibrant 置換の弱同値保存と frame Hom の終域不変性を使う。
規約：元の両終域や始域の cofibrancy・fibrancy を入力しない。
使われ方：導来写像空間の終域に関するホモトピー不変性。 -/
lemma mappingSpace_map_target_isIso (X : (operad A).Algebraᵒᵖ)
    {Y Z : (operad A).Algebra} (g : Y ⟶ Z) (hg : QuasiIso g.hom) :
    IsIso (L.map (((mappingSpace A).obj X).map g)) := by
  let := modelCategory A
  let q := cosimplicialResolutionFamily (mappingCofibrantFactorization A)
  let r := mappingFibrantFactorization A
  have := fibrantTarget_isFibrant r Y
  have := fibrantTarget_isFibrant r Z
  have : WeakEquivalence ((fibrantTarget r).map g) :=
    ⟨fibrantTarget_map_weakEquivalence r g hg⟩
  exact _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.target_weakEquivalence_isIso (q.obj.obj X.unop) (q.cofibrant X.unop)
    L hL ((fibrantTarget r).map g)

/-- 概要：E 代数の始域の擬同型は Map^h で anodyne 反転後に同型（Hovey §5）。
方針：関手的な余単体的分解の弱同値保存と frame Hom の始域不変性を使う。
規約：元の始域に cofibrancy を要求せず、反変な向きを保持する。
使われ方：導来写像空間の始域に関するホモトピー不変性。 -/
lemma mappingSpace_map_source_isIso {X X' : (operad A).Algebraᵒᵖ}
    (f : X ⟶ X') (hf : QuasiIso f.unop.hom) (Y : (operad A).Algebra) :
    IsIso (L.map (((mappingSpace A).map f).app Y)) := by
  let := modelCategory A
  let q := cosimplicialResolutionFamily (mappingCofibrantFactorization A)
  let r := mappingFibrantFactorization A
  have := fibrantTarget_isFibrant r Y
  exact _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.source_weakEquivalence_isIso L hL (q.obj.map f.unop)
    (q.cofibrant X'.unop) (q.cofibrant X.unop) (q.map_weakEquivalence f.unop hf)
    ((fibrantTarget r).obj Y)

/-- 概要：E 代数の両変数の擬同型は Map^h で同時に反転される（Hovey §5）。
方針：始域と終域の像の同型を合成する。
規約：実際の単体集合射の合成を値圏で評価する。
使われ方：導来写像空間の二変数のホモトピー不変性。 -/
lemma mappingSpace_map_both_isIso {X X' : (operad A).Algebraᵒᵖ}
    (f : X ⟶ X') (hf : QuasiIso f.unop.hom)
    {Y Y' : (operad A).Algebra} (g : Y ⟶ Y') (hg : QuasiIso g.hom) :
    IsIso (L.map (((mappingSpace A).map f).app Y ≫ ((mappingSpace A).obj X').map g)) := by
  have := mappingSpace_map_source_isIso A L hL f hf Y
  have := mappingSpace_map_target_isIso A L hL X' g hg
  rw [L.map_comp]
  infer_instance

end SerrePositivity.EInfinity.BarrattEccles
