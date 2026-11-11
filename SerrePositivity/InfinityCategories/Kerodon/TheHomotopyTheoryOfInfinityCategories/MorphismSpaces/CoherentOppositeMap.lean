module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentReverseThickening

/-!
概要：coherent nerve の反転から反対の単体的圏の coherent nerve への標準射。
方針：標準 thickening の頂点と path を反転し、豊穣関手の反対を前合成する。
規約：単体の添字は SimplexCategory.rev で反転し、対象の反対とは区別する。
使われ方：Kerodon §4.6.7（Tag 01LA） の右 Hom と左 coslice の係数の向きの接続。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：coherent simplex の頂点順序を反転して反対の単体的圏の simplex にする。
方針：標準 thickening の反対への関手と豊穣関手の反対を合成する。
規約：C の対象の宇宙と Hom の宇宙は異なってよい。
使われ方：Kerodon §4.6.7（Tag 01LA） の coherent nerve の反対の標準射の各次数。 -/
def coherentOppositeSimplex {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {n : ℕ} (F : (SimplicialNerve C) _⦋n⦌) : (SimplicialNerve Cᵒᵖ) _⦋n⦌ :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentReverseThickening n).comp SSet (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentEnrichedFunctorOp F)

/-- 概要：coherent simplex の反対は反転した単体の添字による制限と可換。
方針：豊穣関手の反対の合成則と、thickening の頂点反転の自然性を使う。
規約：全ての面と退化を同時に扱う。
使われ方：Kerodon §4.6.7（Tag 01LA） の反対の標準射の単体的自然性。 -/
lemma coherentOppositeSimplex_naturality {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌)
    (F : (SimplicialNerve C) _⦋n⦌) :
    coherentOppositeSimplex
      ((SimplicialNerve C).map (SimplexCategory.rev.map α).op F) =
      (SimplicialNerve Cᵒᵖ).map α.op (coherentOppositeSimplex F) := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentReverseThickening m).comp SSet
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentEnrichedFunctorOp
      ((SimplicialThickening.functor (SimplexCategory.rev.map α).toOrderHom.uliftMap).comp
        SSet F)) =
    (SimplicialThickening.functor α.toOrderHom.uliftMap).comp SSet
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentReverseThickening n).comp SSet (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentEnrichedFunctorOp F))
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentEnrichedFunctorOp_comp, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentEnrichedFunctor_comp_assoc,
    ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentReverseThickening_naturality, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentEnrichedFunctor_comp_assoc]

/-- 概要：coherent nerve の単体的な反転は反対の単体的圏の coherent nerve へ標準的に写る。
方針：各次数で coherent simplex を反転し、その自然性を使う。
規約：Kan 性や quasicategory 性は射の定義に要求しない。
使われ方：Kerodon §4.6.7（Tag 01LA）、HTT 4.2.4.1 の左側の係数模型の比較の準備。 -/
def coherentNerveOppositeMap (C : Type v) [Category.{u} C] [SimplicialCategory C] :
    (SimplicialNerve C).op ⟶ SimplicialNerve Cᵒᵖ where
  app _ := ↾fun F ↦ coherentOppositeSimplex (SSet.opObjEquiv F)
  naturality d e α := by
    obtain ⟨⟨n⟩⟩ := d
    obtain ⟨⟨m⟩⟩ := e
    apply ConcreteCategory.hom_ext
    intro F
    exact coherentOppositeSimplex_naturality α.unop (SSet.opObjEquiv F)

/-- 概要：coherent nerve の反対の標準射は元の対象を反対圏の同じ対象へ写す。
方針：零単体を対象で検出する同値を使い、頂点の反転を計算する。
規約：頂点の像は同型類でなく厳密な等式である。
使われ方：Kerodon §4.6.7（Tag 01LA） の反対の Hom の二端点の同定。 -/
lemma coherentNerveOppositeMap_vertex {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (x : C) :
    (coherentNerveOppositeMap C).app (Opposite.op ⦋0⦌)
      (SSet.opObjEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex x)) = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (Opposite.op x) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertexEquiv Cᵒᵖ).symm.injective
  rfl

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
