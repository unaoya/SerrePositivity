module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TerminalUniqueness
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ColimitCoconeRestriction
public import Mathlib.AlgebraicTopology.SimplicialSet.CompStruct

/-!
概要：実際の合成二単体を、最初の辺の指定余錐として読む。
方針：辺と点の join の標準三角形同型で表示する。
規約：元の二単体・二辺・合成辺を全て保持する。
使われ方：coslice 内の分裂三角形から全交互図式の次の余錐を作る。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
variable {X : SSet.{u}} {x y z : X _⦋0⦌}
  {e : X.Edge x y} {r : X.Edge y z} {f : X.Edge x z}

/-- 概要：元の合成三角形は、最初の辺から終頂点への余錐。
方針：Δ¹⋆Δ⁰ と Δ² の同型を使う。
規約：元の三角形の単体値をそのまま使う。
使われ方：反復 coslice による交互図式の余錐の拡張。 -/
def compStructCocone (T : e.CompStruct r f) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (SSet.yonedaEquiv.symm e.edge) :=
  ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 1 0).hom ≫ SSet.yonedaEquiv.symm T.simplex, by
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.joinStdSimplexIso_one_inl,
      SSet.stdSimplex.δ_comp_yonedaEquiv_symm, T.d₂]⟩

/-- 概要：三角形余錐の始点側の全制限は元の合成辺そのもの。
方針：右端の対角面 δ₁ を計算する。
規約：全余錐値の厳密な等式。
使われ方：元の増大余錐を保持する。 -/
lemma compStructCocone_source_val (T : e.CompStruct r f) :
    ((compStructCocone T).restrict (SSet.stdSimplex.δ (1 : Fin 2))).val =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.edgeCosliceVertex f.toTruncated).val := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (SSet.stdSimplex.δ (1 : Fin 2)) (𝟙 Δ[0]) ≫
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 1 0).hom ≫ SSet.yonedaEquiv.symm T.simplex) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom ≫ SSet.yonedaEquiv.symm f.edge
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.joinStdSimplexIso_one_vertex, Category.assoc,
    SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom ≫ SSet.yonedaEquiv.symm (X.δ 1 T.simplex) = _
  rw [T.d₁]

/-- 概要：三角形余錐の終点側の全制限は元の第二辺そのもの。
方針：右端の辺の面 δ₀ を計算する。
規約：全余錐値の厳密な等式。
使われ方：新しい表示段からの元の増大辺を保持する。 -/
lemma compStructCocone_target_val (T : e.CompStruct r f) :
    ((compStructCocone T).restrict (SSet.stdSimplex.δ (0 : Fin 2))).val =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.edgeCosliceVertex r.toTruncated).val := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (SSet.stdSimplex.δ (0 : Fin 2)) (𝟙 Δ[0]) ≫
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 1 0).hom ≫ SSet.yonedaEquiv.symm T.simplex) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom ≫ SSet.yonedaEquiv.symm r.edge
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.joinStdSimplexIso_one_vertex, Category.assoc,
    SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom ≫ SSet.yonedaEquiv.symm (X.δ 0 T.simplex) = _
  rw [T.d₀]

/-- 概要：三角形余錐の頂点は元の第二辺の終点。
方針：標準三角形の最後の頂点を二つの δ₀ として読む。
規約：元の頂点を厳密に回収する。
使われ方：反復 coslice で得る余錐の頂点の同定。 -/
lemma compStructCocone_vertex (T : e.CompStruct r f) : (compStructCocone T).vertex = z := by
  have hshape : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[1] : SSet.{u}) Δ[0] ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 1 0).hom =
      SSet.stdSimplex.δ (0 : Fin 2) ≫ SSet.stdSimplex.δ (0 : Fin 3) := by
    apply SSet.yonedaEquiv.injective
    decide
  change SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[1] Δ[0] ≫
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 1 0).hom ≫ SSet.yonedaEquiv.symm T.simplex)) = z
  rw [← Category.assoc, hshape, Category.assoc,
    SSet.stdSimplex.yonedaEquiv_δ_comp, SSet.stdSimplex.yonedaEquiv_δ_comp,
    Equiv.apply_symm_apply, T.d₀, r.tgt_eq]

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
