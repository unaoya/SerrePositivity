module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TerminalVertices
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.HornPointJoin
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoreLimit
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：終対象性のホモトピー圏の同型による不変性。
方針：終対象への境界上の錐を作り、可逆な最後の辺を持つ外側ホーンを充填する。
規約：同型は Mathlib のホモトピー圏の同型。
使われ方：HTT §1.2.12、Kerodon §4.7.3（Tag 02H6）。

対応節は Kerodon 4.7（Tag 05EA）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories

/-- 概要：終対象上の slice 射影に任意の図式を持ち上げられる。
方針：空部分複体からの単射に対する trivial Kan fibration の持ち上げを使う。
規約：図式の始域は任意の単体集合。
使われ方：HTT §1.2.12、Kerodon §4.7.3（Tag 02H6） の境界上の錐。 -/
lemma IsTerminalVertex.exists_sliceLift {A X : SSet.{u}} {x : X _⦋0⦌}
    (hx : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex x) (b : A ⟶ X) :
    ∃ C : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (SSet.yonedaEquiv.symm x),
      C ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm x) = b := by
  have := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.isTerminalVertex_iff_trivialKanFibration x).1 hx
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm x))
    (⊥ : A.Subcomplex).ι inferInstance
  have sq : CommSq (Subcomplex.isInitialBot.to (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (SSet.yonedaEquiv.symm x)))
      (⊥ : A.Subcomplex).ι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm x)) b :=
    ⟨Subcomplex.isInitialBot.hom_ext _ _⟩
  exact ⟨sq.lift, sq.fac_right⟩

/-- 概要：終対象が存在する場合、ホモトピー圏で終対象となる頂点は終対象。
方針：境界を既知の終対象へ錐にし、最後の辺が終対象間の同型である外側ホーンを充填する。
規約：quasicategory 性を仮定する。
使われ方：HTT §1.2.12、Kerodon §4.7.3（Tag 02H6） の同型不変性。 -/
@[kerodon 02HQ]
lemma isTerminalVertex_of_isTerminalHo {X : SSet.{u}} [Quasicategory X]
    {x y : X _⦋0⦌} (hx : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex x)
    (hy : IsTerminal (SSet.HomotopyCategory.mk y : hoFunctor.obj X)) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex y := by
  intro n b hb
  obtain ⟨C, hC⟩ := hx.exists_sliceLift b
  let G := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry C
  let v := SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n (Fin.last (n + 1)))
  let t := C.app (Opposite.op ⦋0⦌) v
  have ht : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm x)).app (Opposite.op ⦋0⦌) t = y := by
    change SSet.yonedaEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n (Fin.last (n + 1)) ≫ C) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm x)) = y
    rw [Category.assoc, hC, hb, Equiv.apply_symm_apply]
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceOverVertexEdge x t
  have hs : IsTerminal (SSet.HomotopyCategory.mk
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm x)).app (Opposite.op ⦋0⦌) t) :
        hoFunctor.obj X) := by rw [ht]; exact hy
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge e := isIso_of_isTerminal hs hx.isTerminalHo _
  let σ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.finalHornPointJoinIso (n + 1)).inv ≫ G
  have hσ : σ.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.finalHornEdge n) = e.edge := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.finalHornPointJoinIso_edge, ← SSet.yonedaEquiv_comp]
    change SSet.yonedaEquiv (((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n (Fin.last (n + 1))) (𝟙 Δ[0]) ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.finalHornPointJoinIso (n + 1)).hom) ≫
          ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.finalHornPointJoinIso (n + 1)).inv ≫ G)) = _
    rw [Category.assoc, Category.assoc, Iso.hom_inv_id_assoc]
    change SSet.yonedaEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n (Fin.last (n + 1))) (𝟙 Δ[0]) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry C)) = _
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_precomp]
    rw [show _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n (Fin.last (n + 1)) = SSet.yonedaEquiv.symm v from
      (SSet.yonedaEquiv.symm_apply_apply _).symm,
      SSet.yonedaEquiv_symm_comp,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceOverUncurry_yoneda]
    rfl
  obtain ⟨F, hF⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.hasFinalHornFillers_of_isInvertibleEdge e he n σ hσ
  refine ⟨stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.front (n + 1)) ≫ F, ?_⟩
  have hG : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (boundary (n + 1)).ι (𝟙 Δ[0]) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso (n + 1) 0).hom ≫ F = G := by
    rw [← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.finalHornPointJoinIso_hom_ι, Category.assoc, hF]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.finalHornPointJoinIso (n + 1)).hom_inv_id_assoc G
  calc
    (boundary (n + 1)).ι ≫ stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.front (n + 1)) ≫ F =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (boundary (n + 1) : SSet.{u}) Δ[0] ≫ G := by
      rw [← hG]
      simp only [← Category.assoc]
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap]
      simp only [Category.assoc]
      rw [← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl _ _) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso (n + 1) 0).hom,
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinStdSimplexIso_rightPoint_inl]
    _ = b := by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.sliceOverUncurry_projection, hC]

/-- 概要：終対象性はホモトピー圏の頂点の同型で保たれる。
方針：通常の終対象性を同型で移し、既知の終対象から境界の充填へ戻す。
規約：同型は h X で取る。
使われ方：HTT §1.2.12、Kerodon §4.7.3（Tag 02H6）。 -/
lemma IsTerminalVertex.of_vertexIso {X : SSet.{u}} [Quasicategory X]
    {x y : X _⦋0⦌} (hx : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex x) (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso x y) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex y :=
  isTerminalVertex_of_isTerminalHo hx (hx.isTerminalHo.ofIso e)

/-- 概要：同型な二頂点の終対象性は同値。
方針：同型と逆同型で前の補題を適用する。
規約：X は quasicategory。
使われ方：HTT §1.2.12、Kerodon §4.7.3（Tag 02H6）。 -/
lemma isTerminalVertex_iff_of_vertexIso {X : SSet.{u}} [Quasicategory X]
    {x y : X _⦋0⦌} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso x y) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex x ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex y :=
  ⟨fun h ↦ h.of_vertexIso e, fun h ↦ h.of_vertexIso e.symm⟩

/-- 概要：極限錐の性質は図式上の slice のホモトピー圏の同型で保たれる。
方針：slice の終対象性に同型不変性を適用する。
規約：周囲 X の頂点の同型だけではなく、錐全体の h(slice) での同型を仮定する。
使われ方：HTT §1.2.13、Kerodon §7.1（Tag 02H1） の極限錐。 -/
lemma IsLimitCone.of_vertexIso {K X : SSet.{u}} [Quasicategory X] {p : K ⟶ X}
    {c d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p} (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c) (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p) c d) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone d := IsTerminalVertex.of_vertexIso hc e

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone export _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsLimitCone (of_vertexIso)


/-- 概要：図式上で同型な錐の極限性は同値。
方針：slice の終対象性の同値をそのまま使う。
規約：同型の場所は h(sliceOver p)。
使われ方：HTT §1.2.13、Kerodon §7.1（Tag 02H1） の極限錐。 -/
lemma isLimitCone_iff_of_vertexIso {K X : SSet.{u}} [Quasicategory X] {p : K ⟶ X}
    {c d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p) c d) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone d :=
  isTerminalVertex_iff_of_vertexIso e

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
