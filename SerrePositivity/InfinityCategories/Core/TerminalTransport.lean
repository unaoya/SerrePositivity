module

public import SerrePositivity.InfinityCategories.Core.TerminalVertices
public import SerrePositivity.InfinityCategories.Core.HornPointJoin
public import SerrePositivity.InfinityCategories.Core.Limit

/-!
概要：終対象性のホモトピー圏の同型による不変性。
方針：終対象への境界上の錐を作り、可逆な最後の辺を持つ外側ホーンを充填する。
規約：同型は Mathlib のホモトピー圏の同型。
使われ方：HTT §1.2.12、Kerodon §4.7.3。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：終対象上の slice 射影に任意の図式を持ち上げられる。
方針：空部分複体からの単射に対する trivial Kan fibration の持ち上げを使う。
規約：図式の始域は任意の単体集合。
使われ方：HTT §1.2.12、Kerodon §4.7.3 の境界上の錐。 -/
lemma IsTerminalVertex.exists_sliceLift {A X : SSet.{u}} {x : X _⦋0⦌}
    (hx : IsTerminalVertex x) (b : A ⟶ X) :
    ∃ C : A ⟶ sliceOver (SSet.yonedaEquiv.symm x),
      C ≫ sliceOverProjection (SSet.yonedaEquiv.symm x) = b := by
  have := (isTerminalVertex_iff_trivialKanFibration x).1 hx
  have := TrivialKanFibration.mem (p := sliceOverProjection (SSet.yonedaEquiv.symm x))
    (⊥ : A.Subcomplex).ι inferInstance
  have sq : CommSq (Subcomplex.isInitialBot.to (sliceOver (SSet.yonedaEquiv.symm x)))
      (⊥ : A.Subcomplex).ι (sliceOverProjection (SSet.yonedaEquiv.symm x)) b :=
    ⟨Subcomplex.isInitialBot.hom_ext _ _⟩
  exact ⟨sq.lift, sq.fac_right⟩

/-- 概要：終対象が存在する場合、ホモトピー圏で終対象となる頂点は終対象。
方針：境界を既知の終対象へ錐にし、最後の辺が終対象間の同型である外側ホーンを充填する。
規約：quasicategory 性を仮定する。
使われ方：HTT §1.2.12、Kerodon §4.7.3 の同型不変性。 -/
lemma isTerminalVertex_of_isTerminalHo {X : SSet.{u}} [Quasicategory X]
    {x y : X _⦋0⦌} (hx : IsTerminalVertex x)
    (hy : IsTerminal (SSet.HomotopyCategory.mk y : hoFunctor.obj X)) : IsTerminalVertex y := by
  intro n b hb
  obtain ⟨C, hC⟩ := hx.exists_sliceLift b
  let G := sliceOverUncurry C
  let v := SSet.yonedaEquiv (boundaryVertex n (Fin.last (n + 1)))
  let t := C.app (Opposite.op ⦋0⦌) v
  have ht : (sliceOverProjection (SSet.yonedaEquiv.symm x)).app (Opposite.op ⦋0⦌) t = y := by
    change SSet.yonedaEquiv ((boundaryVertex n (Fin.last (n + 1)) ≫ C) ≫
      sliceOverProjection (SSet.yonedaEquiv.symm x)) = y
    rw [Category.assoc, hC, hb, Equiv.apply_symm_apply]
  let e := sliceOverVertexEdge x t
  have hs : IsTerminal (SSet.HomotopyCategory.mk
      ((sliceOverProjection (SSet.yonedaEquiv.symm x)).app (Opposite.op ⦋0⦌) t) :
        hoFunctor.obj X) := by rw [ht]; exact hy
  have he : IsInvertibleEdge e := isIso_of_isTerminal hs hx.isTerminalHo _
  let σ := (finalHornPointJoinIso (n + 1)).inv ≫ G
  have hσ : σ.app (Opposite.op ⦋1⦌) (finalHornEdge n) = e.edge := by
    rw [← finalHornPointJoinIso_edge, ← SSet.yonedaEquiv_comp]
    change SSet.yonedaEquiv (((joinStdSimplexIso 0 0).inv ≫
      joinMap (boundaryVertex n (Fin.last (n + 1))) (𝟙 Δ[0]) ≫
        (finalHornPointJoinIso (n + 1)).hom) ≫
          ((finalHornPointJoinIso (n + 1)).inv ≫ G)) = _
    rw [Category.assoc, Category.assoc, Iso.hom_inv_id_assoc]
    change SSet.yonedaEquiv ((joinStdSimplexIso 0 0).inv ≫
      (joinMap (boundaryVertex n (Fin.last (n + 1))) (𝟙 Δ[0]) ≫ sliceOverUncurry C)) = _
    rw [← sliceOverUncurry_precomp]
    rw [show boundaryVertex n (Fin.last (n + 1)) = SSet.yonedaEquiv.symm v from
      (SSet.yonedaEquiv.symm_apply_apply _).symm,
      SSet.yonedaEquiv_symm_comp,
      sliceOverUncurry_yoneda]
    rfl
  obtain ⟨F, hF⟩ := hasFinalHornFillers_of_isInvertibleEdge e he n σ hσ
  refine ⟨stdSimplex.map (PinchedHom.front (n + 1)) ≫ F, ?_⟩
  have hG : joinMap (boundary (n + 1)).ι (𝟙 Δ[0]) ≫
      (joinStdSimplexIso (n + 1) 0).hom ≫ F = G := by
    rw [← Category.assoc, ← finalHornPointJoinIso_hom_ι, Category.assoc, hF]
    exact (finalHornPointJoinIso (n + 1)).hom_inv_id_assoc G
  calc
    (boundary (n + 1)).ι ≫ stdSimplex.map (PinchedHom.front (n + 1)) ≫ F =
        joinInl (boundary (n + 1) : SSet.{u}) Δ[0] ≫ G := by
      rw [← hG]
      simp only [← Category.assoc]
      rw [joinInl_joinMap]
      simp only [Category.assoc]
      rw [← Category.assoc (joinInl _ _) (joinStdSimplexIso (n + 1) 0).hom,
        joinStdSimplexIso_rightPoint_inl]
    _ = b := by rw [sliceOverUncurry_projection, hC]

/-- 概要：終対象性はホモトピー圏の頂点の同型で保たれる。
方針：通常の終対象性を同型で移し、既知の終対象から境界の充填へ戻す。
規約：同型は h X で取る。
使われ方：HTT §1.2.12、Kerodon §4.7.3。 -/
lemma IsTerminalVertex.of_vertexIso {X : SSet.{u}} [Quasicategory X]
    {x y : X _⦋0⦌} (hx : IsTerminalVertex x) (e : VertexIso x y) : IsTerminalVertex y :=
  isTerminalVertex_of_isTerminalHo hx (hx.isTerminalHo.ofIso e)

/-- 概要：同型な二頂点の終対象性は同値。
方針：同型と逆同型で前の補題を適用する。
規約：X は quasicategory。
使われ方：HTT §1.2.12、Kerodon §4.7.3。 -/
lemma isTerminalVertex_iff_of_vertexIso {X : SSet.{u}} [Quasicategory X]
    {x y : X _⦋0⦌} (e : VertexIso x y) : IsTerminalVertex x ↔ IsTerminalVertex y :=
  ⟨fun h ↦ h.of_vertexIso e, fun h ↦ h.of_vertexIso e.symm⟩

/-- 概要：極限錐の性質は図式上の slice のホモトピー圏の同型で保たれる。
方針：slice の終対象性に同型不変性を適用する。
規約：周囲 X の頂点の同型だけではなく、錐全体の h(slice) での同型を仮定する。
使われ方：HTT §1.2.13、Kerodon §7.1 の極限錐。 -/
lemma IsLimitCone.of_vertexIso {K X : SSet.{u}} [Quasicategory X] {p : K ⟶ X}
    {c d : JoinCone p} (hc : IsLimitCone c) (e : VertexIso (X := sliceOver p) c d) :
    IsLimitCone d := IsTerminalVertex.of_vertexIso hc e

/-- 概要：図式上で同型な錐の極限性は同値。
方針：slice の終対象性の同値をそのまま使う。
規約：同型の場所は h(sliceOver p)。
使われ方：HTT §1.2.13、Kerodon §7.1 の極限錐。 -/
lemma isLimitCone_iff_of_vertexIso {K X : SSet.{u}} [Quasicategory X] {p : K ⟶ X}
    {c d : JoinCone p} (e : VertexIso (X := sliceOver p) c d) : IsLimitCone c ↔ IsLimitCone d :=
  isTerminalVertex_iff_of_vertexIso e

end SerrePositivity.InfinityCategories
