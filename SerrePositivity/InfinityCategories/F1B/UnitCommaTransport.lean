module

public import SerrePositivity.InfinityCategories.F1B.UnitCommaArrowEndpoints
public import SerrePositivity.InfinityCategories.F1B.UnitCommaCartesianEdge
public import SerrePositivity.InfinityCategories.F1B.CommaTransportFold

/-!
概要：comma の始域の辺を、指定した終点と固定した標的で持ち上げる。
方針：始域の辺と終点の矢印を合成する三角形を、標的固定の正方形にする。
規約：指定した終点と基底の辺を厳密に保つ。
使われ方：B1 の始域射影の反転した cocartesian 輸送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：指定終点の始域へ入る辺には標的を固定した cartesian lift が存在する。
方針：合成三角形を標的固定の正方形へ畳み込み、comma の引き戻しへ持ち上げる。
規約：終点と基底の辺は元の指定そのもの。
使われ方：単位の fiber の始対象性を相対始対象性へ移す輸送。 -/
lemma exists_cartesian_unitComma_lift {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (G : Y ⟶ X)
    (v : (unitComma G) _⦋0⦌) (b : X _⦋0⦌)
    (a : SSet.Truncated.Edge (X := (truncation 2).obj X) b
      ((unitCommaSource G).app (Opposite.op ⦋0⦌) v)) :
    ∃ (w : (unitComma G) _⦋0⦌)
      (e : SSet.Truncated.Edge (X := (truncation 2).obj (unitComma G)) w v),
      (unitCommaSource G).app (Opposite.op ⦋1⦌) e.edge = a.edge ∧
        IsCartesianEdge (unitCommaSource G) e.edge := by
  let t := SSet.Truncated.Edge.compStruct a (unitCommaVertexEdge G v)
  let T : (Δ[2] : SSet.{u}) ⟶ X := SSet.yonedaEquiv.symm t.simplex
  have hT₀ : stdSimplex.δ (0 : Fin 3) ≫ T = unitCommaVertexArrow G v := by
    rw [← unitCommaVertexEdge_yoneda G v]
    apply SSet.yonedaEquiv.injective
    dsimp only [T]
    erw [stdSimplex.yonedaEquiv_δ_comp,
      SSet.yonedaEquiv.apply_symm_apply (t.simplex : X _⦋2⦌),
      SSet.yonedaEquiv.apply_symm_apply ((unitCommaVertexEdge G v).edge : X _⦋1⦌)]
    exact t.d₀
  have hT₂ : stdSimplex.δ (2 : Fin 3) ≫ T = SSet.yonedaEquiv.symm a.edge := by
    apply SSet.yonedaEquiv.injective
    dsimp only [T]
    erw [stdSimplex.yonedaEquiv_δ_comp,
      SSet.yonedaEquiv.apply_symm_apply (t.simplex : X _⦋2⦌),
      SSet.yonedaEquiv.apply_symm_apply (a.edge : X _⦋1⦌)]
    exact t.d₂
  let y := (unitCommaTarget G).app (Opposite.op ⦋0⦌) v
  have hlast : T.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (2 : Fin 3)) =
      G.app (Opposite.op ⦋0⦌) y := by
    have h := congrArg (fun q : (Δ[1] : SSet.{u}) ⟶ X ↦
      q.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) hT₀
    change T.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (2 : Fin 3)) =
      (unitCommaVertexArrow G v).app (Opposite.op ⦋0⦌)
        (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) at h
    rw [h]
    have hv := congrArg
      ((evaluateFunctorAt (Y := X) (stdSimplex.obj₀Equiv.symm (1 : Fin 2))).app
        (Opposite.op ⦋0⦌)) (unitCommaVertexArrow_functorVertex G v)
    rw [evaluateFunctorAt_functorVertex] at hv
    exact hv.trans (ConcreteCategory.congr_hom
      (NatTrans.congr_app (unitCommaArrow_evaluate_one G) (Opposite.op ⦋0⦌)) v)
  let l := curry (commaTransportFold ≫ T)
  have hl₀ : prismEndpoint 0 (Δ[1] : SSet.{u}) ≫ uncurry l =
      SSet.yonedaEquiv.symm a.edge := by
    rw [uncurry_curry, ← Category.assoc, commaTransportFold_source, hT₂]
  have hl₁ : prismEndpoint 1 (Δ[1] : SSet.{u}) ≫ uncurry l = SSet.const (G.app _ y) := by
    rw [uncurry_curry, ← Category.assoc, commaTransportFold_target, SSet.const_comp, hlast]
  have hp : l ≫ (pre (boundary 1).ι).app X =
      lift (SSet.yonedaEquiv.symm a.edge) (SSet.const y) ≫ unitCommaBoundary G := by
    apply uncurry_injective
    rw [uncurry_pre_app, intervalBoundaryDiagram_restrict, hl₀, hl₁]
    simp only [unitCommaBoundary, uncurry_natural_left, uncurry_curry,
      intervalBoundaryDiagram_naturality, lift_fst]
    rw [← Category.assoc, lift_snd, SSet.const_comp]
  let f : (Δ[1] : SSet.{u}) ⟶ unitComma G :=
    pullback.lift l (lift (SSet.yonedaEquiv.symm a.edge) (SSet.const y)) hp
  have hfSource : f ≫ unitCommaSource G = SSet.yonedaEquiv.symm a.edge := by
    simp only [f, unitCommaSource, unitCommaPair, pullback.lift_snd_assoc, lift_fst]
    rfl
  have hfTarget : f ≫ unitCommaTarget G = SSet.const y := by
    simp only [f, unitCommaTarget, unitCommaPair, pullback.lift_snd_assoc, lift_snd]
  have hfArrow : f ≫ unitCommaArrow G = l := pullback.lift_fst _ _ _
  let s := SSet.yonedaEquiv f
  have hsend : (unitComma G).δ 0 s = v := by
    apply SSet.yonedaEquiv.symm.injective
    change SSet.yonedaEquiv.symm ((unitComma G).δ 0 (SSet.yonedaEquiv f)) = _
    rw [← stdSimplex.yonedaEquiv_δ_comp, Equiv.symm_apply_apply]
    apply pullback.hom_ext
    · change (stdSimplex.δ (0 : Fin 2) ≫ f) ≫ unitCommaArrow G =
        SSet.yonedaEquiv.symm v ≫ unitCommaArrow G
      rw [Category.assoc, hfArrow, SSet.yonedaEquiv_symm_comp]
      apply SSet.yonedaEquiv.injective
      rw [stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply]
      rw [← functorVertex_uncurry_one, Equiv.symm_apply_apply]
      change functorVertex (SSet.ι₁ ≫ uncurry (curry (commaTransportFold ≫ T))) = _
      rw [uncurry_curry, ← Category.assoc,
        commaTransportFold_end, hT₀, unitCommaVertexArrow_functorVertex]
    · apply CartesianMonoidalCategory.hom_ext
      · change (stdSimplex.δ (0 : Fin 2) ≫ f) ≫ unitCommaSource G =
          SSet.yonedaEquiv.symm v ≫ unitCommaSource G
        rw [Category.assoc, hfSource, SSet.yonedaEquiv_symm_comp]
        apply SSet.yonedaEquiv.injective
        erw [stdSimplex.yonedaEquiv_δ_comp,
          SSet.yonedaEquiv.apply_symm_apply (a.edge : X _⦋1⦌), Equiv.apply_symm_apply]
        exact a.tgt_eq
      · change (stdSimplex.δ (0 : Fin 2) ≫ f) ≫ unitCommaTarget G =
          SSet.yonedaEquiv.symm v ≫ unitCommaTarget G
        rw [Category.assoc, hfTarget, SSet.comp_const, SSet.yonedaEquiv_symm_comp,
          SSet.yonedaEquiv_symm_zero]
  let e : SSet.Truncated.Edge (X := (truncation 2).obj (unitComma G))
      ((unitComma G).δ 1 s) v := ⟨s, rfl, hsend⟩
  refine ⟨_, e, ?_, isCartesianEdge_unitCommaSource_of_target G e ?_⟩
  · change (unitCommaSource G).app (Opposite.op ⦋1⦌) (SSet.yonedaEquiv f) = a.edge
    rw [← SSet.yonedaEquiv_comp, hfSource]
    exact SSet.yonedaEquiv.apply_symm_apply (a.edge : X _⦋1⦌)
  · have heq : (e.map ((truncation 2).map (unitCommaTarget G))).edge =
        PinchedHom.constant y 1 := by
      change (unitCommaTarget G).app (Opposite.op ⦋1⦌) (SSet.yonedaEquiv f) = _
      rw [← SSet.yonedaEquiv_comp, hfTarget]
      rfl
    have hi := isEquivalencePathVertex_const y
    unfold IsEquivalencePathVertex at hi
    rw [intervalFunctorVertexEdge_functorVertex] at hi
    exact (isInvertibleEdge_congr heq).2 hi

end SerrePositivity.InfinityCategories
