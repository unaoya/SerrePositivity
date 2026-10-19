module

public import SerrePositivity.InfinityCategories.F1B.KanCommaTargetFold
public import SerrePositivity.InfinityCategories.F1B.UnitCommaFiberFamilies
public import SerrePositivity.InfinityCategories.F1B.UnitCommaArrowEndpoints

/-!
概要：固定始域の comma の fiber で、標的の辺を指定始点から持ち上げる。
方針：元の矢印と標的の辺の像を合成し、その三角形を始域固定の正方形へ移す。
規約：矢印の値域だけを quasicategory とし、標的添字の圏の充填性は不要。
使われ方：局所 Kan 添字の区間模型の left fibration 性の一次元の入力。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：固定始域の comma から標的の添字への射影。
方針：fiber の包含後に標的射影を取る。
規約：G の充填性は不要。
使われ方：区間模型の局所添字の left fibration の構造射。 -/
def kanUnitCommaFiberProjection {X Y : SSet.{u}} (G : Y ⟶ X) (x : X _⦋0⦌) :
    unitCommaFiber G x ⟶ Y := vertexFiberι (unitCommaSource G) x ≫ unitCommaTarget G

/-- 概要：固定始域の comma の標的の辺を、指定された始点から持ち上げられる。
方針：合成三角形を始域固定の正方形へ引き戻して comma に束ねる。
規約：X の quasicategory 性だけを要求する。
使われ方：射影の一次元の左ホーン持ち上げ。 -/
lemma exists_kanUnitCommaFiber_edge_lift {X Y : SSet.{u}} [Quasicategory X]
    (G : Y ⟶ X) (x : X _⦋0⦌) (v : (unitCommaFiber G x) _⦋0⦌)
    (b : (Δ[1] : SSet.{u}) ⟶ Y)
    (hb : stdSimplex.δ 1 ≫ b = SSet.yonedaEquiv.symm
      ((kanUnitCommaFiberProjection G x).app (Opposite.op ⦋0⦌) v)) :
    ∃ l : (Δ[1] : SSet.{u}) ⟶ unitCommaFiber G x,
      stdSimplex.δ 1 ≫ l = SSet.yonedaEquiv.symm v ∧ l ≫ kanUnitCommaFiberProjection G x = b := by
  have hs : Y.δ 1 (SSet.yonedaEquiv b) =
      (unitCommaTarget G).app (Opposite.op ⦋0⦌) v.val := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, hb, Equiv.apply_symm_apply]
    rfl
  let a : SSet.Truncated.Edge (X := (truncation 2).obj Y)
      ((unitCommaTarget G).app (Opposite.op ⦋0⦌) v.val) (Y.δ 0 (SSet.yonedaEquiv b)) :=
    ⟨SSet.yonedaEquiv b, hs, rfl⟩
  let t := SSet.Truncated.Edge.compStruct (unitCommaVertexEdge G v.val)
    (a.map ((truncation 2).map G))
  let T : (Δ[2] : SSet.{u}) ⟶ X := SSet.yonedaEquiv.symm t.simplex
  have hT₀ : stdSimplex.δ (0 : Fin 3) ≫ T = b ≫ G := by
    apply SSet.yonedaEquiv.injective
    dsimp only [T]
    rw [stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply]
    change _ = G.app (Opposite.op ⦋1⦌) (SSet.yonedaEquiv b)
    exact t.d₀
  have hT₂ : stdSimplex.δ (2 : Fin 3) ≫ T = unitCommaVertexArrow G v.val := by
    rw [← unitCommaVertexEdge_yoneda G v.val]
    apply SSet.yonedaEquiv.injective
    dsimp only [T]
    erw [stdSimplex.yonedaEquiv_δ_comp,
      SSet.yonedaEquiv.apply_symm_apply (t.simplex : X _⦋2⦌),
      SSet.yonedaEquiv.apply_symm_apply ((unitCommaVertexEdge G v.val).edge : X _⦋1⦌)]
    exact t.d₂
  have hfirst : T.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (0 : Fin 3)) = x := by
    have h := congrArg (fun q : (Δ[1] : SSet.{u}) ⟶ X ↦
      q.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) hT₂
    change T.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (0 : Fin 3)) =
      (unitCommaVertexArrow G v.val).app (Opposite.op ⦋0⦌)
        (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) at h
    rw [h]
    have hv := congrArg
      ((evaluateFunctorAt (Y := X) (stdSimplex.obj₀Equiv.symm (0 : Fin 2))).app
        (Opposite.op ⦋0⦌)) (unitCommaVertexArrow_functorVertex G v.val)
    rw [evaluateFunctorAt_functorVertex] at hv
    change _ = (unitCommaArrow G ≫ evaluateFunctorAt
      (stdSimplex.obj₀Equiv.symm (0 : Fin 2))).app (Opposite.op ⦋0⦌) v.val at hv
    rw [unitCommaArrow_evaluate_zero] at hv
    exact hv.trans (v.property.trans (pinchedConstant_zero x))
  let H : SSet.Homotopy (SSet.const x : (Δ[1] : SSet.{u}) ⟶ X) (b ≫ G) := {
    h := kanCommaTargetFold ≫ T
    h₀ := by rw [← Category.assoc, kanCommaTargetFold_source, SSet.const_comp, hfirst]; rfl
    h₁ := by rw [← Category.assoc, kanCommaTargetFold_target, hT₀]; rfl
    rel := by
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro z
      exact False.elim z.1.property }
  let f := unitCommaLift G (SSet.const x) b H
  let l := unitCommaFiberCurry G x b H
  have hfSource : f ≫ unitCommaSource G = SSet.const x := unitCommaLift_source _ _ _ _
  have hfTarget : f ≫ unitCommaTarget G = b := unitCommaLift_target _ _ _ _
  have hfArrow : f ≫ unitCommaArrow G =
      curry ((β_ (Δ[1] : SSet.{u}) Δ[1]).hom ≫ kanCommaTargetFold ≫ T) :=
    unitCommaLift_arrow _ _ _ _
  refine ⟨l, ?_, unitCommaFiberCurry_target G x b H⟩
  apply vertexFiber_hom_ext (unitCommaSource G) x
  rw [Category.assoc, unitCommaFiberCurry_ι]
  erw [SSet.yonedaEquiv_symm_comp v (vertexFiberι (unitCommaSource G) x)]
  change (stdSimplex.δ (1 : Fin 2) ≫ f) = SSet.yonedaEquiv.symm v.val
  apply pullback.hom_ext
  · change (stdSimplex.δ (1 : Fin 2) ≫ f) ≫ unitCommaArrow G =
      SSet.yonedaEquiv.symm v.val ≫ unitCommaArrow G
    rw [Category.assoc, hfArrow, SSet.yonedaEquiv_symm_comp]
    apply SSet.yonedaEquiv.injective
    rw [stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply]
    rw [← functorVertex_uncurry_zero, Equiv.symm_apply_apply, uncurry_curry]
    change functorVertex (prismEndpoint 0 Δ[1] ≫ kanCommaTargetFold ≫ T) = _
    rw [← Category.assoc, kanCommaTargetFold_start, hT₂, unitCommaVertexArrow_functorVertex]
  · apply CartesianMonoidalCategory.hom_ext
    · change (stdSimplex.δ (1 : Fin 2) ≫ f) ≫ unitCommaSource G =
        SSet.yonedaEquiv.symm v.val ≫ unitCommaSource G
      rw [Category.assoc, hfSource, SSet.comp_const, SSet.yonedaEquiv_symm_comp]
      rw [show (unitCommaSource G).app (Opposite.op ⦋0⦌) v.val = x from
        v.property.trans (pinchedConstant_zero x), SSet.yonedaEquiv_symm_zero]
    · change (stdSimplex.δ (1 : Fin 2) ≫ f) ≫ unitCommaTarget G =
        SSet.yonedaEquiv.symm v.val ≫ unitCommaTarget G
      rw [Category.assoc, hfTarget, hb, SSet.yonedaEquiv_symm_comp]
      rfl

end SerrePositivity.InfinityCategories.F1B
