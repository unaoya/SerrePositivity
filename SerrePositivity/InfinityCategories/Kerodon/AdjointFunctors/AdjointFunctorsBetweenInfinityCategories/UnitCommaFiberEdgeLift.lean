module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.CommaTargetFold
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitCommaFiberFamilies
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitCommaArrowEndpoints

/-!
概要：固定始域の comma の fiber で、標的の辺を指定始点から持ち上げる。
方針：元の矢印と標的の辺の像を合成し、その三角形を始域固定の正方形へ移す。
規約：矢印の値域だけを quasicategory とし、標的添字の圏の充填性は不要。
使われ方：局所 Kan 添字の区間模型の left fibration 性の一次元の入力。

対応節は Kerodon 6.2（Tag 02EH）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories

/-- 概要：固定始域の comma から標的の添字への射影。
方針：fiber の包含後に標的射影を取る。
規約：G の充填性は不要。
使われ方：区間模型の局所添字の left fibration の構造射。 -/
def unitCommaFiberProjection {X Y : SSet.{u}} (G : Y ⟶ X) (x : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber G x ⟶ Y := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSource G) x ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaTarget G

/-- 概要：固定始域の comma の標的の辺を、指定された始点から持ち上げられる。
方針：合成三角形を始域固定の正方形へ引き戻して comma に束ねる。
規約：X の quasicategory 性だけを要求する。
使われ方：射影の一次元の左ホーン持ち上げ。 -/
lemma exists_kanUnitCommaFiber_edge_lift {X Y : SSet.{u}} [Quasicategory X]
    (G : Y ⟶ X) (x : X _⦋0⦌) (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber G x) _⦋0⦌)
    (b : (Δ[1] : SSet.{u}) ⟶ Y)
    (hb : stdSimplex.δ 1 ≫ b = SSet.yonedaEquiv.symm
      ((unitCommaFiberProjection G x).app (Opposite.op ⦋0⦌) v)) :
    ∃ l : (Δ[1] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber G x,
      stdSimplex.δ 1 ≫ l = SSet.yonedaEquiv.symm v ∧ l ≫ unitCommaFiberProjection G x = b := by
  have hs : Y.δ 1 (SSet.yonedaEquiv b) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaTarget G).app (Opposite.op ⦋0⦌) v.val := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, hb, Equiv.apply_symm_apply]
    rfl
  let a : SSet.Truncated.Edge (X := (truncation 2).obj Y)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaTarget G).app (Opposite.op ⦋0⦌) v.val) (Y.δ 0 (SSet.yonedaEquiv b)) :=
    ⟨SSet.yonedaEquiv b, hs, rfl⟩
  let t := SSet.Truncated.Edge.compStruct (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaVertexEdge G v.val)
    (a.map ((truncation 2).map G))
  let T : (Δ[2] : SSet.{u}) ⟶ X := SSet.yonedaEquiv.symm t.simplex
  have hT₀ : stdSimplex.δ (0 : Fin 3) ≫ T = b ≫ G := by
    apply SSet.yonedaEquiv.injective
    dsimp only [T]
    rw [stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply]
    change _ = G.app (Opposite.op ⦋1⦌) (SSet.yonedaEquiv b)
    exact t.d₀
  have hT₂ : stdSimplex.δ (2 : Fin 3) ≫ T = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaVertexArrow G v.val := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaVertexEdge_yoneda G v.val]
    apply SSet.yonedaEquiv.injective
    dsimp only [T]
    erw [stdSimplex.yonedaEquiv_δ_comp,
      SSet.yonedaEquiv.apply_symm_apply (t.simplex : X _⦋2⦌),
      SSet.yonedaEquiv.apply_symm_apply ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaVertexEdge G v.val).edge : X _⦋1⦌)]
    exact t.d₂
  have hfirst : T.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (0 : Fin 3)) = x := by
    have h := congrArg (fun q : (Δ[1] : SSet.{u}) ⟶ X ↦
      q.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) hT₂
    change T.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (0 : Fin 3)) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaVertexArrow G v.val).app (Opposite.op ⦋0⦌)
        (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) at h
    rw [h]
    have hv := congrArg
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) (stdSimplex.obj₀Equiv.symm (0 : Fin 2))).app
        (Opposite.op ⦋0⦌)) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaVertexArrow_functorVertex G v.val)
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex] at hv
    change _ = (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaArrow G ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
      (stdSimplex.obj₀Equiv.symm (0 : Fin 2))).app (Opposite.op ⦋0⦌) v.val at hv
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaArrow_evaluate_zero] at hv
    exact hv.trans (v.property.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero x))
  let H : SSet.Homotopy (SSet.const x : (Δ[1] : SSet.{u}) ⟶ X) (b ≫ G) := {
    h := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanCommaTargetFold ≫ T
    h₀ := by rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanCommaTargetFold_source, SSet.const_comp, hfirst]; rfl
    h₁ := by rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanCommaTargetFold_target, hT₀]; rfl
    rel := by
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro z
      exact False.elim z.1.property }
  let f := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaLift G (SSet.const x) b H
  let l := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberCurry G x b H
  have hfSource : f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSource G = SSet.const x := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaLift_source _ _ _ _
  have hfTarget : f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaTarget G = b := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaLift_target _ _ _ _
  have hfArrow : f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaArrow G =
      curry ((β_ (Δ[1] : SSet.{u}) Δ[1]).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanCommaTargetFold ≫ T) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaLift_arrow _ _ _ _
  refine ⟨l, ?_, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberCurry_target G x b H⟩
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSource G) x
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberCurry_ι]
  erw [SSet.yonedaEquiv_symm_comp v (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSource G) x)]
  change (stdSimplex.δ (1 : Fin 2) ≫ f) = SSet.yonedaEquiv.symm v.val
  apply pullback.hom_ext
  · change (stdSimplex.δ (1 : Fin 2) ≫ f) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaArrow G =
      SSet.yonedaEquiv.symm v.val ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaArrow G
    rw [Category.assoc, hfArrow, SSet.yonedaEquiv_symm_comp]
    apply SSet.yonedaEquiv.injective
    rw [stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply]
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_uncurry_zero, Equiv.symm_apply_apply, uncurry_curry]
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 Δ[1] ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanCommaTargetFold ≫ T) = _
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanCommaTargetFold_start, hT₂, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaVertexArrow_functorVertex]
  · apply CartesianMonoidalCategory.hom_ext
    · change (stdSimplex.δ (1 : Fin 2) ≫ f) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSource G =
        SSet.yonedaEquiv.symm v.val ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSource G
      rw [Category.assoc, hfSource, SSet.comp_const, SSet.yonedaEquiv_symm_comp]
      rw [show (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSource G).app (Opposite.op ⦋0⦌) v.val = x from
        v.property.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero x), SSet.yonedaEquiv_symm_zero]
    · change (stdSimplex.δ (1 : Fin 2) ≫ f) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaTarget G =
        SSet.yonedaEquiv.symm v.val ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaTarget G
      rw [Category.assoc, hfTarget, hb, SSet.yonedaEquiv_symm_comp]
      rfl

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories
