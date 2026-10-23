module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.PointedReverseCompositionPrismCoordinates
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.PointedOppositeMorphismValueVertex

/-!
概要：元の固定 Kan 射で、F1 の同じ全反転合成 prism を全一点 Hom 係数へ制限する。
方針：係数の交換同型を保持して、元の合成単体の実座標を計算する。
規約：元の射・実 prism・全係数を保持。使われ方：元の pointed prism との直接照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
variable {K L : KanObject.{u}} (f : K ⟶ L)

/-- 元の射を固定し全一点 Hom だけを動かす、元の F1 の同じ反転合成 prism。 -/
def pointedReverseMorphismPrism :
    (Δ[1] : SSet.{u + 1}) ⊗ (SSet.uliftFunctor.{u + 1, u}).obj
      (SimplicialCategory.sHom pointKanObject K).op ⟶ PointedSpaceInfinity.{u} :=
  (Δ[1] ◁ lift (uliftOppositeIso (SimplicialCategory.sHom pointKanObject K)).hom
    (SSet.const (ULift.up (SSet.opObjEquiv.symm (functorVertex f))) ≫
      (uliftOppositeIso (SimplicialCategory.sHom K L)).hom)) ≫
        (pointedReverseKanCompositionTransportFamily K L).prism

/-- 元の固定射に沿う反転合成 prism の全単体座標は、同じ元の合成単体の反転。 -/
lemma pointedReverseMorphismPrism_coordinates {n : ℕ}
    (t : (Δ[1] : SSet.{u + 1}) _⦋n⦌)
    (p : (SimplicialCategory.sHom pointKanObject K).op _⦋n⦌) :
    SSet.yonedaEquiv ((leftPointStdSimplexIso n).inv ≫
      ((pointedReverseMorphismPrism f).app (Opposite.op ⦋n⦌) (t, ULift.up p)).val) =
    coherentOppositeInverseSimplex
      (coherentCompositionSimplex (X := Opposite.op L) (Y := Opposite.op K)
        (Z := Opposite.op pointKanObject) (PinchedHom.constant (functorVertex f) n)
        (SSet.opObjEquiv p) (stableReverseOrderHom (stdSimplex.objEquiv t).toOrderHom)) := by
  change SSet.yonedaEquiv ((leftPointStdSimplexIso n).inv ≫
    (((pointedReverseKanCompositionTransportFamily K L).prism).app (Opposite.op ⦋n⦌)
      (t, (uliftOppositeIso (SimplicialCategory.sHom pointKanObject K)).hom.app
        (Opposite.op ⦋n⦌) (ULift.up p),
      (uliftOppositeIso (SimplicialCategory.sHom K L)).hom.app (Opposite.op ⦋n⦌)
        ((SSet.const (ULift.up (SSet.opObjEquiv.symm (functorVertex f))) :
          (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom pointKanObject K).op ⟶
            (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom K L).op).app
            (Opposite.op ⦋n⦌) (ULift.up p)))).val) = _
  rw [pointedReverseKanCompositionPrism_coordinates]
  rfl

end SerrePositivity.InfinityCategories.F2
