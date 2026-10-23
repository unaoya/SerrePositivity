module

public import SerrePositivity.InfinityCategories.HomotopyLimits.FiberSquareTransportDetection
public import SerrePositivity.InfinityCategories.HomotopyLimits.LeftFibrationConeRestriction
public import SerrePositivity.InfinityCategories.HomotopyLimits.ConeApexEvaluation
public import SerrePositivity.InfinityCategories.F1.Fibrations.LeftFibrationInternalHom
public import SerrePositivity.InfinityCategories.F1.Transport.InvertibleLeftTransport

/-!
概要：全錐の底制限・頂点評価の正方形の fiber 射を、元の切断作用と照合する。
方針：元の内部 Hom の自然性の正方形を使い、元の固定図式の等式だけを正規化する。
規約：指定した全錐と元の射影を保持する。
使われ方：一点からの切断制限による空間値錐の比較頂点辺の検出。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 底制限の内部 Hom の自然性正方形の fiber 射は、元の切断制限そのもの。 -/
lemma coneRestriction_transportSquareFiberMap {K E B : SSet.{u}} (p : E ⟶ B)
    {D : K ⟶ B} (c : JoinCone D) :
    transportSquareFiberMap ((ihom (join (Δ[0] : SSet.{u}) K)).map p) ((ihom K).map p)
        ((pre (joinInr Δ[0] K)).app E) ((pre (joinInr Δ[0] K)).app B)
        ((pre (joinInr Δ[0] K)).naturality p) (functorVertex c.val) ≫
      eqToHom (congrArg (relativeFunctorSpace p) c.property) =
        leftFibrationConeRestriction p c := by
  rfl

/-- 頂点評価の内部 Hom 正方形の fiber 射は、元の全錐の頂点評価。 -/
lemma coneApex_transportSquareFiberMap {K X : SSet.{u}} {D : K ⟶ X}
    (c : JoinCone D) (x : X _⦋0⦌) :
    transportSquareFiberMap
        ((ihom (join (Δ[0] : SSet.{u}) K)).map
          (sliceUnderProjection (SSet.yonedaEquiv.symm x)))
        (sliceUnderProjection (SSet.yonedaEquiv.symm x))
        (evaluateFunctorAt (joinApexVertex K)) (evaluateFunctorAt (joinApexVertex K))
        (by rfl)
        (functorVertex c.val) ≫
      eqToHom (congrArg (vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm x)))
        (coneDiagram_apex c)) = coneApexSectionEvaluation c x := by
  rfl

end SerrePositivity.InfinityCategories.HomotopyLimits
