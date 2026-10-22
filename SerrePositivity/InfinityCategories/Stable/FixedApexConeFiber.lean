module
public import SerrePositivity.InfinityCategories.Stable.VertexFiberSwap
public import SerrePositivity.InfinityCategories.HomotopyLimits.FixedEndpointConeSpace
public import SerrePositivity.InfinityCategories.Stable.PointedConeLeftFibration
public import SerrePositivity.InfinityCategories.Stable.LoopConeDiagramFibers

/-!
概要：固定錐頂点と固定図式の二段 fiber の厳密な比較。
方針：元の全単体と比較円柱を保ち、厳密 fiber の普遍性で接続する。
規約：安定性を先取りしない。使われ方：一般安定性判定の実 loop fiber 比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 錐の頂点評価は、元の全錐の左頂点での評価そのもの。 -/
lemma coneFamilyApex_eq_vertexEvaluation {K X : SSet.{u}} (p : K ⟶ X) :
    HomotopyLimits.coneFamilyApex p =
      vertexFiberι (coneRestriction K X) (functorVertex p) ≫ coneApexEvaluation K X := by
  change vertexFiberι (coneRestriction K X) (functorVertex p) ≫
      (pre (joinInl (Δ[0] : SSet.{u}) K)).app X ≫
        evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) = _
  rw [stable_pre_evaluateFunctorAt]
  rfl

/-- 固定錐頂点と固定図式の順序を、同じ全錐を保って交換する。 -/
def fixedApexPointedConeDiagramFiberIso {K X : SSet.{u}} (p : K ⟶ X) (x : X _⦋0⦌) :
    HomotopyLimits.fixedApexConeFamily p x ≅
      vertexFiber (pointedConeProjection K X x) (functorVertex p) :=
  eqToIso (congrArg (fun f ↦ vertexFiber f x) (coneFamilyApex_eq_vertexEvaluation p)) ≪≫
    vertexFiberSwapIso (coneRestriction K X) (coneApexEvaluation K X) (functorVertex p) x

/-- 固定頂点の錐 fiber の厳密比較は、元の全錐の評価と可換。 -/
lemma fixedApexPointedConeDiagramFiberIso_hom_ι {K X : SSet.{u}} (p : K ⟶ X)
    (x : X _⦋0⦌) :
    (fixedApexPointedConeDiagramFiberIso p x).hom ≫
        vertexFiberι (pointedConeProjection K X x) (functorVertex p) ≫
          vertexFiberι (coneApexEvaluation K X) x =
      HomotopyLimits.fixedApexConeFamilyEvaluation p x := by
  dsimp only [fixedApexPointedConeDiagramFiberIso, Iso.trans_hom, pointedConeProjection,
    HomotopyLimits.fixedApexConeFamilyEvaluation, HomotopyLimits.fixedApexConeFamily, coneFamily]
  rw [Category.assoc, vertexFiberSwapIso_hom_ι, ← Category.assoc,
    vertexFiberEqToIso_hom_ι]
  exact coneFamilyApex_eq_vertexEvaluation p
end SerrePositivity.InfinityCategories
