module

public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.TwistedArrowSourceLift
public import SerrePositivity.InfinityCategories.F2.Ind.RelativeEvaluationIsoTransport
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorSquarePost

/-!
概要：元の right fibration の全 twisted-arrow 持ち上げを制限すると、元の左端評価と相対同型。
方針：相対自明 Kan 比較の切断と恒等の可縮な同型を、同じ左端射影で写す。
規約：同じ切断と同じ元の底を保持。使われ方：指定された weighted 係数評価の回収。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {E B : SSet.{u}} (p : E ⟶ B) [RightFibration p]
local notation "r" => relativeEdgewiseRightComparison p
local notation "σ" => pullback.fst (edgewiseRight B) p ≫ edgewiseLeft B

/-- 元の同じ切断の左端評価は、相対比較で制限すると元の全左端評価と相対同型。 -/
def twistedArrowSourceLift_restrictIso : VertexIso
    (relativeFunctorVertex (SSet.opFunctor.map p) (edgewiseSubdivisionMap p ≫ edgewiseLeft B)
      (r ≫ twistedArrowSourceLift p) (by
        rw [Category.assoc, twistedArrowSourceLift_projection, ← Category.assoc,
          relativeEdgewiseRightComparison_fst]))
    (relativeFunctorVertex (SSet.opFunctor.map p) (edgewiseSubdivisionMap p ≫ edgewiseLeft B)
      (edgewiseLeft E) (edgewiseLeft_naturality p).symm) := by
  have hc := vertexFiber_isContractibleKan ((ihom (edgewiseSubdivision E)).map r) (functorVertex r)
  have := hc.kanComplex
  let v₀ : (relativeFunctorSpace r r) _⦋0⦌ :=
    relativeFunctorVertex r r (r ≫ twistedArrowRightSection p) (by
      rw [Category.assoc, twistedArrowRightSection_comparison, Category.comp_id])
  let v₁ : (relativeFunctorSpace r r) _⦋0⦌ :=
    relativeFunctorVertex r r (𝟙 _) (Category.id_comp _)
  have hi := terminalVertexIso (hc.isTerminalVertex v₀) (hc.isTerminalVertex v₁)
  have hw : edgewiseLeft E ≫ SSet.opFunctor.map p = r ≫ σ := by
    rw [← Category.assoc, relativeEdgewiseRightComparison_fst, edgewiseLeft_naturality]
  have he := VertexIso.map hi
    (relativeFunctorSquarePost r (SSet.opFunctor.map p) σ (edgewiseLeft E) hw r)
  have hs : (r ≫ twistedArrowRightSection p) ≫ r = r := by
    rw [Category.assoc, twistedArrowRightSection_comparison, Category.comp_id]
  have h₀ := relativeFunctorSquarePost_vertex r (SSet.opFunctor.map p) σ (edgewiseLeft E)
    hw r (r ≫ twistedArrowRightSection p) hs
  have h₁ := relativeFunctorSquarePost_vertex r (SSet.opFunctor.map p) σ (edgewiseLeft E)
    hw r (𝟙 _) (Category.id_comp _)
  have he' := eqToIso (congrArg SSet.HomotopyCategory.mk h₀.symm) ≪≫ he ≪≫
    eqToIso (congrArg SSet.HomotopyCategory.mk h₁)
  exact relativeEvaluationIsoOfEq (by rw [← Category.assoc, relativeEdgewiseRightComparison_fst])
    (Category.assoc _ _ _) (Category.id_comp _) he'

end SerrePositivity.InfinityCategories.F2.Ind
