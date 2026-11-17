module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.NativePullbackRepresentationArrowComparison
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SmallLeftUnstraighteningFunctorIso
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalenceCalculus

/-!
概要：指定したnative引き戻しの実射aは、同じ相対比較から準圏同値となる。
方針：同じ表現比較と指定νの作用の同値性を、相対同型の包含と二対三で反映する。
規約：HTT §3.3.2、Kerodon Corollary 5.6.0.6（Tag 028T）の既存構成の法則。
  元のa・R・eを引数に保つ。別の同値な実射を選ばない。
使われ方：5∞-1のR04.1、元の右Kanの局所形状の比較。
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
open SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

local instance nativeArrow_pullbackLeft {E B K : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (f : K ⟶ B) : LeftFibration (pullback.snd p f) :=
  ⟨leftFibrations.pullback_snd _ _ (LeftFibration.mem (p := p))⟩

/-- 指定表現の相対同型は、元の同じ実射aの同値性を反映する。
HTT §3.3.2、Kerodon 5.6.0.6（Tag 028T）の小さい表現での二対三の法則。 -/
@[cite HTT "3.3.2" (partial := special)
  "同じnative引き戻しの実射の同値性を、指定表現の相対同型から反映する法則。"]
lemma nativePullbackArrow_isQCatEquivalence :
∀ {E B K : SSet.{u}} [Quasicategory B] [Quasicategory K]
 (p : E ⟶ B) [LeftFibration p]
 (R : LeftTransportRepresentation ((SSet.uliftFunctor.{u + 1, u}).map p))
 {f g : K ⟶ B} (e : FunctorIso f g),
let Rf := R.nativeRestrict f
let Rg := R.nativeRestrict g
let ν := (functorIso_ulift.{u, u + 1} e).postcomp R.diagram
let rF := smallLeftUnstraighteningLift Rf.diagram Rf.comparison
let rG := smallLeftUnstraighteningLift Rg.diagram Rg.comparison
let z := rF ≫ smallUnstraighteningFunctorHom ν.hom
∀ (a : pullback p f ⟶ pullback p g)
 (hz : z ≫ smallLeftUnstraighteningProjection Rg.diagram = pullback.snd p f)
 (ht : (a ≫ rG) ≫ smallLeftUnstraighteningProjection Rg.diagram = pullback.snd p f)
 (h : VertexIso
   (relativeFunctorVertex (smallLeftUnstraighteningProjection Rg.diagram) (pullback.snd p f) z hz)
   (relativeFunctorVertex (smallLeftUnstraighteningProjection Rg.diagram) (pullback.snd p f) (a ≫ rG) ht)),
 IsQCatEquivalence a := by
  intro E B K hB hK p hp R f g e
  dsimp only
  intro a hz ht h
  let Rf := R.nativeRestrict f
  let Rg := R.nativeRestrict g
  let ν := (functorIso_ulift.{u, u + 1} e).postcomp R.diagram
  let rF := smallLeftUnstraighteningLift Rf.diagram Rf.comparison
  let rG := smallLeftUnstraighteningLift Rg.diagram Rg.comparison
  let pf := pullback.snd p f
  let pg := pullback.snd p g
  let q := smallLeftUnstraighteningProjection Rg.diagram
  let z := rF ≫ smallUnstraighteningFunctorHom ν.hom
  letI : Quasicategory (pullback p f) := quasicategory_of_innerFibration pf
  letI : Quasicategory (pullback p g) := quasicategory_of_innerFibration pg
  have erF : IsQCatEquivalence rF :=
    (smallLeftUnstraighteningLift_isPrecompositionEquivalence Rf.diagram pf Rf.comparison
      Rf.over_base Rf.isPrecompositionEquivalence).isQCatEquivalence
  have erG : IsQCatEquivalence rG :=
    (smallLeftUnstraighteningLift_isPrecompositionEquivalence Rg.diagram pg Rg.comparison
      Rg.over_base Rg.isPrecompositionEquivalence).isQCatEquivalence
  have en : IsQCatEquivalence (smallUnstraighteningFunctorHom ν.hom) :=
    (smallLeftUnstraighteningComparisonOfFunctorIso_isPrecompositionEquivalence ν).isQCatEquivalence
  have ez : IsQCatEquivalence z := erF.comp en
  have eh : FunctorIso z (a ≫ rG) :=
    h.map (vertexFiberι ((ihom (pullback p f)).map q) (functorVertex pf))
  exact erG.cancel_right (ez.ofFunctorIso eh)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
