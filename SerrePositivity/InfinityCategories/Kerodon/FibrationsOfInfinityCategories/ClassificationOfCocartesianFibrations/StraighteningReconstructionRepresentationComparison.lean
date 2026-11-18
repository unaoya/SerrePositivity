module

public meta import SerrePositivity.Util.Citation

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SmallTransportRepresentationComparison
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SmallUnstraighteningFunctorHomComposition
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.StraighteningRepresentationComparisonLaw
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftStraighteningInfinityReconstruction
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SmallStraighteningCounit
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorPostLaws
/-!
概要：元の全straighteningの復元射を、任意の同じ相対表現からの指定射と比較する。
方針：表現空間の同じ比較、指定Homの合成則、元の宇宙への降下を接続する。
規約：Kerodon Corollary 5.6.0.6（Tag 028T）、HTT §3.3.2の既存構成の比較の法則。
  元の復元射と指定したrepresentationIsoの逆を保持し、存在だけの別の同型を使わない。
使われ方：5∞-1の残り第2項、指定余単位の局所頂点比較への接続。
-/

@[expose] public noncomputable section
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
/-- 元の復元射は、同じ指定分類同型の逆で表した射と底上の相対写像空間で同型。 -/
@[cite HTT "3.3.2" (partial := special) "指定分類同型と同じ相対表現による復元の比較の法則。"]
lemma leftStraighteningInfinityReconstruction_representationComparison {E B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) [LeftFibration p]
    (R : LeftTransportRepresentation ((SSet.uliftFunctor.{u + 1, u}).map p)) :
    let q := smallLeftUnstraighteningProjection (leftStraighteningInfinityDiagram p)
    let a := leftStraighteningInfinityDiagram_representationIso p R
    let f := smallLeftUnstraighteningLift R.diagram R.comparison ≫ smallUnstraighteningFunctorHom a.inv
    ∃ hf : f ≫ q = p,
      Nonempty (VertexIso
        (relativeFunctorVertex q p (leftStraighteningInfinityReconstruction p)
          (leftStraighteningInfinityReconstruction_projection p))
        (relativeFunctorVertex q p f hf)) := by
  dsimp only
  let U := SSet.uliftFunctor.{u + 1, u}
  let N := nativeLeftTransportRepresentation p
  let ηR := leftStraighteningInfinityDiagram_representationIso p R
  let ηN := leftStraighteningInfinityDiagram_representationIso p N
  haveI : ∀ m, Small.{u} ((U.obj E).obj m) := fun m => by
    change Small.{u} (ULift.{u + 1, u} (E.obj m))
    infer_instance
  let h := smallTransportRepresentationVertexIso (U.map p) R N
  let c := R.diagramIso N h
  have hc : ηR ≪≫ c = ηN :=
    leftStraighteningInfinityDiagram_representationIso_comp_diagramIso p R N h
  have hinv : ηR.inv = c.hom ≫ ηN.inv := by
    have hi := congrArg (fun e => e.inv) hc
    simp only [Iso.trans_inv] at hi
    calc
      ηR.inv = c.hom ≫ (c.inv ≫ ηR.inv) := by rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
      _ = c.hom ≫ ηN.inv := congrArg (fun v => c.hom ≫ v) hi
  let q := smallLeftUnstraighteningProjection (leftStraighteningInfinityDiagram p)
  let qR := smallLeftUnstraighteningProjection R.diagram
  let qN := smallLeftUnstraighteningProjection N.diagram
  let rR := smallLeftUnstraighteningLift R.diagram R.comparison
  let rN := smallLeftUnstraighteningLift N.diagram N.comparison
  have hr : rR ≫ qR = p := smallLeftUnstraighteningLift_projection R.diagram p R.comparison R.over_base
  have hn : rN ≫ qN = p := smallLeftUnstraighteningLift_projection N.diagram p N.comparison N.over_base
  let nc := smallUnstraighteningFunctorHom c.hom
  let cn := smallUnstraighteningFunctorHom ηN.inv
  have hnc : nc ≫ qN = qR := smallUnstraighteningFunctorHom_projection _
  have hcn : cn ≫ q = qN := smallUnstraighteningFunctorHom_projection _
  let f := rR ≫ smallUnstraighteningFunctorHom ηR.inv
  have hf : f ≫ q = p := by
    dsimp only [f, q]
    rw [Category.assoc, smallUnstraighteningFunctorHom_projection, hr]
  refine ⟨hf, ?_⟩
  have hz := smallTransportRepresentation_unstraighteningComparison p R N h
  change ∃ hrnc : (rR ≫ nc) ≫ qN = p,
    Nonempty (VertexIso (relativeFunctorVertex qN p (rR ≫ nc) hrnc)
      (relativeFunctorVertex qN p rN hn)) at hz
  obtain ⟨hrnc, ⟨ern⟩⟩ := hz
  obtain ⟨ec⟩ := smallUnstraighteningFunctorHom_comp_iso c.hom ηN.inv
  let ov : Over.mk p ⟶ Over.mk qR := Over.homMk rR hr
  let e0 := ec.map (relativeFunctorOverPre q ov)
  have hcf : smallUnstraighteningFunctorHom (c.hom ≫ ηN.inv) ≫ q = qR :=
    smallUnstraighteningFunctorHom_projection _
  have hnc_cn : (nc ≫ cn) ≫ q = qR := by rw [Category.assoc, hcn, hnc]
  have hl := relativeFunctorOverPre_vertex q ov
    (smallUnstraighteningFunctorHom (c.hom ≫ ηN.inv)) hcf
  have hh := relativeFunctorOverPre_vertex q ov (nc ≫ cn) hnc_cn
  let ep := (eqToIso (congrArg HomotopyCategory.mk hl)).symm ≪≫ e0 ≪≫
    eqToIso (congrArg HomotopyCategory.mk hh)
  have hpostl := relativeFunctorPost_vertex qN q cn hcn p (rR ≫ nc) hrnc
  have hpostr := relativeFunctorPost_vertex qN q cn hcn p rN hn
  let epost := (eqToIso (congrArg HomotopyCategory.mk hpostl)).symm ≪≫
    ern.map (relativeFunctorPost qN q cn hcn p) ≪≫
    eqToIso (congrArg HomotopyCategory.mk hpostr)
  have hlp : (rR ≫ smallUnstraighteningFunctorHom (c.hom ≫ ηN.inv)) ≫ q = p := by
    rw [Category.assoc, hcf, hr]
  have hap : (rR ≫ (nc ≫ cn)) ≫ q = p := by rw [Category.assoc, hnc_cn, hr]
  have ha'p : ((rR ≫ nc) ≫ cn) ≫ q = p := by rw [Category.assoc, hcn, hrnc]
  have hnp : (rN ≫ cn) ≫ q = p := by rw [Category.assoc, hcn, hn]
  have hv0 : relativeFunctorVertex q p f hf =
      relativeFunctorVertex q p (rR ≫ smallUnstraighteningFunctorHom (c.hom ≫ ηN.inv)) hlp := by
    apply Subtype.ext
    exact congrArg functorVertex (congrArg (fun v => rR ≫ smallUnstraighteningFunctorHom v) hinv)
  have hva : relativeFunctorVertex q p (rR ≫ (nc ≫ cn)) hap =
      relativeFunctorVertex q p ((rR ≫ nc) ≫ cn) ha'p := by
    apply Subtype.ext
    exact congrArg functorVertex (Category.assoc rR nc cn).symm
  have hve : relativeFunctorVertex q p (rN ≫ cn) hnp =
      relativeFunctorVertex q p (leftStraighteningInfinityReconstruction p)
        (leftStraighteningInfinityReconstruction_projection p) := by
    apply Subtype.ext
    apply congrArg functorVertex
    rfl
  exact ⟨(eqToIso (congrArg HomotopyCategory.mk hv0) ≪≫ ep ≪≫
    eqToIso (congrArg HomotopyCategory.mk hva) ≪≫ epost ≪≫
    eqToIso (congrArg HomotopyCategory.mk hve)).symm⟩

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
