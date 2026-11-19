module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.NativePullbackArrowEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftPullbackRepresentationComparison
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.StraighteningReconstructionRepresentationComparison
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorPostLaws

/-!
概要：指定したnative引き戻しの相対比較を、元の分類図式の復元spanへ戻す。
方針：指定した二つの表現比較と小さいunstraighteningの相対合成則を貼る。
規約：HTT §3.3.2、Kerodon Corollary 5.6.0.6（Tag 028T）の構成の法則。
使われ方：R04.3。
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
open SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

local instance nativeRelative_pullbackLeft {E B K : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (f : K ⟶ B) : LeftFibration (pullback.snd p f) :=
  ⟨leftFibrations.pullback_snd _ _ (LeftFibration.mem (p := p))⟩

private theorem relativeVertex_eq {A X B : SSet.{u}} (q : X ⟶ B) (p : A ⟶ B)
    {f g : A ⟶ X} {hf : f ≫ q = p} {hg : g ≫ q = p} (e : f = g) :
    relativeFunctorVertex q p f hf = relativeFunctorVertex q p g hg :=
  Subtype.ext (congrArg functorVertex e)

private def postRelativeIso {A X Y B : SSet.{u}} (p : A ⟶ B) (q : X ⟶ B) (r : Y ⟶ B)
    (k : X ⟶ Y) (hk : k ≫ r = q)
    {f g : A ⟶ X} {hf : f ≫ q = p} {hg : g ≫ q = p}
    (i : VertexIso (relativeFunctorVertex q p f hf) (relativeFunctorVertex q p g hg)) :
    VertexIso (relativeFunctorVertex r p (f ≫ k) (by rw [Category.assoc, hk, hf]))
      (relativeFunctorVertex r p (g ≫ k) (by rw [Category.assoc, hk, hg])) := by
  have h := i.map (relativeFunctorPost q r k hk p)
  rw [relativeFunctorPost_vertex, relativeFunctorPost_vertex] at h
  exact h

private def preRelativeIso {A A' X B : SSet.{u}} (q : X ⟶ B)
    (p : A ⟶ B) (p' : A' ⟶ B) (a : A ⟶ A') (ha : a ≫ p' = p)
    {f g : A' ⟶ X} {hf : f ≫ q = p'} {hg : g ≫ q = p'}
    (i : VertexIso (relativeFunctorVertex q p' f hf) (relativeFunctorVertex q p' g hg)) :
    VertexIso (relativeFunctorVertex q p (a ≫ f) (by rw [Category.assoc, hf, ha]))
      (relativeFunctorVertex q p (a ≫ g) (by rw [Category.assoc, hg, ha])) := by
  let v : Over.mk p ⟶ Over.mk p' := Over.homMk a ha
  have he₀ := relativeFunctorOverPre_vertex q v f hf
  have he₁ := relativeFunctorOverPre_vertex q v g hg
  exact (eqToIso (congrArg HomotopyCategory.mk he₀)).symm ≪≫
    i.map (relativeFunctorOverPre q v) ≪≫ eqToIso (congrArg HomotopyCategory.mk he₁)

/-- 同じ実射の相対同型を、元の復元spanの相対同型として読む。 -/
@[cite HTT "3.3.2" (partial := special)
  "指定されたnative表現の射と元の復元spanの比較の合成則。"]
lemma nativePullback_reconstruction_relativeIso :
∀ {E B K : SSet.{u}} [Quasicategory B] [Quasicategory K]
 (p : E ⟶ B) [LeftFibration p]
 (R : LeftTransportRepresentation ((SSet.uliftFunctor.{u + 1, u}).map p))
 {f g : K ⟶ B} (e : FunctorIso f g),
let pf := pullback.snd p f
let pg := pullback.snd p g
let ν := (functorIso_ulift.{u, u + 1} e).postcomp R.diagram
let ν₀ := leftPullbackClassificationIso p e
let rF := smallLeftUnstraighteningLift (R.nativeRestrict f).diagram (R.nativeRestrict f).comparison
let rG := smallLeftUnstraighteningLift (R.nativeRestrict g).diagram (R.nativeRestrict g).comparison
let q := smallLeftUnstraighteningProjection (leftStraighteningInfinityDiagram pg)
∀ (a : pullback p f ⟶ pullback p g)
 (hz : (rF ≫ smallUnstraighteningFunctorHom ν.hom) ≫
   smallLeftUnstraighteningProjection (R.nativeRestrict g).diagram = pf)
 (ht : (a ≫ rG) ≫ smallLeftUnstraighteningProjection (R.nativeRestrict g).diagram = pf)
 (h : VertexIso
   (relativeFunctorVertex (smallLeftUnstraighteningProjection (R.nativeRestrict g).diagram) pf
     (rF ≫ smallUnstraighteningFunctorHom ν.hom) hz)
   (relativeFunctorVertex (smallLeftUnstraighteningProjection (R.nativeRestrict g).diagram) pf (a ≫ rG) ht)),
 ∃ (h₀ : (leftStraighteningInfinityReconstruction pf ≫
       smallLeftUnstraighteningComparisonOfFunctorIso ν₀) ≫ q = pf)
   (h₁ : (a ≫ leftStraighteningInfinityReconstruction pg) ≫ q = pf),
 Nonempty (VertexIso
   (relativeFunctorVertex q pf (leftStraighteningInfinityReconstruction pf ≫
       smallLeftUnstraighteningComparisonOfFunctorIso ν₀) h₀)
   (relativeFunctorVertex q pf (a ≫ leftStraighteningInfinityReconstruction pg) h₁)) := by
  intro E B K hB hK p hp R f g e
  dsimp only
  intro a hz ht h
  let pf := pullback.snd p f
  let pg := pullback.snd p g
  let Rf := R.nativeRestrict f
  let Rg := R.nativeRestrict g
  let ν := (functorIso_ulift.{u,u+1} e).postcomp R.diagram
  let ν₀ := leftPullbackClassificationIso p e
  let rF := smallLeftUnstraighteningLift Rf.diagram Rf.comparison
  let rG := smallLeftUnstraighteningLift Rg.diagram Rg.comparison
  let sf := leftStraighteningInfinityReconstruction pf
  let sg := leftStraighteningInfinityReconstruction pg
  let ef := leftStraighteningInfinityDiagram_representationIso pf Rf
  let eg := leftStraighteningInfinityDiagram_representationIso pg Rg
  let q := smallLeftUnstraighteningProjection (leftStraighteningInfinityDiagram pg)
  let m := smallUnstraighteningFunctorHom ν.hom
  let m₀ := smallUnstraighteningFunctorHom ν₀.hom
  let i := smallUnstraighteningFunctorHom ef.inv
  let j := smallUnstraighteningFunctorHom eg.inv
  have hG : rG ≫ smallLeftUnstraighteningProjection Rg.diagram = pg :=
    smallLeftUnstraighteningLift_projection Rg.diagram pg Rg.comparison Rg.over_base
  have ha : a ≫ pg = pf := by
    rw [← hG, ← Category.assoc]
    exact ht
  obtain ⟨hf, ⟨ef'⟩⟩ := leftStraighteningInfinityReconstruction_representationComparison pf Rf
  obtain ⟨hg, ⟨eg'⟩⟩ := leftStraighteningInfinityReconstruction_representationComparison pg Rg
  have h₀ : (sf ≫ m₀) ≫ q = pf := by
    rw [Category.assoc, smallUnstraighteningFunctorHom_projection,
      leftStraighteningInfinityReconstruction_projection]
  have h₁ : (a ≫ sg) ≫ q = pf := by
    rw [Category.assoc, leftStraighteningInfinityReconstruction_projection, ha]
  have homEq : ef.inv ≫ ν₀.hom = ν.hom ≫ eg.inv := by
    have hs := congrArg Iso.hom (leftPullbackClassificationIso_representation_naturality p e R)
    change ν₀.hom ≫ eg.hom = ef.hom ≫ ν.hom at hs
    calc
      ef.inv ≫ ν₀.hom = ef.inv ≫ (ν₀.hom ≫ eg.hom) ≫ eg.inv := by
        simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
      _ = ν.hom ≫ eg.inv := by
        rw [hs]
        simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  let qF := smallLeftUnstraighteningProjection (leftStraighteningInfinityDiagram pf)
  let qRF := smallLeftUnstraighteningProjection Rf.diagram
  let qRG := smallLeftUnstraighteningProjection Rg.diagram
  let e₁ := postRelativeIso pf qF q m₀ (smallUnstraighteningFunctorHom_projection _) ef'
  have hF : rF ≫ qRF = pf :=
    smallLeftUnstraighteningLift_projection Rf.diagram pf Rf.comparison Rf.over_base
  obtain ⟨comp₁⟩ := smallUnstraighteningFunctorHom_comp_iso ef.inv ν₀.hom
  obtain ⟨comp₂⟩ := smallUnstraighteningFunctorHom_comp_iso ν.hom eg.inv
  let e₂ := (preRelativeIso q pf qRF rF hF comp₁).symm
  let e₃ := preRelativeIso q pf qRF rF hF comp₂
  let e₄ := postRelativeIso pf qRG q j (smallUnstraighteningFunctorHom_projection _) h
  let e₅ := (preRelativeIso q pf pg a ha eg').symm
  have h₂ : ((rF ≫ i) ≫ m₀) ≫ q = pf := by
    rw [Category.assoc, smallUnstraighteningFunctorHom_projection]
    exact hf
  have h₂' : (rF ≫ (i ≫ m₀)) ≫ q = pf := by rw [← Category.assoc rF i m₀, h₂]
  have h₃ : (rF ≫ smallUnstraighteningFunctorHom (ef.inv ≫ ν₀.hom)) ≫ q = pf := by
    rw [Category.assoc, smallUnstraighteningFunctorHom_projection, hF]
  have h₃' : (rF ≫ smallUnstraighteningFunctorHom (ν.hom ≫ eg.inv)) ≫ q = pf := by
    rw [← homEq, h₃]
  have h₄ : (rF ≫ (m ≫ j)) ≫ q = pf := by
    rw [← Category.assoc rF m j, Category.assoc (rF ≫ m) j,
      smallUnstraighteningFunctorHom_projection]
    exact hz
  have h₄' : ((rF ≫ m) ≫ j) ≫ q = pf := by rw [Category.assoc rF m j, h₄]
  have h₅ : ((a ≫ rG) ≫ j) ≫ q = pf := by
    rw [Category.assoc (a ≫ rG), smallUnstraighteningFunctorHom_projection]
    exact ht
  have h₅' : (a ≫ (rG ≫ j)) ≫ q = pf := by rw [← Category.assoc a rG j, h₅]
  have t₂ := relativeVertex_eq q pf (hf := h₂) (hg := h₂') (Category.assoc rF i m₀)
  have t₃ := relativeVertex_eq q pf (hf := h₃) (hg := h₃')
    (congrArg (fun x => rF ≫ smallUnstraighteningFunctorHom x) homEq)
  have t₄ := relativeVertex_eq q pf (hf := h₄) (hg := h₄') (Category.assoc rF m j).symm
  have t₅ := relativeVertex_eq q pf (hf := h₅) (hg := h₅') (Category.assoc a rG j)
  exact ⟨h₀, h₁, ⟨e₁ ≪≫ eqToIso (congrArg HomotopyCategory.mk t₂) ≪≫ e₂ ≪≫
    eqToIso (congrArg HomotopyCategory.mk t₃) ≪≫ e₃ ≪≫
    eqToIso (congrArg HomotopyCategory.mk t₄) ≪≫ e₄ ≪≫
    eqToIso (congrArg HomotopyCategory.mk t₅) ≪≫ e₅⟩⟩

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
