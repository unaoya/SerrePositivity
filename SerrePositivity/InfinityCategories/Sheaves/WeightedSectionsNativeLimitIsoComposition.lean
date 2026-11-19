module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Sheaves.WeightedSectionsLocalComparison
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.OverEquivalenceLimitComposition
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftStraighteningLimitVertexComputations

/-!
概要：指定の重み付き切断の値を、二つの極限錐の標準比較に沿って移す。
方針：固定した指定輸送錐と同じ中間極限錐を使い、標準比較を相殺する。
規約：HTT §5.1.5.6、Kerodon Definition 7.3.1.2（Tag 02Y9）の局所極限の比較。
使われ方：R05.1。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories
namespace SerrePositivity.InfinityCategories.Sheaves
private lemma compareLeftStraightening_target_comp {A B K X : SSet.{u}}
    [Quasicategory K] [Quasicategory X]
    (p : A ⟶ K) (q : B ⟶ K) [LeftFibration p] [LeftFibration q]
    (e : FunctorIso (leftStraighteningInfinityDiagram p) (leftStraighteningInfinityDiagram q))
    (O : K ⟶ X) (t : JoinCone (p ≫ O)) (c d : JoinCone (q ≫ O))
    (ht : IsLimitCone t) (hc : IsLimitCone c) (hd : IsLimitCone d) :
    (limitVertexIsoOfLeftStraighteningIso p q e O t c ht hc).hom ≫
      (limitVertexIso c d hc hd).hom =
    (limitVertexIsoOfLeftStraighteningIso p q e O t d ht hd).hom := by
  letI : Quasicategory A := quasicategory_of_innerFibration p
  letI : Quasicategory B := quasicategory_of_innerFibration q
  let r := leftStraighteningInfinityReconstruction p
  let s := leftStraighteningInfinityReconstruction q
  let er := (leftStraighteningInfinityReconstruction_isPrecompositionEquivalence p).isQCatEquivalence
  let es := (leftStraighteningInfinityReconstruction_isPrecompositionEquivalence q).isQCatEquivalence
  let hr := leftStraighteningInfinityReconstruction_projection p
  let hs := leftStraighteningInfinityReconstruction_projection q
  have H₁ : HasLimit (smallLeftUnstraighteningProjection (leftStraighteningInfinityDiagram p) ≫ O) := by
    apply (hasLimit_iff_equivalentRestriction r er _).mpr
    change HasLimit (r ≫ (_ ≫ O))
    rw [← Category.assoc, hr]
    exact ⟨t, ht⟩
  have H₂ : HasLimit (smallLeftUnstraighteningProjection (leftStraighteningInfinityDiagram q) ≫ O) := by
    apply (hasLimit_iff_equivalentRestriction s es _).mpr
    change HasLimit (s ≫ (_ ≫ O))
    rw [← Category.assoc, hs]
    exact ⟨c, hc⟩
  obtain ⟨m, hm⟩ := H₁
  obtain ⟨n, hn⟩ := H₂
  let ic := limitVertexIsoOfOverEquivalence s es hs O c n hc hn
  let id := limitVertexIsoOfOverEquivalence s es hs O d n hd hn
  have h := limitVertexIso_hom_comp_overEquivalence s es hs O c d n hc hd hn
  change (limitVertexIso c d hc hd).hom ≫ id.hom = ic.hom at h
  have h' : ic.inv ≫ (limitVertexIso c d hc hd).hom = id.inv := by
    apply (cancel_mono id.hom).mp
    rw [Category.assoc, h, ic.inv_hom_id, id.inv_hom_id]
  rw [limitVertexIsoOfLeftStraighteningIso_eq_middle p q e O t c ht hc m n hm hn,
    limitVertexIsoOfLeftStraighteningIso_eq_middle p q e O t d ht hd m n hm hn]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [show ic.inv ≫ (limitVertexIso c d hc hd).hom = id.inv from h']

local instance nativeCompare_pullbackLeft {A B K : SSet.{u}} (p : A ⟶ B)
    [LeftFibration p] (f : K ⟶ B) : LeftFibration (Limits.pullback.snd p f) :=
  ⟨leftFibrations.pullback_snd _ _ (LeftFibration.mem (p := p))⟩

/-- 同じ指定値の比較は、標準の極限頂点比較に沿って自然である。 -/
@[cite HTT "5.1.5.6" (partial := special) "指定された反対Yonedaの局所極限での比較の計算法則。"]
lemma weightedSections_nativeShapeLimitIso_hom_comp :
∀ {C : Type u} [SmallCategory C] {E : SSet.{u + 1}} [Quasicategory E],
∀ (O : Presheaf C E) (hE : HTT.PresentableInfinityCategories.IsPresentable E),
∀ (P : (PresheafCat C SpaceInfinity.{u}).op _⦋0⦌)
 (c d : JoinCone (rightKanDiagram (nativeSetShapeOppositeYoneda C) O P))
 (hc : IsLimitCone c) (hd : IsLimitCone d),
 (weightedSections_nativeShapeLimitIso O hE P c hc).hom ≫
 (limitVertexIso c d hc hd).hom =
 (weightedSections_nativeShapeLimitIso O hE P d hd).hom := by
  intro C hC E hE₀ O hE P c d hc hd
  let t := (weightedSections_valueTransport O hE P).cone
  let ht := weightedSections_valueTransport_isLimit O hE P
  let hv := weightedSections_valueTransport_vertex O hE P
  let e := fixedOppositeSetYoneda_nativeIso C
  let i := rightKanLimitVertexIsoOfFunctorIso e O P t c ht hc
  let j := rightKanLimitVertexIsoOfFunctorIso e O P t d ht hd
  have h : i.hom ≫ (limitVertexIso c d hc hd).hom = j.hom := by
    unfold i j rightKanLimitVertexIsoOfFunctorIso
    apply compareLeftStraightening_target_comp
  change (hv ▸ i).hom ≫ (limitVertexIso c d hc hd).hom = (hv ▸ j).hom
  rw [vertexIso_transport_source_hom, vertexIso_transport_source_hom, Category.assoc, h]

end SerrePositivity.InfinityCategories.Sheaves
