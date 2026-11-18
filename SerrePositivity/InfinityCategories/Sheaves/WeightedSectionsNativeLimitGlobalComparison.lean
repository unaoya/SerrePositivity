module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Sheaves.WeightedSectionsGlobalComparisonVertex
public import SerrePositivity.InfinityCategories.Sheaves.WeightedSectionsNativeLimitIsoComposition
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightKanIndexTransportValue

/-!
概要：指定した重み付き切断の局所極限の値は、大域的な右 Kan 比較の成分で計算できる。
方針：同じ余単位の輸送を選び、添字輸送の頂点と標準極限比較の合成を計算する。
規約：HTT 5.1.5.6、Kerodon Definition 7.3.1.2（Tag 02Y9）の指定右 Kan 比較。
使われ方：S8 の指定離散重みの射の計算。
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy
open SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
namespace SerrePositivity.InfinityCategories.Sheaves

local instance nativeSource_pullbackLeft {A B K : SSet.{u}} (p : A ⟶ B)
    [LeftFibration p] (f : K ⟶ B) : LeftFibration (pullback.snd p f) :=
  ⟨leftFibrations.pullback_snd _ _ (LeftFibration.mem (p := p))⟩

private lemma rightKanLimitVertexIsoOfFunctorIso_hom_source_comp
    {K C D : SSet.{u}} [Quasicategory K] [Quasicategory C] [Quasicategory D]
    {δ δ' : K ⟶ C} (e : FunctorIso δ δ') (O : K ⟶ D) (v : C _⦋0⦌)
    (c s : JoinCone (rightKanDiagram δ O v)) (t : JoinCone (rightKanDiagram δ' O v))
    (hc : IsLimitCone c) (hs : IsLimitCone s) (ht : IsLimitCone t) :
    (limitVertexIso c s hc hs).hom ≫ (rightKanLimitVertexIsoOfFunctorIso e O v s t hs ht).hom =
      (rightKanLimitVertexIsoOfFunctorIso e O v c t hc ht).hom := by
  let p := rightKanProjection δ v
  let q := rightKanProjection δ' v
  let e₀ := leftPullbackClassificationIso (sliceUnderProjection (SSet.yonedaEquiv.symm v)) e
  letI : LeftFibration p := inferInstance
  letI : LeftFibration q := inferInstance
  letI : Quasicategory (rightKanShape δ v) := quasicategory_of_innerFibration p
  letI : Quasicategory (rightKanShape δ' v) := quasicategory_of_innerFibration q
  let r₀ := leftStraighteningInfinityReconstruction p
  let r₁ := leftStraighteningInfinityReconstruction q
  let er₀ := (leftStraighteningInfinityReconstruction_isPrecompositionEquivalence p).isQCatEquivalence
  let er₁ := (leftStraighteningInfinityReconstruction_isPrecompositionEquivalence q).isQCatEquivalence
  let h₀ := leftStraighteningInfinityReconstruction_projection p
  let h₁ := leftStraighteningInfinityReconstruction_projection q
  have H₀ : HasLimit (smallLeftUnstraighteningProjection (leftStraighteningInfinityDiagram p) ≫ O) := by
    apply (hasLimit_iff_equivalentRestriction r₀ er₀ _).mpr
    change HasLimit (r₀ ≫ (_ ≫ O))
    rw [← Category.assoc, h₀]
    exact ⟨c, hc⟩
  have H₁ : HasLimit (smallLeftUnstraighteningProjection (leftStraighteningInfinityDiagram q) ≫ O) := by
    apply (hasLimit_iff_equivalentRestriction r₁ er₁ _).mpr
    change HasLimit (r₁ ≫ (_ ≫ O))
    rw [← Category.assoc, h₁]
    exact ⟨t, ht⟩
  obtain ⟨m, hm⟩ := H₀
  obtain ⟨n, hn⟩ := H₁
  change (limitVertexIso c s hc hs).hom ≫
      (limitVertexIsoOfLeftStraighteningIso p q e₀ O s t hs ht).hom =
    (limitVertexIsoOfLeftStraighteningIso p q e₀ O c t hc ht).hom
  rw [limitVertexIsoOfLeftStraighteningIso_eq_middle p q e₀ O s t hs ht m n hm hn,
    limitVertexIsoOfLeftStraighteningIso_eq_middle p q e₀ O c t hc ht m n hm hn]
  simp only [Iso.trans_hom, ← Category.assoc]
  rw [limitVertexIso_hom_comp_overEquivalence r₀ er₀ h₀ O c s m hc hs hm]

/-- 元の指定重み付き切断の値の比較は、同じ大域比較の成分を標準極限比較へ続けた射。 -/
@[cite HTT "5.1.5.6" (partial := special) "重み付き切断における指定右 Kan 比較の成分。"]
lemma weightedSections_nativeShapeLimitIso_hom_eq_globalComparison :
∀ {C : Type u} [SmallCategory C] {E : SSet.{u + 1}} [Quasicategory E],
∀ (O : Presheaf C E) (hE : HTT.PresentableInfinityCategories.IsPresentable E)
  {G : (PresheafCat C SpaceInfinity.{u}).op ⟶ E}
  (β : SSet.Homotopy (nativeSetShapeOppositeYoneda C ≫ G) O)
  (hβ : IsRightKanExtension (nativeSetShapeOppositeYoneda C) O G β)
  (P : (PresheafCat C SpaceInfinity.{u}).op _⦋0⦌)
  (t : RightKanConeTransport (nativeSetShapeOppositeYoneda C) O G β P)
  (ht : IsLimitCone t.cone)
  (d : JoinCone (rightKanDiagram (nativeSetShapeOppositeYoneda C) O P))
  (hd : IsLimitCone d),
  (weightedSections_nativeShapeLimitIso O hE P d hd).hom =
    functorHomEvaluate (weightedSections_nativeShape_comparison O hE β hβ).hom P ≫
    eqToHom (congrArg (fun x => (HomotopyCategory.mk x : hoFunctor.obj E))
      t.cone_vertex.symm) ≫ (limitVertexIso t.cone d ht hd).hom := by
  intro C hC E hQ O hE G β hβ P t ht d hd
  let ε := fixedOppositeSetYoneda_nativeIso C
  let z := Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy β)
  let b := (ε.postcomp G).hom ≫ z
  let α := functorHomHomotopy b
  let c := weightedSections_valueTransport O hE P
  let hc := weightedSections_valueTransport_isLimit O hE P
  let hv := weightedSections_valueTransport_vertex O hE P
  let m := functorHomEvaluate (weightedSections_nativeShape_comparison O hE β hβ).hom P
  obtain ⟨s⟩ := rightKanConeTransport_nonempty (oppositeSpaceYoneda C) O G α P
  let hs := (isRightKanExtension_iff_forall_transport _ _ _ _).mp
    (weightedSections_nativeShape_counit_isRightKan O hE β hβ) P s
  let a := eqToIso (congrArg (fun x => (HomotopyCategory.mk x : hoFunctor.obj E)) hv)
  let e := eqToIso (congrArg (fun x => (HomotopyCategory.mk x : hoFunctor.obj E)) s.cone_vertex)
  let f := eqToIso (congrArg (fun x => (HomotopyCategory.mk x : hoFunctor.obj E)) t.cone_vertex)
  let n := rightKanLimitVertexIsoOfFunctorIso ε O P s.cone t.cone hs ht
  let p := rightKanLimitVertexIsoOfFunctorIso ε O P c.cone t.cone hc ht
  let j := limitVertexIso c.cone s.cone hc hs
  have hn : e.inv ≫ n.hom ≫ f.hom = 𝟙 _ :=
    rightKanIndexTransport_valueHom ε O G β P s t hs ht
  have hm : a.inv ≫ j.hom ≫ e.hom = m :=
    weightedSections_nativeShape_comparison_transport_vertex O hE β hβ P s
  have hn' : n.hom = e.hom ≫ f.inv := by
    apply (cancel_epi e.inv).mp
    apply (cancel_mono f.hom).mp
    simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
      Category.id_comp, Category.comp_id] using hn
  have hp : p.hom = j.hom ≫ n.hom :=
    (rightKanLimitVertexIsoOfFunctorIso_hom_source_comp ε O P c.cone s.cone t.cone hc hs ht).symm
  have hvv : (weightedSections_nativeShapeLimitIso O hE P t.cone ht).hom = a.inv ≫ p.hom := by
    change (hv ▸ p).hom = _
    exact vertexIso_transport_source_hom hv p
  rw [← weightedSections_nativeShapeLimitIso_hom_comp O hE P t.cone d ht hd, hvv, hp, hn']
  calc
    _ = (a.inv ≫ j.hom ≫ e.hom) ≫ f.inv ≫ (limitVertexIso t.cone d ht hd).hom := by
      simp only [Category.assoc]
    _ = _ := congrArg (fun k => k ≫ f.inv ≫ (limitVertexIso t.cone d ht hd).hom) hm

end SerrePositivity.InfinityCategories.Sheaves
