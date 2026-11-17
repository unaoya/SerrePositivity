module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.StraighteningBaseChangeRestriction
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.FunctorIsoWhiskerComposition
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportRepresentationUnstraighteningComparison

/-!
概要：P3-C1Pの証明分割。scaffold上の指定pointed比較を全空間と指定辺へ移す。
方針：既存の前合成の充満忠実性・像の回収・辺代表の持ち上げを順に使う。
規約：HTT §3.3.2、Kerodon Corollary 5.6.0.6（Tag 028T）の構成の照合に使う法則。
  この補助部分だけでは、元のscaffold上のpointed比較の存在は結論していない。
使われ方：5∞-1のP3-C1P。元のνの辺代表を変えず、端点と射影を厳密に保つ。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
open SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

private lemma pointedComparisonIsoOfRestriction {A Z X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    (i : Z ⟶ A) (hi : IsPrecompositionEquivalence i) (q : X ⟶ Y)
    {f g : A ⟶ X} (d : FunctorIso (f ≫ q) (g ≫ q))
    (e : FunctorIso (i ≫ f) (i ≫ g))
    (h : e.postcomp q = d.precomp i) :
    ∃ a : FunctorIso f g, a.precomp i = e ∧ a.postcomp q = d := by
  let ff := (hi X).isFullyFaithful
  let a : FunctorIso f g := ff.preimageVertexIso
    (x := functorVertex f) (y := functorVertex g) e
  have hm : VertexIso.map a ((pre i).app X) = e :=
    ff.preimageVertexIso_map (x := functorVertex f) (y := functorVertex g) e
  have ha : a.precomp i = e := by
    exact eq_of_heq ((functorIsoPrecomp_heq_map a i).trans (heq_of_eq hm))
  refine ⟨a, ha, ?_⟩
  apply functorIso_precomp_injective i (hi Y).isFullyFaithful
  rw [← functorIso_precomp_postcomp, ha, h]

private lemma pointedPrismOfRestriction {A B Z : SSet.{u+1}} (p : A ⟶ B)
    (i : Z ⟶ A) (hi : IsPrecompositionEquivalence i)
    {F G : B ⟶ SpaceInfinity.{u}} (ν : FunctorIso F G)
    {f g : A ⟶ PointedSpaceInfinity.{u}}
    (hf : f ≫ pointedSpaceProjection = p ≫ F)
    (hg : g ≫ pointedSpaceProjection = p ≫ G)
    (e : FunctorIso (i ≫ f) (i ≫ g))
    (h : e.postcomp pointedSpaceProjection =
      (functorIsoOfEq (ν.precomp p) hf.symm hg.symm).precomp i) :
    let r := functorEdgeOfSimplicialHomotopy (functorHomHomotopy ν.hom)
    ∃ W : (Δ[1] : SSet.{u+1}) ⊗ A ⟶ PointedSpaceInfinity.{u},
      prismEndpoint 0 A ≫ W = f ∧ prismEndpoint 1 A ≫ W = g ∧
      W ≫ pointedSpaceProjection = (Δ[1] ◁ p) ≫ functorEdgePrism r := by
  dsimp only
  obtain ⟨a, _, haq⟩ := pointedComparisonIsoOfRestriction i hi pointedSpaceProjection
    (functorIsoOfEq (ν.precomp p) hf.symm hg.symm) e h
  have hn : functorIsoOfEq (a.postcomp pointedSpaceProjection) hf hg = ν.precomp p := by
    exact eq_of_heq ((functorIsoOfEq_heq _ hf hg).trans
      ((heq_of_eq haq).trans (functorIsoOfEq_heq _ hf.symm hg.symm)))
  let r := functorEdgeOfSimplicialHomotopy (functorHomHomotopy ν.hom)
  let rp := r.map ((truncation 2).map ((pre p).app SpaceInfinity.{u}))
  have hrp : Truncated.HomotopyCategory.homMk rp = (ν.precomp p).hom := by
    change (SSet.mapHomotopyCategory ((pre p).app SpaceInfinity.{u})).map
      (Truncated.HomotopyCategory.homMk r) = _
    rw [functorHomHomotopy_hom, functorIso_precomp_hom]
  obtain ⟨l, hl, _⟩ := functorIso_exists_edge_representative_over pointedSpaceProjection
    a (ν.precomp p) hf hg hn rp hrp
  refine ⟨functorEdgePrism l, functorEdgePrism_zero _, functorEdgePrism_one _, ?_⟩
  have hx : SSet.yonedaEquiv.symm l.edge ≫ (ihom A).map pointedSpaceProjection =
      SSet.yonedaEquiv.symm r.edge ≫ (pre p).app SpaceInfinity.{u} := by
    rw [SSet.yonedaEquiv_symm_comp, SSet.yonedaEquiv_symm_comp]
    exact congrArg SSet.yonedaEquiv.symm hl
  change functorFamilyPrism (SSet.yonedaEquiv.symm l.edge) ≫ pointedSpaceProjection = _
  rw [← functorFamilyPrism_post, hx, functorFamilyPrism_pre]
  rfl


end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
