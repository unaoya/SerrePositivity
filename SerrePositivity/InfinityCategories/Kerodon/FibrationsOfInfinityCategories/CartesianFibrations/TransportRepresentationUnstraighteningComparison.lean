module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.UnstraighteningSourceFamilyComparison
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.FunctorFamilyVertices
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SmallUnstraighteningIsoHom
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.WitnessPrism
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.WitnessPointedDiagramIso
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FunctorIsoEdgeRepresentative
/-!
概要：同じ表現空間の比較を、指定した分類辺のunstraighteningの相対比較へ送る。
方針：pointed比較の射影を正規化し、同じ代表辺へ揃えたprismを全族の比較へ渡す。
規約：Kerodon Remark 5.6.2.18（Tag 0271）、HTT §3.3.2の既存構成の法則。
  分類辺と全空間の比較を独立に選び直さない。任意の底を扱う。
使われ方：5∞-1の残り第2項の証明分割。元の復元射と任意の表現との比較への入力。
-/

@[expose] public noncomputable section
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
open SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories
open SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy
open CategoryTheory.Limits CartesianMonoidalCategory
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
private lemma pointNorm {E B : SSet.{u + 1}} {p : E ⟶ B} [LeftFibration p]
    (R S : LeftTransportRepresentation p)
    (h : VertexIso (transportWitnessVertex R) (transportWitnessVertex S)) :
    functorIsoOfEq ((R.pointedIso S h).postcomp pointedSpaceProjection)
      R.pointedMap_projection S.pointedMap_projection = (R.diagramIso S h).precomp p := by
  have hh {A X : SSet.{u + 1}} {f g f' g' : A ⟶ X}
      (e : FunctorIso f g) (hf : f = f') (hg : g = g') :
      (functorIsoOfEq e hf hg).hom = kanFunctorHomCongr hf hg e.hom := by
    subst f' g'
    simp only [functorIsoOfEq, kanFunctorHomCongr, Iso.homCongr_apply,
      eqToIso.hom, eqToIso.inv, eqToHom_refl, Category.id_comp, Category.comp_id]
  apply Iso.ext
  rw [hh]
  simpa only [functorIso_postcomp_hom, functorIso_precomp_hom,
    postcomposeFunctorHom_eq_map, precomposeFunctorHom_eq_map,
    SSet.hoFunctor_map, Functor.toCatHom_toFunctor] using
    SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.LeftTransportRepresentation.pointedIso_projection R S h

private lemma pointPrism {E B : SSet.{u + 1}} {p : E ⟶ B} [LeftFibration p]
    (R S : LeftTransportRepresentation p)
    (h : VertexIso (transportWitnessVertex R) (transportWitnessVertex S)) :
    ∃ W : (Δ[1] : SSet.{u + 1}) ⊗ E ⟶ PointedSpaceInfinity.{u},
      SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 E ≫ W = R.pointedMap ∧
      SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 E ≫ W = S.pointedMap ∧
      W ≫ pointedSpaceProjection = (Δ[1] ◁ p) ≫
        functorEdgePrism (SSet.Edge.ofTruncated (functorEdgeOfSimplicialHomotopy
          (functorHomHomotopy (R.diagramIso S h).hom))) := by
  let e := SSet.Edge.ofTruncated (functorEdgeOfSimplicialHomotopy
          (functorHomHomotopy (R.diagramIso S h).hom))
  let r := e.toTruncated.map ((truncation 2).map ((pre p).app SpaceInfinity.{u}))
  have hr : Truncated.HomotopyCategory.homMk r = ((R.diagramIso S h).precomp p).hom := by
    change (SSet.mapHomotopyCategory ((pre p).app SpaceInfinity.{u})).map
      (Truncated.HomotopyCategory.homMk e.toTruncated) = _
    have he : Truncated.HomotopyCategory.homMk e.toTruncated = (R.diagramIso S h).hom :=
      functorHomHomotopy_hom _
    rw [he, functorIso_precomp_hom]
  obtain ⟨l, hl, _⟩ := functorIso_exists_edge_representative_over pointedSpaceProjection
    (R.pointedIso S h) ((R.diagramIso S h).precomp p)
    R.pointedMap_projection S.pointedMap_projection (pointNorm R S h) r hr
  refine ⟨functorEdgePrism (SSet.Edge.ofTruncated l),
    functorEdgePrism_zero _, functorEdgePrism_one _, ?_⟩
  have hx : SSet.yonedaEquiv.symm l.edge ≫ (ihom E).map pointedSpaceProjection =
      SSet.yonedaEquiv.symm e.edge ≫ (pre p).app SpaceInfinity.{u} := by
    rw [SSet.yonedaEquiv_symm_comp, SSet.yonedaEquiv_symm_comp]
    exact congrArg SSet.yonedaEquiv.symm hl
  change functorFamilyPrism (SSet.yonedaEquiv.symm l.edge) ≫ pointedSpaceProjection = _
  rw [← functorFamilyPrism_post, hx, functorFamilyPrism_pre]
  rfl

/-- 同じ表現の比較のunstraighteningは、元の全空間の比較を相対写像空間内で回収する。 -/
lemma transportRepresentation_unstraighteningComparison {E B : SSet.{u + 1}} {p : E ⟶ B} [LeftFibration p]
    (R S : LeftTransportRepresentation p)
    (h : VertexIso (transportWitnessVertex R) (transportWitnessVertex S)) :
    let e := SSet.Edge.ofTruncated (functorEdgeOfSimplicialHomotopy
      (functorHomHomotopy (R.diagramIso S h).hom))
    let g := leftUnstraighteningMappingVertexMap R.diagram S.diagram (intervalMappingVertexOfEdge e)
    ∃ hf : (R.comparison ≫ g.val) ≫ leftUnstraighteningProjection S.diagram = p,
      Nonempty (VertexIso
        (relativeFunctorVertex (leftUnstraighteningProjection S.diagram) p
          (R.comparison ≫ g.val) hf)
        (relativeFunctorVertex (leftUnstraighteningProjection S.diagram) p S.comparison S.over_base)) := by
  dsimp only
  let e := SSet.Edge.ofTruncated (functorEdgeOfSimplicialHomotopy
    (functorHomHomotopy (R.diagramIso S h).hom))
  let z := intervalMappingVertexOfEdge e
  let g := leftUnstraighteningMappingVertexMap R.diagram S.diagram z
  let q := leftUnstraighteningProjection S.diagram
  have hf : (R.comparison ≫ g.val) ≫ q = p := by
    rw [Category.assoc, g.property, R.over_base]
  refine ⟨hf, ?_⟩
  obtain ⟨W, hw0, hw1, hwp⟩ := pointPrism R S h
  let K : SSet.{u + 1} := Δ[0]
  let t : K ⟶ leftUnstraighteningTransformationSpace R.diagram S.diagram := SSet.const z
  let f : E ⊗ K ⟶ leftUnstraightening S.diagram := fst E K ≫ S.comparison
  have hfp : f ≫ q = fst E K ≫ p := by rw [Category.assoc, S.over_base]
  let W' := fst (Δ[1] ⊗ E) K ≫ W
  have hw0' : (prismEndpoint 0 E ▷ K) ≫ W' =
      fst E K ≫ R.comparison ≫ pullback.fst pointedSpaceProjection R.diagram := by
    change (prismEndpoint 0 E ▷ K) ≫ (fst (Δ[1] ⊗ E) K ≫ W) = _
    rw [whiskerRight_fst_assoc, hw0]
    rfl
  have hw1' : (prismEndpoint 1 E ▷ K) ≫ W' =
      f ≫ pullback.fst pointedSpaceProjection S.diagram := by
    change (prismEndpoint 1 E ▷ K) ≫ (fst (Δ[1] ⊗ E) K ≫ W) = _
    rw [whiskerRight_fst_assoc, hw1]
    rfl
  have hwp' : W' ≫ pointedSpaceProjection =
      ((Δ[1] ◁ p) ▷ K) ≫ functorParameterizedPrism (intervalMappingUncurry t) := by
    rw [Category.assoc, hwp]
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    rintro ⟨⟨a, x⟩, y⟩
    rfl
  let H := unstraighteningSourceFamilyComparisonIso R.diagram S.diagram p
    R.comparison R.over_base t f hfp W' hw0' hw1' hwp'
  let v0 := stdSimplex.obj₀Equiv.symm (0 : Fin 1)
  have vl : ((t ≫ leftUnstraighteningMappingSpaceMap R.diagram S.diagram) ≫
      relativeFunctorOverPre q
        (Over.homMk (U := Over.mk p) (V := Over.mk (leftUnstraighteningProjection R.diagram))
          R.comparison R.over_base)).app (Opposite.op ⦋0⦌) v0 =
      relativeFunctorVertex q p (R.comparison ≫ g.val) hf := by
    change SSet.yonedaEquiv ((t ≫ leftUnstraighteningMappingSpaceMap R.diagram S.diagram) ≫
      relativeFunctorOverPre q (Over.homMk (U := Over.mk p)
        (V := Over.mk (leftUnstraighteningProjection R.diagram)) R.comparison R.over_base)) = _
    rw [show t = SSet.const z from rfl, SSet.const_comp, SSet.const_comp, SSet.yonedaEquiv_const,
      ← leftUnstraighteningMappingVertexMap_vertex]
    exact relativeFunctorOverPre_vertex (leftUnstraighteningProjection S.diagram)
      (Over.homMk (U := Over.mk p) (V := Over.mk (leftUnstraighteningProjection R.diagram))
        R.comparison R.over_base) g.val g.property
  have vr : (relativeFunctorCurry f hfp).app (Opposite.op ⦋0⦌) v0 =
      relativeFunctorVertex q p S.comparison S.over_base := by
    rw [relativeFunctorCurry_vertex]
    apply Subtype.ext
    apply congrArg functorVertex
    dsimp only [f]
    rw [← Category.assoc, lift_fst, Category.id_comp]
  exact ⟨(eqToIso (congrArg HomotopyCategory.mk vl)).symm ≪≫
    H.app v0 ≪≫ eqToIso (congrArg HomotopyCategory.mk vr)⟩

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
