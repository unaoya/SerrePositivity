module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Sheaves.WeightedSectionsRelativeCechDiagonal
public import SerrePositivity.InfinityCategories.Sheaves.WeightedSectionsDiscreteMap
public import SerrePositivity.InfinityCategories.Sheaves.RelativeCechLocalSections
public import SerrePositivity.InfinityCategories.Sheaves.CechIndexConstantLimit
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SimplicialHomotopyOpposite

/-!
概要：局所単射の場合、元の相対 Čech 対角に沿った切断は各次数で可逆。
方針：全対角の頂点成分を指定切断の写像に照合する。
  文献対応：HTT 6.2.2.6（集合値重みを持つ Čech 図式の場合）。
使われ方：相対 Čech 対角全体の可逆性。
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.HA.StableInfinityCategories
open SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CatInfinity
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy
open SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
open Truncated.HomotopyCategory
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations

namespace SerrePositivity.InfinityCategories.Sheaves

private theorem evaluateHomotopy_cast_target {A E : SSet.{u}} {F G G' : A ⟶ E}
    (h : G = G') (H : SSet.Homotopy F G) (a : FunctorHom F G')
    (ha : HEq a (homMk (functorEdgeOfSimplicialHomotopy H))) (k : A _⦋0⦌) :
    Arrow.mk (functorHomEvaluate a k) =
      Arrow.mk (homMk (simplicialHomotopyVertexEdge H k).toTruncated) := by
  subst G'
  have ha' := eq_of_heq ha
  rw [ha', functorHomEvaluate_homotopy]

private theorem relativeCechDiagonal_component {C : Type u} [SmallCategory C]
    {P Q : Cᵒᵖ ⥤ Type u} (g : P ⟶ Q) (j : AsSmall.{u} SimplexCategoryᵒᵖ)
    {E : SSet.{u + 1}} [Quasicategory E] (O : Presheaf C E)
    (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E) :
    let L := SerrePositivity.InfinityCategories.Sheaves.weightedSections O hE
    let k : cechReverseIndex.{u} _⦋0⦌ := SSet.opObjEquiv.symm (ULift.up (nerveVertex j))
    let I := (discretePresheafInclusion C).val
    let b := edgeOp ((nerve.edgeMk ((relativeCechDiagonal g).app j)).map I).toTruncated
    Arrow.mk (functorHomEvaluate (weightedSections_relativeCechDiagonalHom g O hE) k) =
      Arrow.mk (homMk (b.map ((truncation 2).map L))) := by
  intro L k I b
  let t := discreteRelativeCechDiagonalHomotopy g
  let H := functorHomotopyPostcomp (homotopyOpposite t) L
  have ht : SSet.opFunctor.map (SSet.const (X := ((SSet.uliftFunctor.{u + 1, u}).obj
      (nerve (AsSmall.{u} SimplexCategoryᵒᵖ)))) (functorVertex (discretePresheaf P))) ≫ L =
      (SSet.const
      (L.app _ (opObjEquiv.symm (functorVertex (discretePresheaf P)))) : cechReverseIndex.{u} ⟶ E) := by
    change (SSet.const (SSet.opObjEquiv.symm
      (functorVertex (discretePresheaf P))) : cechReverseIndex.{u} ⟶ _) ≫ L = _
    rw [SSet.const_comp]
  have he : HEq (weightedSections_relativeCechDiagonalHom g O hE)
      (homMk (functorEdgeOfSimplicialHomotopy H)) := by
    unfold weightedSections_relativeCechDiagonalHom
    exact cast_heq _ _
  have h₀ := evaluateHomotopy_cast_target ht H _ he k
  refine h₀.trans (congr_arrowMk_homMk _ _ ?_)
  have hv := kanHomotopyOpposite_vertex_edge t (ULift.up (nerveVertex j))
  change L.app (Opposite.op ⦋1⦌)
    (simplicialHomotopyVertexEdge (homotopyOpposite t) k).edge =
      L.app (Opposite.op ⦋1⦌) b.edge
  apply congrArg (L.app (Opposite.op ⦋1⦌))
  change (simplicialHomotopyVertexEdge (homotopyOpposite t) k).edge =
    SSet.opObjEquiv.symm (((nerve.edgeMk ((relativeCechDiagonal g).app j)).map I).edge)
  exact hv.trans (congrArg SSet.opObjEquiv.symm
    (discreteRelativeCechDiagonalHomotopy_component g j))


private lemma iso_of_arrow_eq {D : Type*} [Category* D]
    {a b x y : D} {f : a ⟶ b} {g : x ⟶ y}
    (h : Arrow.mk f = Arrow.mk g) (hg : IsIso g) : IsIso f := by
  obtain ⟨rfl, rfl, hh⟩ := (Arrow.mk_eq_mk_iff _ _).mp h
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hh
  exact hh.symm ▸ hg

/-- 元の相対 Čech 対角の成分は、同じ要素圏上の指定切断の写像の可逆性を受け継ぐ。 -/
@[cite HTT "6.2.2.6" (partial := special)
  "小さい通常の site の集合値重みの Čech 対角の成分。"]
lemma weightedSections_relativeCechDiagonalHom_component_isIso
    {C : Type u} [SmallCategory C] {E : SSet.{u + 1}} [Quasicategory E]
    (J : GrothendieckTopology C) {P Q : Cᵒᵖ ⥤ Type u} (f : P ⟶ Q)
    [CategoryTheory.Presheaf.IsLocallyInjective J f]
    (O : Presheaf C E) (hO : IsSheaf J O)
    (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E)
    (j : cechReverseIndex.{u} _⦋0⦌) :
    IsIso (functorHomEvaluate (weightedSections_relativeCechDiagonalHom f O hE) j) := by
  let v := (SSet.opObjEquiv j).down
  let j₀ : AsSmall.{u} SimplexCategoryᵒᵖ := nerveEquiv v
  have hv : nerveVertex j₀ = v := nerveEquiv.left_inv v
  have hj : SSet.opObjEquiv.symm (ULift.up (nerveVertex j₀)) = j := by
    rw [hv]
    exact SSet.opObjEquiv.symm_apply_apply j
  rw [← hj]
  let D := (relativeCechDiagram f).obj j₀
  let φ : P ⟶ D := (relativeCechDiagonal f).app j₀
  let hP := sectionsOfDiagram_hasLimit hE P O
  let hD := sectionsOfDiagram_hasLimit hE D O
  let e := (nerve.edgeMk φ).map (discretePresheafInclusion C).val
  let r := (edgeOp e.toTruncated).map ((truncation 2).map (weightedSections O hE))
  let eP := (weightedSections_discrete O hE P hP).hom
  let eD := (weightedSections_discrete O hE D hD).hom
  let m := homMk (sectionsOf_map φ O hP hD).toTruncated
  letI : IsIso m := relativeCechDiagonal_sections_isInvertible J f j₀ O hO hP hD
  letI : IsIso eP := inferInstanceAs (IsIso (weightedSections_discrete O hE P hP).hom)
  letI : IsIso eD := inferInstanceAs (IsIso (weightedSections_discrete O hE D hD).hom)
  have hr : homMk r ≫ eP = eD ≫ m := weightedSections_discrete_map O hE φ hP hD
  have hcomp : IsIso (homMk r ≫ eP) := hr.symm ▸ inferInstanceAs (IsIso (eD ≫ m))
  have hi := (isIso_comp_right_iff (homMk r) eP).mp hcomp
  exact iso_of_arrow_eq (relativeCechDiagonal_component f j₀ O hE) hi

end SerrePositivity.InfinityCategories.Sheaves
