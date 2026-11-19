module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Sheaves.DiscretePresheafHom
public import SerrePositivity.InfinityCategories.Sheaves.DiscretePresheafInclusion
public import SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.SetWeightRelativeUniverse
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.HomotopyTransformationClassIso
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpaceIntervalVertices
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SmallUnstraighteningIsoHom
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftUnstraighteningEdgeLiftFamily
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.EdgeRepresentativeLift
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.UniverseVertexIso
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SmallTransportRepresentationArrowPrism

/-!
概要：指定された離散前層の射の作用を小さい要素圏で計算する。
方針：同じ変換の辺の類を比較し、G8 の相対自然性を元の宇宙へ戻す。
規約：HTT 5.1.5.6（双対）、Kerodon 5.6.0.6（Tag 028T）の指定作用。
使われ方：離散重みに沿う重み付き切断の比較。
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories
open SerrePositivity.InfinityCategories.Project.SetWeightedTensors
open SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
open SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries
namespace SerrePositivity.InfinityCategories.Sheaves

/-- 元の離散前層の射と要素の圏による制限を、同じ底上の相対写像空間で比較する。 -/
@[cite HTT "5.1.5.6" (partial := special) "小さい通常の site の集合値重みの指定作用。"]
lemma discreteElementsComparison_specifiedHom :
∀ {C : Type u} [SmallCategory C] {P Q : Cᵒᵖ ⥤ Type u} (φ : P ⟶ Q),
let q := smallLeftUnstraighteningProjection (discretePresheaf Q)
let a := SetWeight.elementsComparisonNatural P ≫ smallUnstraighteningFunctorHom (discretePresheafHom φ)
let b := nerveMap φ.mapElements ≫ SetWeight.elementsComparisonNatural Q
∃ (ha : a ≫ q = SetWeight.projection P) (hb : b ≫ q = SetWeight.projection P),
 Nonempty (VertexIso (relativeFunctorVertex q (SetWeight.projection P) a ha)
   (relativeFunctorVertex q (SetWeight.projection P) b hb)) := by
  intro C hC P Q φ
  dsimp only
  let U := SSet.uliftFunctor.{u + 1, u}
  let F := discretePresheaf P
  let G := discretePresheaf Q
  let p := SetWeight.projection P
  let q := smallLeftUnstraighteningProjection G
  let q' := leftUnstraighteningProjection G
  let α := discretePresheafHom φ
  let e := SetWeight.spaceDiagramEdge φ
  let r := SetWeight.elementsComparisonNatural P
  let a := r ≫ smallUnstraighteningFunctorHom α
  let b := nerveMap φ.mapElements ≫ SetWeight.elementsComparisonNatural Q
  have ha : a ≫ q = p := by
    rw [show a = r ≫ smallUnstraighteningFunctorHom α from rfl, Category.assoc]
    have hh : smallUnstraighteningFunctorHom α ≫ q = smallLeftUnstraighteningProjection F :=
      smallUnstraighteningFunctorHom_projection α
    rw [hh]
    exact SetWeight.elementsComparisonNatural_projection P
  have hb : b ≫ q = p := by
    dsimp only [b]
    have hh : SetWeight.elementsComparisonNatural Q ≫ q = SetWeight.projection Q :=
      SetWeight.elementsComparisonNatural_projection Q
    rw [Category.assoc, hh]
    rfl
  refine ⟨ha, hb, ?_⟩
  have he : Truncated.HomotopyCategory.homMk e.toTruncated = α := by
    apply congrArg Truncated.HomotopyCategory.homMk
    apply Truncated.Edge.ext
    change (SetWeight.spaceDiagramEdge φ).edge =
      ((nerve.edgeMk φ).map (kanDiscretePresheafMap C)).edge
    exact (kanDiscretePresheafMap_edge φ).symm
  let M := setWeightRelativeUniverseIso P G
  have hv (v : nerve P.Elements ⟶ smallLeftUnstraightening G) (h : v ≫ q = p) :
      M.hom.app (Opposite.op ⦋0⦌) (ULift.up (relativeFunctorVertex q p v h)) =
        relativeFunctorVertex q' (U.map p) (U.map v ≫ (smallLeftUnstraighteningIso G).hom)
          (by
            rw [Category.assoc, smallLeftUnstraighteningIso_projection, ← U.map_comp, h]) := by
    change (relativeFunctorOverIso (Iso.refl (Over.mk (U.map p)))
      (smallLeftUnstraighteningOverIso G)).hom.app _
        ((uliftRelativeFunctorMap q p).app _ (ULift.up (relativeFunctorVertex q p v h))) = _
    rw [uliftRelativeFunctorMap_vertex]
    have h' : U.map v ≫ U.map q = U.map p := by rw [← U.map_comp, h]
    refine (relativeFunctorOverIso_vertex (Iso.refl (Over.mk (U.map p)))
      (smallLeftUnstraighteningOverIso G) (U.map v) h').trans ?_
    apply Subtype.ext
    apply congrArg functorVertex
    change (𝟙 _ ≫ U.map v) ≫ (smallLeftUnstraighteningIso G).hom = _
    rw [Category.id_comp]
  let c := leftUnstraighteningMappingSpaceMap F G
  let e' := smallUnstraighteningHomEdge α
  have hclass : Truncated.HomotopyCategory.homMk e'.toTruncated =
      Truncated.HomotopyCategory.homMk e.toTruncated :=
    (smallUnstraighteningHomEdge_hom α).trans he.symm
  obtain ⟨w⟩ := exists_kanPinchedHomEdge_of_homMk_eq e'.toTruncated e.toTruncated hclass
  let comp := pinchedHomToIntervalMappingSpace (functorVertex F) (functorVertex G)
  obtain ⟨wi₀⟩ := nonempty_vertexIso_of_piZero_eq (SSet.π₀.sound w)
  have wi := (wi₀.map comp).map c
  dsimp only [comp] at wi
  rw [pinchedHomToIntervalMappingSpace_vertex, pinchedHomToIntervalMappingSpace_vertex,
    Equiv.apply_symm_apply, Equiv.apply_symm_apply] at wi
  let s := setWeightElementsUnstraightening P
  let preS : Over.mk (U.map p) ⟶ Over.mk (leftUnstraighteningProjection F) :=
    Over.homMk s (setWeightElementsUnstraightening_projection P)
  have hbigA : U.map a ≫ (smallLeftUnstraighteningIso G).hom =
      s ≫ unstraighteningFunctorHom α := by
    dsimp only [a]
    rw [U.map_comp, Category.assoc, smallUnstraighteningFunctorHom_naturality]
    rfl
  have hbigB : U.map b ≫ (smallLeftUnstraighteningIso G).hom =
      U.map (nerveMap φ.mapElements) ≫ setWeightElementsUnstraightening Q := by
    dsimp only [b]
    rw [U.map_comp, Category.assoc]
    rfl
  have hpA := (hv a ha)
  have hpB := (hv b hb)
  have wA := leftUnstraighteningMappingVertexMap_vertex F G (intervalMappingVertexOfEdge e')
  have wB := leftUnstraighteningEdgeLiftMap_vertex F G e
  have nA := relativeFunctorOverPre_vertex q' preS (unstraighteningFunctorHom α)
    (unstraighteningFunctorHom_projection α)
  have nB := relativeFunctorOverPre_vertex q' preS (leftUnstraighteningEdgeLiftMap F G e)
    (leftUnstraighteningEdgeLiftMap_projection F G e)
  let V := relativeFunctorOverPre q' preS
  have hA : V.app _ (c.app _ (intervalMappingVertexOfEdge e')) =
      M.hom.app _ (ULift.up (relativeFunctorVertex q p a ha)) := by
    refine (congrArg (fun x => V.app (Opposite.op ⦋0⦌) x) wA.symm).trans
      (nA.trans (Eq.trans ?_ hpA.symm))
    apply Subtype.ext
    exact congrArg functorVertex hbigA.symm
  have hB : V.app _ (c.app _ (intervalMappingVertexOfEdge e)) =
      relativeFunctorVertex q' (U.map p) (s ≫ leftUnstraighteningEdgeLiftMap F G e)
        (by
          rw [Category.assoc, leftUnstraighteningEdgeLiftMap_projection]
          exact setWeightElementsUnstraightening_projection P) :=
    (congrArg (fun x => V.app (Opposite.op ⦋0⦌) x) wB).trans nB
  have hQ := setWeightElementsUnstraightening_naturality φ
  have hQ' :
      relativeFunctorVertex q' (U.map p)
        (U.map (nerveMap φ.mapElements) ≫ setWeightElementsUnstraightening Q)
        (setWeightElementsUnstraightening_map_projection φ) =
      M.hom.app _ (ULift.up (relativeFunctorVertex q p b hb)) := by
    rw [hpB]
    apply Subtype.ext
    exact congrArg functorVertex hbigB.symm
  let wi' : VertexIso (c.app _ (intervalMappingVertexOfEdge e))
      (c.app _ (intervalMappingVertexOfEdge e')) := wi
  let iso := (eqToIso (congrArg HomotopyCategory.mk hA)).symm ≪≫ (wi'.map V).symm ≪≫
    eqToIso (congrArg HomotopyCategory.mk hB) ≪≫ hQ ≪≫
    eqToIso (congrArg HomotopyCategory.mk hQ')
  exact ⟨downVertexIso ((qCatEquivalenceOfIso M).isFullyFaithful.preimageVertexIso iso)⟩

end SerrePositivity.InfinityCategories.Sheaves
