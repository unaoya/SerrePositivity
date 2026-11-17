module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.TransportRepresentationArrowPrism

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportRepresentationUnstraighteningComparison
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SmallLeftUnstraighteningLift
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorOverIsomorphism
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SmallLeftUnstraighteningMappingSpace
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.UniverseVertexIso
/-!
概要：同じ指定pointed prismで表現された全空間の射を、小さいunstraighteningの作用へ戻す。
方針：大きい宇宙での既存比較の零次成分を、元のuliftと縮小の相対関手空間の同型で反映する。
規約：HTT §3.3.2、Kerodon Remark 5.6.2.18（Tag 0271）の既存構成の照合。
使われ方：R04-PR。指定分類同型と元の底上の射aの双方を保持する。
-/

@[expose] public noncomputable section
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
open SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
/-- 指定prismによる比較は、元の小さい相対写像空間で同じ射aを回収する。 -/
@[cite HTT "3.3.2" (partial := special) "同じpointed prismの比較を小さい相対写像空間の同型で反映する法則。"]
lemma smallTransportRepresentation_arrowPrismComparison {E F B : SSet.{u}} (p : E ⟶ B) (qF : F ⟶ B)
    [LeftFibration p] [LeftFibration qF]
    (R : LeftTransportRepresentation ((SSet.uliftFunctor.{u + 1, u}).map p))
    (S : LeftTransportRepresentation ((SSet.uliftFunctor.{u + 1, u}).map qF))
    (a : E ⟶ F) (ha : a ≫ qF = p) (ν : FunctorIso R.diagram S.diagram)
    (W : (Δ[1] : SSet.{u + 1}) ⊗ (SSet.uliftFunctor.{u + 1, u}).obj E ⟶ PointedSpaceInfinity.{u})
    (h₀ : prismEndpoint 0 ((SSet.uliftFunctor.{u + 1, u}).obj E) ≫ W = R.pointedMap)
    (h₁ : prismEndpoint 1 ((SSet.uliftFunctor.{u + 1, u}).obj E) ≫ W =
      (SSet.uliftFunctor.{u + 1, u}).map a ≫ S.pointedMap)
    (hW : W ≫ pointedSpaceProjection =
      (Δ[1] ◁ (SSet.uliftFunctor.{u + 1, u}).map p) ≫
        functorEdgePrism (SSet.Edge.ofTruncated (functorEdgeOfSimplicialHomotopy
          (functorHomHomotopy ν.hom)))) :
    let rR := smallLeftUnstraighteningLift R.diagram R.comparison
    let rS := smallLeftUnstraighteningLift S.diagram S.comparison
    let z := rR ≫ smallUnstraighteningFunctorHom ν.hom
    ∃ (hz : z ≫ smallLeftUnstraighteningProjection S.diagram = p)
      (ht : (a ≫ rS) ≫ smallLeftUnstraighteningProjection S.diagram = p),
      Nonempty (VertexIso
        (relativeFunctorVertex (smallLeftUnstraighteningProjection S.diagram) p z hz)
        (relativeFunctorVertex (smallLeftUnstraighteningProjection S.diagram) p (a ≫ rS) ht)) := by
  dsimp only
  let U := SSet.uliftFunctor.{u + 1, u}
  let c := ν.hom
  let q := smallLeftUnstraighteningProjection S.diagram
  let rR := smallLeftUnstraighteningLift R.diagram R.comparison
  let rS := smallLeftUnstraighteningLift S.diagram S.comparison
  have hr : rR ≫ smallLeftUnstraighteningProjection R.diagram = p :=
    smallLeftUnstraighteningLift_projection R.diagram p R.comparison R.over_base
  have hs : rS ≫ q = qF := smallLeftUnstraighteningLift_projection S.diagram qF S.comparison S.over_base
  let target := a ≫ rS
  have ht : target ≫ q = p := by rw [Category.assoc, hs, ha]
  let f := rR ≫ smallUnstraighteningFunctorHom c
  have hf : f ≫ q = p := by
    dsimp only [f, q]
    rw [Category.assoc, smallUnstraighteningFunctorHom_projection, hr]
  refine ⟨hf, ht, ?_⟩
  have hh := transportRepresentation_arrowPrismComparison (U.map p) (U.map qF) R S
    (U.map a) (by rw [← U.map_comp, ha]) ν W h₀ h₁ hW
  dsimp only at hh
  obtain ⟨hb, htb, ⟨eb⟩⟩ := hh
  haveI : Quasicategory (relativeFunctorSpace (leftUnstraighteningProjection S.diagram) (U.map p)) := inferInstance
  haveI : Quasicategory (relativeFunctorSpace q p) := by
    dsimp only [q]
    infer_instance
  let M : U.obj (relativeFunctorSpace q p) ≅
      relativeFunctorSpace (leftUnstraighteningProjection S.diagram) (U.map p) :=
    uliftRelativeFunctorIso.{u, u + 1} q p ≪≫
    relativeFunctorOverIso (Iso.refl (Over.mk (U.map p))) (smallLeftUnstraighteningOverIso S.diagram)
  have hm (v : E ⟶ smallLeftUnstraightening S.diagram) (hv : v ≫ q = p) :
      M.hom.app (Opposite.op ⦋0⦌) (ULift.up (relativeFunctorVertex q p v hv)) =
      relativeFunctorVertex (leftUnstraighteningProjection S.diagram) (U.map p)
        (U.map v ≫ (smallLeftUnstraighteningIso S.diagram).hom)
        (by
          rw [Category.assoc,
            show (smallLeftUnstraighteningIso S.diagram).hom ≫
              leftUnstraighteningProjection S.diagram = U.map q from
                (smallLeftUnstraighteningOverIso S.diagram).hom.w,
            ← U.map_comp, hv]) := by
    change (relativeFunctorOverIso (Iso.refl (Over.mk (U.map p)))
      (smallLeftUnstraighteningOverIso S.diagram)).hom.app _
        ((uliftRelativeFunctorMap q p).app _ (ULift.up (relativeFunctorVertex q p v hv))) = _
    rw [uliftRelativeFunctorMap_vertex]
    have he := relativeFunctorOverIso_vertex (Iso.refl (Over.mk (U.map p)))
      (smallLeftUnstraighteningOverIso S.diagram) (U.map v)
      (by
        change U.map v ≫ U.map q = U.map p
        rw [← U.map_comp, hv])
    refine he.trans ?_
    apply Subtype.ext
    apply congrArg functorVertex
    change (𝟙 _ ≫ U.map v) ≫ (smallLeftUnstraighteningIso S.diagram).hom = _
    rw [Category.id_comp]
  have hfr : U.map f ≫ (smallLeftUnstraighteningIso S.diagram).hom =
      R.comparison ≫ unstraighteningFunctorHom c := by
    dsimp only [f, rR]
    rw [U.map_comp, Category.assoc, smallUnstraighteningFunctorHom_naturality,
      ← Category.assoc, smallLeftUnstraighteningLift_naturality]
  have hvf : M.hom.app (Opposite.op ⦋0⦌) (ULift.up (relativeFunctorVertex q p f hf)) =
      relativeFunctorVertex (leftUnstraighteningProjection S.diagram) (U.map p)
        (R.comparison ≫ unstraighteningFunctorHom c) hb := by
    rw [hm]
    apply Subtype.ext
    exact congrArg functorVertex hfr
  have hvs : M.hom.app (Opposite.op ⦋0⦌) (ULift.up (relativeFunctorVertex q p target ht)) =
      relativeFunctorVertex (leftUnstraighteningProjection S.diagram) (U.map p)
        (U.map a ≫ S.comparison) htb := by
    rw [hm]
    apply Subtype.ext
    apply congrArg functorVertex
    dsimp only [target]
    rw [U.map_comp, Category.assoc, smallLeftUnstraighteningLift_naturality]
  let eu := (qCatEquivalenceOfIso M).isFullyFaithful.preimageVertexIso
    (eqToIso (congrArg HomotopyCategory.mk hvf) ≪≫ eb ≪≫
      (eqToIso (congrArg HomotopyCategory.mk hvs)).symm)
  exact ⟨downVertexIso eu⟩


end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
