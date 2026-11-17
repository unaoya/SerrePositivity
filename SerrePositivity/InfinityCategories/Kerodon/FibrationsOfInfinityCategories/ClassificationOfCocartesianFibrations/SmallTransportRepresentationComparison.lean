module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportRepresentationUnstraighteningComparison
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SmallLeftUnstraighteningLift
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorOverIsomorphism
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SmallLeftUnstraighteningMappingSpace
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.UniverseVertexIso
/-!
概要：同じ表現のunstraightening比較を、元の小さい全空間の相対写像空間へ降ろす。
方針：指定した縮小同型と相対内部Homの同型で前後を移し、同じ二射の頂点同型を反映する。
規約：Kerodon Remark 5.6.2.18（Tag 0271）、HTT §3.3.2の既存構成の宇宙移送の法則。
  元の比較射・底の等式・指定した図式同型を保持する。
使われ方：5∞-1の残り第2項の証明分割。元の復元比較への接続。
-/

@[expose] public noncomputable section
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
open SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
/-- 同じ表現空間の比較は、指定した小さい二射の相対頂点の同型を与える。 -/
lemma smallTransportRepresentation_unstraighteningComparison {E B : SSet.{u}} (p : E ⟶ B) [LeftFibration p]
    (R S : LeftTransportRepresentation ((SSet.uliftFunctor.{u + 1, u}).map p))
    (h : VertexIso (transportWitnessVertex R) (transportWitnessVertex S)) :
    let a := (R.diagramIso S h).hom
    let f := smallLeftUnstraighteningLift R.diagram R.comparison ≫ smallUnstraighteningFunctorHom a
    ∃ hf : f ≫ smallLeftUnstraighteningProjection S.diagram = p,
      Nonempty (VertexIso
        (relativeFunctorVertex (smallLeftUnstraighteningProjection S.diagram) p f hf)
        (relativeFunctorVertex (smallLeftUnstraighteningProjection S.diagram) p
          (smallLeftUnstraighteningLift S.diagram S.comparison)
          (smallLeftUnstraighteningLift_projection S.diagram p S.comparison S.over_base))) := by
  dsimp only
  let U := SSet.uliftFunctor.{u + 1, u}
  let a := (R.diagramIso S h).hom
  let q := smallLeftUnstraighteningProjection S.diagram
  let rR := smallLeftUnstraighteningLift R.diagram R.comparison
  let rS := smallLeftUnstraighteningLift S.diagram S.comparison
  have hr : rR ≫ smallLeftUnstraighteningProjection R.diagram = p :=
    smallLeftUnstraighteningLift_projection R.diagram p R.comparison R.over_base
  have hs : rS ≫ q = p := smallLeftUnstraighteningLift_projection S.diagram p S.comparison S.over_base
  let f := rR ≫ smallUnstraighteningFunctorHom a
  have hf : f ≫ q = p := by
    dsimp only [f, q]
    rw [Category.assoc, smallUnstraighteningFunctorHom_projection, hr]
  refine ⟨hf, ?_⟩
  have hh := transportRepresentation_unstraighteningComparison R S h
  change ∃ hb : (R.comparison ≫ unstraighteningFunctorHom a) ≫
      leftUnstraighteningProjection S.diagram = U.map p,
    Nonempty (VertexIso
      (relativeFunctorVertex (leftUnstraighteningProjection S.diagram) (U.map p)
        (R.comparison ≫ unstraighteningFunctorHom a) hb)
      (relativeFunctorVertex (leftUnstraighteningProjection S.diagram) (U.map p)
        S.comparison S.over_base)) at hh
  obtain ⟨hb, ⟨eb⟩⟩ := hh
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
      R.comparison ≫ unstraighteningFunctorHom a := by
    dsimp only [f, rR]
    rw [U.map_comp, Category.assoc, smallUnstraighteningFunctorHom_naturality,
      ← Category.assoc, smallLeftUnstraighteningLift_naturality]
  have hvf : M.hom.app (Opposite.op ⦋0⦌) (ULift.up (relativeFunctorVertex q p f hf)) =
      relativeFunctorVertex (leftUnstraighteningProjection S.diagram) (U.map p)
        (R.comparison ≫ unstraighteningFunctorHom a) hb := by
    rw [hm]
    apply Subtype.ext
    exact congrArg functorVertex hfr
  have hvs : M.hom.app (Opposite.op ⦋0⦌) (ULift.up (relativeFunctorVertex q p rS hs)) =
      relativeFunctorVertex (leftUnstraighteningProjection S.diagram) (U.map p)
        S.comparison S.over_base := by
    rw [hm]
    apply Subtype.ext
    exact congrArg functorVertex (smallLeftUnstraighteningLift_naturality S.diagram S.comparison)
  let eu := (qCatEquivalenceOfIso M).isFullyFaithful.preimageVertexIso
    (eqToIso (congrArg HomotopyCategory.mk hvf) ≪≫ eb ≪≫
      (eqToIso (congrArg HomotopyCategory.mk hvs)).symm)
  exact ⟨downVertexIso eu⟩

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
