module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.ElementsYonedaSliceInterval
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpaceIntervalVertices
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconeVertexTriangles

/-!
概要：元の Yoneda comma の区間頂点は、指定した密度余錐の実際の脚を表す。
方針：元の余錐の展開を指定した頂点へ制限する。
使われ方：離散前層の密度の脚の自然性。
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
open SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding

namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories

variable {C : SSet.{u}} [Quasicategory C]
  (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u}) (x : C _⦋0⦌)

/-- 元の Yoneda comma の区間頂点は、指定した密度余錐の実際の脚を表す。
Kerodon §9.3（Tag 06FR）の密度比較。HTT 5.1.5.6 へ使う指定脚の照合。 -/
lemma presheafElementsYonedaSliceInterval_at_leg
    (s : (vertexFiber (smallRightUnstraighteningProjection F) x) _⦋0⦌) :
    (presheafElementsYonedaSliceInterval F x).app (Opposite.op ⦋0⦌) (ULift.up s) =
      intervalMappingVertexOfEdge
        ((coconeVertexLeg (presheafDensityCocone F) (ULift.up s.val)).ofEq
          (by
            have h : (smallRightUnstraighteningProjection F).app (Opposite.op ⦋0⦌) s.val = x :=
              s.property.trans (pinchedConstant_zero x)
            change (yonedaInfinityMap C).app (Opposite.op ⦋0⦌)
              (ULift.up ((smallRightUnstraighteningProjection F).app
                (Opposite.op ⦋0⦌) s.val)) = _
            rw [h, yonedaInfinityMap_vertex]) (presheafDensityCocone_vertex F)) := by
  let A := presheafDensityFiberParameter F x
  let W := presheafDensityElementsParameter F
  let z := functorVertex F
  let y := functorVertex (representablePresheafInfinity x)
  let i := presheafDensityFiberParameterInclusion F x
  let v : A _⦋0⦌ := ULift.up s
  let k := SSet.yonedaEquiv.symm v
  let R := presheafElementsYonedaSliceMapping F x
  let T := (pinchedHomSliceFiberIso y z).hom
  let j := vertexFiberι (sliceOverProjection (SSet.yonedaEquiv.symm z)) y
  let w := R.app (Opposite.op ⦋0⦌) v
  have h : sliceOverUncurry (R ≫ T ≫ j) =
      joinMap i (𝟙 Δ[0]) ≫ (presheafDensityCocone F).val :=
    presheafElementsYonedaSliceMapping_uncurry F x
  have hh := congrArg (fun f : join A (Δ[0] : SSet.{u + 1}) ⟶ PresheafInfinity C =>
    joinMap k (𝟙 Δ[0]) ≫ f) h
  rw [← sliceOverUncurry_precomp, ← Category.assoc, SSet.yonedaEquiv_symm_comp] at hh
  change sliceOverUncurry ((SSet.yonedaEquiv.symm w ≫ T) ≫ j) = _ at hh
  rw [SSet.yonedaEquiv_symm_comp, SSet.yonedaEquiv_symm_comp, sliceOverUncurry_yoneda] at hh
  have hC : joinMap k (𝟙 Δ[0]) ≫
      joinMap i (𝟙 Δ[0]) ≫ (presheafDensityCocone F).val =
      joinMap (SSet.yonedaEquiv.symm (ULift.up s.val : W _⦋0⦌)) (𝟙 Δ[0]) ≫
        (presheafDensityCocone F).val := by
    rw [← Category.assoc, ← joinMap_comp, Category.id_comp, SSet.yonedaEquiv_symm_comp]
    rfl
  rw [hC] at hh
  change (pinchedHomToIntervalMappingSpace y z).app (Opposite.op ⦋0⦌) w = _
  rw [pinchedHomToIntervalMappingSpace_vertex]
  apply congrArg intervalMappingVertexOfEdge
  apply Edge.ext
  have ht := congrArg (fun f : join (Δ[0] : SSet.{u + 1}) Δ[0] ⟶ PresheafInfinity C =>
    SSet.yonedaEquiv ((joinStdSimplexIso 0 0).inv ≫ f)) hh
  change SSet.yonedaEquiv ((joinStdSimplexIso 0 0).inv ≫
    ((joinStdSimplexIso 0 0).hom ≫ SSet.yonedaEquiv.symm w.val)) = _ at ht
  rw [Iso.inv_hom_id_assoc, Equiv.apply_symm_apply] at ht
  exact ht

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
