module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.CovariantRepresentableCosliceComparison
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.PointCosliceIsoTransportComparison
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.CosliceTransportRightMappingComparison
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FamilyEquivalenceReflection

/-!
概要：元の共変表現可能値の同じ比較と標準後合成の全族自然性。
方針：反転 coslice の値比較の上で輸送を照合し、同じ同値で全族同型を反映する。
規約：対象ごとに別の同値へ置き換えない。
使われ方：G8 の四角形②の表現可能値の因子。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories
open TheSliceAndJoinConstructions MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
open SerrePositivity.InfinityCategories.Project.FilteredExchange

namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding

/-- 概要：元の共変表現可能値の比較は、同じ指定辺の値の作用と標準後合成を全族で結ぶ。
方針：同じ反転 coslice の比較、二重反転の輸送、右写像空間比較を合成して反映する。
規約：元の比較の順射を保持し、必要な同型を仮定しない。
使われ方：G8 の選ばれた表現可能値の比較の自然性。 -/
def covariantRepresentableValue_postcomposeIso {C : SSet.{u}} [Quasicategory C]
    (x : C _⦋0⦌) {a b : C _⦋0⦌} (e : C.Edge a b) :
    FunctorIso
      (spaceInfinityEdgeValue
        ((SSet.Edge.ofTruncated (uliftTruncatedEdge.{u, u + 1} e)).map
          (covariantRepresentableInfinity x)) ≫
            (covariantRepresentableValueEquivalence x b).hom)
      ((covariantRepresentableValueEquivalence x a).hom ≫
        postcompose x (SSet.Truncated.HomotopyCategory.homMk e)) := by
  letI : Quasicategory ((SSet.opFunctor ⋙ SSet.opFunctor).obj C) :=
    inferInstanceAs (Quasicategory C.op.op)
  letI : Quasicategory ((𝟭 SSet).obj C) := inferInstanceAs (Quasicategory C)
  let d := SSet.opFunctorCompOpFunctorIso.app C
  let e' := e.map d.inv
  let z := SSet.opObjEquiv.symm x
  let v := fun c : C _⦋0⦌ => reversedRepresentableValueEquivalence (B := C.op) z
    (SSet.opObjEquiv.symm (SSet.opObjEquiv.symm c))
  let f := fun c : C _⦋0⦌ => covariantRepresentableValueEquivalence x c
  let K := fun c : C _⦋0⦌ => pointCosliceFiberMap d.hom
    (SSet.opObjEquiv.symm (SSet.opObjEquiv.symm x))
    (SSet.opObjEquiv.symm (SSet.opObjEquiv.symm c))
  let R := fun c : C _⦋0⦌ => (cosliceFiberRightMappingEquivalence x c).hom
  let T := edgeTransport (sliceUnderProjection (SSet.yonedaEquiv.symm
    (SSet.opObjEquiv.symm (SSet.opObjEquiv.symm x)))) e'
  let w := spaceInfinityEdgeValue
    ((SSet.Edge.ofTruncated (uliftTruncatedEdge.{u, u + 1} e)).map
      (covariantRepresentableInfinity x))
  let post := postcompose x (SSet.Truncated.HomotopyCategory.homMk e)
  have he : e'.map d.hom = e := by
    apply SSet.Edge.ext
    change (d.inv ≫ d.hom).app (Opposite.op ⦋1⦌) e.edge = e.edge
    rw [Iso.inv_hom_id]
    rfl
  have hve : ((SSet.Edge.ofTruncated (uliftTruncatedEdge.{u, u + 1} e')).map
      (representablePresheafInfinity (C := C.op) z)) =
      ((SSet.Edge.ofTruncated (uliftTruncatedEdge.{u, u + 1} e)).map
        (covariantRepresentableInfinity x)) := by
    apply SSet.Edge.ext
    rfl
  have hv : FunctorIso (T ≫ (v b).hom) ((v a).hom ≫ w) := by
    have h := reversedRepresentableValueTransportIso (B := C.op) z e'
    rw [hve] at h
    exact h
  have hk : FunctorIso (T ≫ K b)
      (K a ≫ edgeTransport (sliceUnderProjection (SSet.yonedaEquiv.symm x)) e) := by
    have h := pointCosliceIso_transportIso d
      (SSet.opObjEquiv.symm (SSet.opObjEquiv.symm x)) e'
    rw [he] at h
    exact h
  apply functorIsoOfPrecompEquivalence (v a).hom (v a).isQCatEquivalence
  have h₁ := FunctorIso.postcomp hv.symm (f b).hom
  have h₂ := FunctorIso.precomp (covariantRepresentableValue_cosliceIso x b) T
  have h₃ := FunctorIso.postcomp hk (R b)
  have h₄ := FunctorIso.precomp (cosliceTransport_rightMappingIso x e) (K a)
  have h₅ := FunctorIso.postcomp (covariantRepresentableValue_cosliceIso x a).symm post
  simp only [Category.assoc] at h₁ h₂ h₃ h₄ h₅
  exact h₁ ≪≫ h₂ ≪≫ h₃ ≪≫ h₄ ≪≫ h₅

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
