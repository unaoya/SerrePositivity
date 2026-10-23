module

public import SerrePositivity.InfinityCategories.HomotopyLimits.CosliceRestrictionOpposite
public import SerrePositivity.InfinityCategories.HomotopyLimits.RelativeSectionRestrictionOpposite
public import SerrePositivity.InfinityCategories.F1B.QuillenASliceOpposite
public import SerrePositivity.InfinityCategories.F1.RightFibrationYoneda
public import SerrePositivity.InfinityCategories.F1.RelativeFunctorRestrictionLifting
public import SerrePositivity.InfinityCategories.F1B.RightAnodyneTensor
public import SerrePositivity.InfinityCategories.F2.Presentable.LocalEdgeRestriction

/-!
概要：終点固定余錐の制限を切断の制限と照合し、元の辺の局所性を全境界充填へ移す。
方針：元の比較射の可換性と Kan な写像空間の同値判定を使う。
規約：底と全パラメータは任意。使われ方：HTT 5.5.4.5(2) の局所辺の族の制限。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 終点固定余錐の制限の同値性は、その頂点への slice 上の切断の制限と一致。 -/
lemma cosliceRestriction_homotopyEquivalence_iff_sections {J K X : SSet.{u}}
    [Quasicategory X] (p : J ⟶ X) (i : K ⟶ J) (z : X _⦋0⦌) :
    IsSimplicialHomotopyEquivalence (cosliceRestrictionFiberMap p i z) ↔
      IsSimplicialHomotopyEquivalence
        (relativeFunctorPre (sliceOverProjection (SSet.yonedaEquiv.symm z)) p i) := by
  rw [cosliceRestriction_homotopyEquivalence_iff_op_slice,
    sliceRestriction_homotopyEquivalence_iff_sections]
  rw [relativeFunctorPre_homotopyEquivalence_iff_op
    (sliceOverProjection (SSet.yonedaEquiv.symm z)) p i]
  have hs := kanComplex_of_iso
    (relativeFunctorOppositeIso (sliceOverProjection (SSet.yonedaEquiv.symm z)) p)
  have ht := kanComplex_of_iso
    (relativeFunctorOppositeIso (sliceOverProjection (SSet.yonedaEquiv.symm z)) (i ≫ p))
  have : KanComplex (relativeFunctorSpace
      (Over.mk (SSet.opFunctor.map (sliceOverProjection (SSet.yonedaEquiv.symm z)))).hom
      (SSet.opFunctor.map p)) := hs
  have : KanComplex (relativeFunctorSpace
      (Over.mk (SSet.opFunctor.map (sliceOverProjection (SSet.yonedaEquiv.symm z)))).hom
      (SSet.opFunctor.map i ≫ SSet.opFunctor.map p)) := ht
  exact (relativeFunctorPre_homotopyEquivalence_iff_totalIso (cofinalPointSliceOverOpIso z)
    (SSet.opFunctor.map p) (SSet.opFunctor.map i)).symm

/-- 右ファイブレーション上の相対関手空間の単射による制限も右ファイブレーション。 -/
instance relativeFunctorPre_rightFibration {A D E B : SSet.{u}}
    (p : E ⟶ B) [RightFibration p] (a : A ⟶ B) (i : D ⟶ A) [Mono i] :
    RightFibration (relativeFunctorPre p a i) where
  mem := by
    let r := CategoryTheory.Functor.PullbackObjObj.ofHasPullback internalHom i p
    have := cofinalRightFibration_pullbackObjObjπ i p r
    intro T U j hj
    have := RightFibration.mem (p := r.π) j hj
    exact hasLiftingProperty_relativeFunctorPre p a i r j

/-- 元の辺への局所性は、その辺上の slice の切断の始点制限の同値性と一致。 -/
lemma isLocalForHom_edge_iff_sectionRestriction {X : SSet.{u}} [Quasicategory X]
    (e : (Δ[1] : SSet.{u}) ⟶ X) (z : X _⦋0⦌) :
    IsLocalForHom (SSet.Truncated.HomotopyCategory.homMk (edgeCosliceEdge e)) z ↔
      IsSimplicialHomotopyEquivalence
        (relativeFunctorPre (sliceOverProjection (SSet.yonedaEquiv.symm z)) e
          (stdSimplex.δ (1 : Fin 2))) := by
  have := vertexFiber_kanComplex_of_leftFibration (sliceUnderProjection e) z
  have := vertexFiber_kanComplex_of_leftFibration
    (sliceUnderProjection (stdSimplex.δ (1 : Fin 2) ≫ e)) z
  rw [isLocalForHom_edge_iff_sourceRestriction,
    ← isSimplicialHomotopyEquivalence_iff_isQCatEquivalence,
    cosliceRestriction_homotopyEquivalence_iff_sections]

/-- 元の辺への局所性は、その辺上の slice の切断の始点制限の全境界充填性と一致。 -/
lemma isLocalForHom_edge_iff_sectionRestriction_trivial {X : SSet.{u}} [Quasicategory X]
    (e : (Δ[1] : SSet.{u}) ⟶ X) (z : X _⦋0⦌) :
    IsLocalForHom (SSet.Truncated.HomotopyCategory.homMk (edgeCosliceEdge e)) z ↔
      TrivialKanFibration
        (relativeFunctorPre (sliceOverProjection (SSet.yonedaEquiv.symm z)) e
          (stdSimplex.δ (1 : Fin 2))) := by
  rw [isLocalForHom_edge_iff_sectionRestriction]
  constructor
  · intro h
    exact trivialKanFibration_of_fibration_of_simplicialHomotopyEquivalence _ h
  · intro h
    have := h
    exact (isQCatEquivalence_of_trivialKanFibration _).isSimplicialHomotopyEquivalence

end SerrePositivity.InfinityCategories.HomotopyLimits
