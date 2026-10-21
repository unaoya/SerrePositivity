module

public import SerrePositivity.InfinityCategories.HomotopyLimits.SliceEndpointConeComparison
public import SerrePositivity.InfinityCategories.HomotopyLimits.ReflectedConeLimitLift
public import SerrePositivity.InfinityCategories.F1B.KanSliceProjectionLaws
public import SerrePositivity.InfinityCategories.F1.VertexFiberTotalIso
public import SerrePositivity.InfinityCategories.HomotopyLimits.OppositeVertexFiber
public import SerrePositivity.InfinityCategories.Stable.CoconeMappingRestriction

/-!
概要：余錐の反転同型を元の制限と頂点 fiber に対して自然に構成する。
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

/-- 余錐の反転比較は、元の図式への制限と厳密に可換。 -/
lemma cosliceOppositeIso_restrict {J K X : SSet.{u}} (p : J ⟶ X) (i : K ⟶ J) :
    SSet.opFunctor.map (sliceUnderRestrict p i) ≫ (F1B.kanSliceUnderOpIso (i ≫ p)).hom =
      (F1B.kanSliceUnderOpIso p).hom ≫
        sliceOverRestrict (SSet.opFunctor.map p) (SSet.opFunctor.map i) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  apply Subtype.ext
  change (F1B.kanSliceUnderOpObjEquiv (i ≫ p) ⦋n⦌
    ((SSet.opFunctor.map (sliceUnderRestrict p i)).app _ s)).val =
      joinMap (𝟙 (Δ[n] : SSet.{u})) (SSet.opFunctor.map i) ≫
        (F1B.kanSliceUnderOpObjEquiv p ⦋n⦌ s).val
  rw [F1B.kanSliceUnderOpObjEquiv_val, F1B.kanSliceUnderOpObjEquiv_val]
  have hs : (SSet.opObjEquiv
      ((SSet.opFunctor.map (sliceUnderRestrict p i)).app (Opposite.op ⦋n⦌) s)).val =
      joinMap i (𝟙 (Δ[n] : SSet.{u})) ≫ (SSet.opObjEquiv s).val := rfl
  rw [hs, SSet.opFunctor.map_comp]
  have hn := stableJoinReverse_inv_naturality i (𝟙 (Δ[n] : SSet.{u}))
  simp only [CategoryTheory.Functor.map_id] at hn
  rw [← reassoc_of% hn]
  simp only [← Category.assoc, ← joinMap_comp, Category.comp_id, Category.id_comp]

/-- 終点固定余錐の反転を、反転した図式の始点固定錐へ移す同型。 -/
def cosliceReverseFiberIso {J X : SSet.{u}} (p : J ⟶ X) (z : X _⦋0⦌) :
    (vertexFiber (sliceUnderProjection p) z).op ≅
      vertexFiber (sliceOverProjection (SSet.opFunctor.map p)) (SSet.opObjEquiv.symm z) :=
  oppositeVertexFiberIso _ z ≪≫ vertexFiberTotalIso _ _ (F1B.kanSliceUnderOpIso p)
    (F1B.kanSliceUnderOpIso_projection p) (SSet.opObjEquiv.symm z)

/-- 反転した余錐の fiber の同型は元の全空間への包含を保つ。 -/
lemma cosliceReverseFiberIso_ι {J X : SSet.{u}} (p : J ⟶ X) (z : X _⦋0⦌) :
    (cosliceReverseFiberIso p z).hom ≫
        vertexFiberι (sliceOverProjection (SSet.opFunctor.map p)) (SSet.opObjEquiv.symm z) =
      SSet.opFunctor.map (vertexFiberι (sliceUnderProjection p) z) ≫
        (F1B.kanSliceUnderOpIso p).hom := rfl

/-- 元の制限射を反転した fiber の同型は、錐の制限と厳密に可換。 -/
lemma cosliceReverseFiberIso_restrict {J K X : SSet.{u}} (p : J ⟶ X)
    (i : K ⟶ J) (z : X _⦋0⦌) :
    SSet.opFunctor.map (cosliceRestrictionFiberMap p i z) ≫
        (cosliceReverseFiberIso (i ≫ p) z).hom =
      (cosliceReverseFiberIso p z).hom ≫
        sliceRestrictionFiberMap (SSet.opFunctor.map p) (SSet.opObjEquiv.symm z)
          (SSet.opFunctor.map i) := by
  apply vertexFiber_hom_ext (sliceOverProjection (SSet.opFunctor.map (i ≫ p)))
    (SSet.opObjEquiv.symm z)
  rw [Category.assoc, cosliceReverseFiberIso_ι, ← Category.assoc,
    ← SSet.opFunctor.map_comp]
  rw [cosliceRestrictionFiberMap, vertexFiberMap_ι,
    SSet.opFunctor.map_comp (vertexFiberι (sliceUnderProjection p) z) (sliceUnderRestrict p i),
    Category.assoc, cosliceOppositeIso_restrict]
  have hr : sliceRestrictionFiberMap (SSet.opFunctor.map p) (SSet.opObjEquiv.symm z)
      (SSet.opFunctor.map i) ≫ vertexFiberι (sliceOverProjection (SSet.opFunctor.map (i ≫ p)))
        (SSet.opObjEquiv.symm z) =
      vertexFiberι (sliceOverProjection (SSet.opFunctor.map p)) (SSet.opObjEquiv.symm z) ≫
        sliceOverRestrict (SSet.opFunctor.map p) (SSet.opFunctor.map i) :=
    vertexFiberMap_ι _ _ _ _ _
  simp only [Category.assoc, hr]
  simpa only [Category.assoc] using
    (congrArg (fun t ↦ t ≫ sliceOverRestrict (SSet.opFunctor.map p) (SSet.opFunctor.map i))
      (cosliceReverseFiberIso_ι p z)).symm

/-- 元の余錐の制限の同値性は、反転した錐の制限の同値性と一致。 -/
lemma cosliceRestriction_homotopyEquivalence_iff_op_slice {J K X : SSet.{u}}
    [Quasicategory X] (p : J ⟶ X) (i : K ⟶ J) (z : X _⦋0⦌) :
    IsSimplicialHomotopyEquivalence (cosliceRestrictionFiberMap p i z) ↔
      IsSimplicialHomotopyEquivalence
        (sliceRestrictionFiberMap (SSet.opFunctor.map p) (SSet.opObjEquiv.symm z)
          (SSet.opFunctor.map i)) := by
  have := vertexFiber_kanComplex_of_leftFibration (sliceUnderProjection p) z
  have := vertexFiber_kanComplex_of_leftFibration (sliceUnderProjection (i ≫ p)) z
  rw [← oppositeKanHomotopyEquivalence_iff (cosliceRestrictionFiberMap p i z)]
  have hs : IsQCatEquivalence (cosliceReverseFiberIso p z).hom :=
    (qCatEquivalenceOfIso (cosliceReverseFiberIso p z)).isQCatEquivalence
  have ht : IsQCatEquivalence (cosliceReverseFiberIso (i ≫ p) z).hom :=
    (qCatEquivalenceOfIso (cosliceReverseFiberIso (i ≫ p) z)).isQCatEquivalence
  constructor
  · intro h
    have hc := h.isQCatEquivalence.comp ht
    rw [cosliceReverseFiberIso_restrict] at hc
    exact (hs.cancel_left hc).isSimplicialHomotopyEquivalence
  · intro h
    have hc := hs.comp h.isQCatEquivalence
    rw [← cosliceReverseFiberIso_restrict] at hc
    exact (ht.cancel_right hc).isSimplicialHomotopyEquivalence

end SerrePositivity.InfinityCategories.HomotopyLimits
