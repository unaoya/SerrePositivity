module

public import SerrePositivity.KST.LocalizingInvariants.VerdierCoreQuotientCofinality
public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierSimplexCompletionComparison

/-!
概要：元の第一行零単体商比較を、同じ商の core 逆像射影の cofinality で放電する。
方針：元の一点関手評価の両向きを厳密な逆像へ制限し、同じ商可換四角形で戻す。
規約：零次を除外せず、元の relativeFirstRowSimplexQuotient 自身の可逆性を証明する。
使われ方：K-B c5 の全次数の依頼型における零次入力。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Fibration
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.LocalizingInvariants

variable {B C : StableCategory.{u}} (q : ExactMap B C)

lemma pointFunctorEvaluation_inv_post {X Y : SSet.{u}} (f : X ⟶ Y) :
    (pointFunctorEvaluationIso X).inv ≫ (ihom (Δ[0] : SSet.{u})).map f =
      f ≫ (pointFunctorEvaluationIso Y).inv := by
  have hh : (ihom (Δ[0] : SSet.{u})).map f ≫ (pointFunctorEvaluationIso Y).hom =
      (pointFunctorEvaluationIso X).hom ≫ f := rfl
  apply (cancel_mono (pointFunctorEvaluationIso Y).hom).mp
  rw [Category.assoc, hh, ← Category.assoc, Iso.inv_hom_id, Category.id_comp,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]

def relativeFirstRowSimplexZeroToCorePreimage : (relativeFirstRowSimplex q 0 : SSet.{u}) ⟶
    ((quasicategoryCore C.obj).preimage q.hom : SSet.{u}) :=
  Subcomplex.lift ((relativeFirstRowSimplex q 0).ι ≫ (pointFunctorEvaluationIso B.obj).hom) (by
    rintro n _ ⟨s, rfl⟩
    exact ((quasicategoryCoreMap (pointFunctorEvaluationIso C.obj).hom).app n
      ⟨((ihom (Δ[0] : SSet.{u})).map q.hom).app n s.val, s.property⟩).property)

def relativeFirstRowSimplexZeroFromCorePreimage :
    ((quasicategoryCore C.obj).preimage q.hom : SSet.{u}) ⟶
      (relativeFirstRowSimplex q 0 : SSet.{u}) :=
  Subcomplex.lift (((quasicategoryCore C.obj).preimage q.hom).ι ≫
    (pointFunctorEvaluationIso B.obj).inv) (by
    rintro n _ ⟨s, rfl⟩
    have hi := ((quasicategoryCoreMap (pointFunctorEvaluationIso C.obj).inv).app n
      ⟨q.hom.app n s.val, s.property⟩).property
    have hn := congrArg (fun k => k.app n s.val) (pointFunctorEvaluation_inv_post q.hom)
    change ((ihom (Δ[0] : SSet.{u})).map q.hom).app n
      ((pointFunctorEvaluationIso B.obj).inv.app n s.val) =
      (pointFunctorEvaluationIso C.obj).inv.app n (q.hom.app n s.val) at hn
    change ((ihom (Δ[0] : SSet.{u})).map q.hom).app n
      ((pointFunctorEvaluationIso B.obj).inv.app n s.val) ∈
      (quasicategoryCore ((ihom (Δ[0] : SSet.{u})).obj C.obj)).obj n
    rw [hn]
    exact hi)

/-- 元の一点評価を同じ相対 core 逆像へ制限した、全単体での厳密な両側逆。 -/
def relativeFirstRowSimplexZeroCorePreimageIso : (relativeFirstRowSimplex q 0 : SSet.{u}) ≅
    ((quasicategoryCore C.obj).preimage q.hom : SSet.{u}) where
  hom := relativeFirstRowSimplexZeroToCorePreimage q
  inv := relativeFirstRowSimplexZeroFromCorePreimage q
  hom_inv_id := by
    apply (cancel_mono (relativeFirstRowSimplex q 0).ι).mp
    change (relativeFirstRowSimplexZeroToCorePreimage q ≫
      (((quasicategoryCore C.obj).preimage q.hom).ι ≫ (pointFunctorEvaluationIso B.obj).inv)) = _
    rw [← Category.assoc]
    change ((relativeFirstRowSimplex q 0).ι ≫ (pointFunctorEvaluationIso B.obj).hom) ≫
      (pointFunctorEvaluationIso B.obj).inv = _
    rw [Category.assoc, Iso.hom_inv_id, Category.comp_id, Category.id_comp]
  inv_hom_id := by
    apply (cancel_mono ((quasicategoryCore C.obj).preimage q.hom).ι).mp
    change (relativeFirstRowSimplexZeroFromCorePreimage q ≫
      ((relativeFirstRowSimplex q 0).ι ≫ (pointFunctorEvaluationIso B.obj).hom)) = _
    rw [← Category.assoc]
    change ((((quasicategoryCore C.obj).preimage q.hom).ι ≫ (pointFunctorEvaluationIso B.obj).inv) ≫
      (pointFunctorEvaluationIso B.obj).hom) = _
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.id_comp]

lemma relativeFirstRowSimplexZeroCorePreimage_square :
    (relativeFirstRowSimplexZeroCorePreimageIso q).hom ≫
      (quasicategoryCore C.obj).fromPreimage q.hom =
      relativeFirstRowSimplexQuotient q 0 ≫
        quasicategoryCoreMap (pointFunctorEvaluationIso C.obj).hom := by
  apply (cancel_mono (quasicategoryCore C.obj).ι).mp
  simp only [Category.assoc, quasicategoryCoreMap_ι]
  rfl

/-- 元の第一行零単体商射そのものは anodyne 局所化で可逆。 -/
lemma relativeFirstRowSimplexQuotient_zero_localized_isIso
    {A : StableCategory.{u}} {i : ExactMap A B} (h : IsVerdierSequence i q) :
    IsIso (AnodyneHomotopy.anodyneQ.map (relativeFirstRowSimplexQuotient q 0)) := by
  let L := AnodyneHomotopy.anodyneQ.{u}
  have := verdierCoreQuotient_localized_isIso h
  have hi : IsIso (L.map (relativeFirstRowSimplexZeroCorePreimageIso q).hom) := inferInstance
  have hc : IsIso (L.map (quasicategoryCoreMap (pointFunctorEvaluationIso C.obj).hom)) := by
    change IsIso (L.map (quasicategoryCoreFunctor.mapIso (pointFunctorEvaluationIso C.obj)).hom)
    infer_instance
  have hs := congrArg L.map (relativeFirstRowSimplexZeroCorePreimage_square q)
  rw [L.map_comp, L.map_comp] at hs
  have hm : IsIso (L.map (relativeFirstRowSimplexQuotient q 0) ≫
      L.map (quasicategoryCoreMap (pointFunctorEvaluationIso C.obj).hom)) := by
    rw [← hs]
    infer_instance
  exact (isIso_comp_right_iff _ _).mp hm

/-- 同じ零次完成比較の全写像空間も充満忠実。 -/
lemma relativeFirstRowSimplexCompletionComparison_zero_isFullyFaithful
    {A : StableCategory.{u}} {i : ExactMap A B} (h : IsVerdierSequence i q) :
    IsFullyFaithful (relativeFirstRowSimplexCompletionComparison q 0) :=
  (relativeFirstRowSimplexQuotient_localized_isIso_iff_fullyFaithful h 0).mp
    (relativeFirstRowSimplexQuotient_zero_localized_isIso q h)

end SerrePositivity.KST.LocalizingInvariants
