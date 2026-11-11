module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.KST.LocalizingInvariants.VerdierCoreQuotientCofinality
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierSimplexCompletionComparison

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
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Fibration
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.LocalizingInvariants
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions
open _root_.SerrePositivity.KST.LocalizingInvariants

variable {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)

lemma pointFunctorEvaluation_inv_post {X Y : SSet.{u}} (f : X ⟶ Y) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.pointFunctorEvaluationIso X).inv ≫ (ihom (Δ[0] : SSet.{u})).map f =
      f ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.pointFunctorEvaluationIso Y).inv := by
  have hh : (ihom (Δ[0] : SSet.{u})).map f ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.pointFunctorEvaluationIso Y).hom =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.pointFunctorEvaluationIso X).hom ≫ f := rfl
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.pointFunctorEvaluationIso Y).hom).mp
  rw [Category.assoc, hh, ← Category.assoc, Iso.inv_hom_id, Category.id_comp,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]

def relativeFirstRowSimplexZeroToCorePreimage : (relativeFirstRowSimplex q 0 : SSet.{u}) ⟶
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore C.obj).preimage q.hom : SSet.{u}) :=
  Subcomplex.lift ((relativeFirstRowSimplex q 0).ι ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.pointFunctorEvaluationIso B.obj).hom) (by
    rintro n _ ⟨s, rfl⟩
    exact ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.pointFunctorEvaluationIso C.obj).hom).app n
      ⟨((ihom (Δ[0] : SSet.{u})).map q.hom).app n s.val, s.property⟩).property)

def relativeFirstRowSimplexZeroFromCorePreimage :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore C.obj).preimage q.hom : SSet.{u}) ⟶
      (relativeFirstRowSimplex q 0 : SSet.{u}) :=
  Subcomplex.lift (((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore C.obj).preimage q.hom).ι ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.pointFunctorEvaluationIso B.obj).inv) (by
    rintro n _ ⟨s, rfl⟩
    have hi := ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.pointFunctorEvaluationIso C.obj).inv).app n
      ⟨q.hom.app n s.val, s.property⟩).property
    have hn := congrArg (fun k => k.app n s.val) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.pointFunctorEvaluation_inv_post q.hom)
    change ((ihom (Δ[0] : SSet.{u})).map q.hom).app n
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.pointFunctorEvaluationIso B.obj).inv.app n s.val) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.pointFunctorEvaluationIso C.obj).inv.app n (q.hom.app n s.val) at hn
    change ((ihom (Δ[0] : SSet.{u})).map q.hom).app n
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.pointFunctorEvaluationIso B.obj).inv.app n s.val) ∈
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore ((ihom (Δ[0] : SSet.{u})).obj C.obj)).obj n
    rw [hn]
    exact hi)

/-- 元の一点評価を同じ相対 core 逆像へ制限した、全単体での厳密な両側逆。 -/
def relativeFirstRowSimplexZeroCorePreimageIso : (relativeFirstRowSimplex q 0 : SSet.{u}) ≅
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore C.obj).preimage q.hom : SSet.{u}) where
  hom := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.relativeFirstRowSimplexZeroToCorePreimage q
  inv := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.relativeFirstRowSimplexZeroFromCorePreimage q
  hom_inv_id := by
    apply (cancel_mono (relativeFirstRowSimplex q 0).ι).mp
    change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.relativeFirstRowSimplexZeroToCorePreimage q ≫
      (((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore C.obj).preimage q.hom).ι ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.pointFunctorEvaluationIso B.obj).inv)) = _
    rw [← Category.assoc]
    change ((relativeFirstRowSimplex q 0).ι ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.pointFunctorEvaluationIso B.obj).hom) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.pointFunctorEvaluationIso B.obj).inv = _
    rw [Category.assoc, Iso.hom_inv_id, Category.comp_id, Category.id_comp]
  inv_hom_id := by
    apply (cancel_mono ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore C.obj).preimage q.hom).ι).mp
    change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.relativeFirstRowSimplexZeroFromCorePreimage q ≫
      ((relativeFirstRowSimplex q 0).ι ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.pointFunctorEvaluationIso B.obj).hom)) = _
    rw [← Category.assoc]
    change ((((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore C.obj).preimage q.hom).ι ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.pointFunctorEvaluationIso B.obj).inv) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.pointFunctorEvaluationIso B.obj).hom) = _
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.id_comp]

lemma relativeFirstRowSimplexZeroCorePreimage_square :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.relativeFirstRowSimplexZeroCorePreimageIso q).hom ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore C.obj).fromPreimage q.hom =
      relativeFirstRowSimplexQuotient q 0 ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.pointFunctorEvaluationIso C.obj).hom := by
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore C.obj).ι).mp
  simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap_ι]
  rfl

/-- 元の第一行零単体商射そのものは anodyne 局所化で可逆。 -/
lemma relativeFirstRowSimplexQuotient_zero_localized_isIso
    {A : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) :
    IsIso (AnodyneHomotopy.anodyneQ.map (relativeFirstRowSimplexQuotient q 0)) := by
  let L := AnodyneHomotopy.anodyneQ.{u}
  have := verdierCoreQuotient_localized_isIso h
  have hi : IsIso (L.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.relativeFirstRowSimplexZeroCorePreimageIso q).hom) := inferInstance
  have hc : IsIso (L.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.pointFunctorEvaluationIso C.obj).hom)) := by
    change IsIso (L.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor.mapIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.pointFunctorEvaluationIso C.obj)).hom)
    infer_instance
  have hs := congrArg L.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.relativeFirstRowSimplexZeroCorePreimage_square q)
  rw [L.map_comp, L.map_comp] at hs
  have hm : IsIso (L.map (relativeFirstRowSimplexQuotient q 0) ≫
      L.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.pointFunctorEvaluationIso C.obj).hom)) := by
    rw [← hs]
    infer_instance
  exact (isIso_comp_right_iff _ _).mp hm

/-- 同じ零次完成比較の全写像空間も充満忠実。 -/
lemma relativeFirstRowSimplexCompletionComparison_zero_isFullyFaithful
    {A : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.relativeFirstRowSimplexCompletionComparison q 0) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.relativeFirstRowSimplexQuotient_localized_isIso_iff_fullyFaithful h 0).mp
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.relativeFirstRowSimplexQuotient_zero_localized_isIso q h)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.pointFunctorEvaluation_inv_post := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.pointFunctorEvaluation_inv_post

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.relativeFirstRowSimplexCompletionComparison_zero_isFullyFaithful := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.relativeFirstRowSimplexCompletionComparison_zero_isFullyFaithful

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.relativeFirstRowSimplexQuotient_zero_localized_isIso := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.relativeFirstRowSimplexQuotient_zero_localized_isIso

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.relativeFirstRowSimplexZeroCorePreimageIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.relativeFirstRowSimplexZeroCorePreimageIso := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.relativeFirstRowSimplexZeroCorePreimageIso

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.relativeFirstRowSimplexZeroCorePreimage_square := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.relativeFirstRowSimplexZeroCorePreimage_square

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.relativeFirstRowSimplexZeroFromCorePreimage (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.relativeFirstRowSimplexZeroFromCorePreimage := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.relativeFirstRowSimplexZeroFromCorePreimage

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.relativeFirstRowSimplexZeroToCorePreimage (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.relativeFirstRowSimplexZeroToCorePreimage := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.relativeFirstRowSimplexZeroToCorePreimage

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.relativeFirstRowSimplexZeroCorePreimageIso._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.relativeFirstRowSimplexZeroCorePreimageIso._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.relativeFirstRowSimplexZeroCorePreimageIso._proof_2 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.relativeFirstRowSimplexZeroCorePreimageIso._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.relativeFirstRowSimplexZeroFromCorePreimage._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.relativeFirstRowSimplexZeroFromCorePreimage._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.relativeFirstRowSimplexZeroToCorePreimage._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.relativeFirstRowSimplexZeroToCorePreimage._proof_1
