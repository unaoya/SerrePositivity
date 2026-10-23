module

public import SerrePositivity.InfinityCategories.F2.Ind.PinchedHomPullbackSquare
public import SerrePositivity.InfinityCategories.F2.CatInfinity.PinchedHomEndpointTransport
public import SerrePositivity.InfinityCategories.F1.KanFibrationEquivalenceLifting
public import SerrePositivity.InfinityCategories.F1.EquivalenceLiftingPullback

/-!
概要：右側の射が inner fibration のとき、充満忠実性を厳密な引き戻しへ移す。
方針：元の右写像空間の pullback と、右側の全ホーンの充填性を使う。
規約：充満忠実な左側の射自身には充填性を要求しない。使われ方：実 diagram comma。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 右側が inner fibration なら、左側の充満忠実性は第二射影へ移る。 -/
lemma fullyFaithful_pullback_snd_of_innerFibration_right
    {X Y B : SSet.{u}} [Quasicategory X] [Quasicategory Y] [Quasicategory B]
    {p : X ⟶ B} (hp : IsFullyFaithful p) (q : Y ⟶ B) [InnerFibration q] :
    IsFullyFaithful (pullback.snd p q) := by
  have : InnerFibration (pullback.fst p q) :=
    ⟨innerFibrations.pullback_fst p q (InnerFibration.mem (q := q))⟩
  have : Quasicategory (pullback p q) := quasicategory_of_innerFibration (pullback.fst p q)
  intro v w
  let mp := pinchedHomMap p ((pullback.fst p q).app (Opposite.op ⦋0⦌) v)
    ((pullback.fst p q).app (Opposite.op ⦋0⦌) w)
  let mq := pinchedHomPullbackBaseMap p q v w
  let e := pinchedHomIsoOfEq (pullbackSimplex_compat p q v).symm
    (pullbackSimplex_compat p q w).symm
  have hm : mq = pinchedHomMap q ((pullback.snd p q).app (Opposite.op ⦋0⦌) v)
      ((pullback.snd p q).app (Opposite.op ⦋0⦌) w) ≫ e.hom := by
    apply SSet.hom_ext
    rintro ⟨⟨n⟩⟩
    apply ConcreteCategory.hom_ext
    intro s
    apply PinchedHom.Simplex.ext
    change _ = ((pinchedHomIsoOfEq _ _).hom.app (Opposite.op ⦋n⦌) _).val
    rw [pinchedHomIsoOfEq_hom_val]
    rfl
  have : Fibration (pinchedHomMap q ((pullback.snd p q).app (Opposite.op ⦋0⦌) v)
      ((pullback.snd p q).app (Opposite.op ⦋0⦌) w)) :=
    fibration_of_hasLiftingProperty_horn _ (pinchedHomMap_hasLiftingProperty_horn q _ _)
  have : Fibration mq := by
    rw [hm]
    infer_instance
  have he : IsQCatEquivalence mp := (hp _ _).isQCatEquivalence
  have hpb := (he.pullback_snd_isPrecompositionEquivalence_of_kanEquivalenceLifting mq
    (kanEquivalenceLifting_of_kanFibration mq)).isQCatEquivalence
  have hs := pinchedHomPullback_isPullback p q v w
  have h := (qCatEquivalenceOfIso hs.isoPullback).isQCatEquivalence.comp hpb
  change IsQCatEquivalence (hs.isoPullback.hom ≫ pullback.snd mp mq) at h
  rw [hs.isoPullback_hom_snd] at h
  exact h.isSimplicialHomotopyEquivalence

end SerrePositivity.InfinityCategories.F2.Ind
