module
public import SerrePositivity.DifferentialGraded.Endomorphism.DerivedHomHomotopyComparison
public import SerrePositivity.DifferentialGraded.Perfect.KaroubiEquivalence

/-! # 再構成比較の本質的像のretract閉性と正則生成対象 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory

lemma fullyFaithfulEssImage_of_retract {C : Type v} {B : Type w} [Category* C] [Category* B]
    (F : C ⥤ B) [F.Full] [F.Faithful] [IsIdempotentComplete C]
    {X Y : B} (a : Retract X Y) (hY : F.essImage Y) : F.essImage X := by
  obtain ⟨M, ⟨e⟩⟩ := hY
  let b : Retract X (F.obj M) := a.trans (Retract.ofIso e.symm)
  let p := F.preimage (b.r ≫ b.i)
  have hpmap : F.map p = b.r ≫ b.i := F.map_preimage _
  have hp : p ≫ p = p := F.map_injective (by
    rw [F.map_comp, hpmap]
    simp only [Category.assoc, b.retract_assoc])
  obtain ⟨N, j, t, hjt, htj⟩ := IsIdempotentComplete.idempotents_split M p hp
  have hri : F.map t ≫ F.map j = b.r ≫ b.i := by rw [← F.map_comp, htj, hpmap]
  have hJT : F.map j ≫ F.map t = 𝟙 _ := by rw [← F.map_comp, hjt, F.map_id]
  refine ⟨N, ⟨{
    hom := F.map j ≫ b.r
    inv := b.i ≫ F.map t
    hom_inv_id := ?_
    inv_hom_id := ?_ }⟩⟩
  · calc
      (F.map j ≫ b.r) ≫ (b.i ≫ F.map t) = F.map j ≫ (b.r ≫ b.i) ≫ F.map t := by
        simp only [Category.assoc]
      _ = F.map j ≫ (F.map t ≫ F.map j) ≫ F.map t := by rw [hri]
      _ = (F.map j ≫ F.map t) ≫ (F.map j ≫ F.map t) := by simp only [Category.assoc]
      _ = 𝟙 _ := by rw [hJT, Category.id_comp]
  · calc
      (b.i ≫ F.map t) ≫ (F.map j ≫ b.r) = b.i ≫ (F.map t ≫ F.map j) ≫ b.r := by
        simp only [Category.assoc]
      _ = b.i ≫ (b.r ≫ b.i) ≫ b.r := by rw [hri]
      _ = 𝟙 _ := by simp only [Category.assoc, b.retract_assoc, b.retract]

lemma fullyFaithfulEssImageStableUnderRetracts {C : Type v} {B : Type w}
    [Category* C] [Category* B] (F : C ⥤ B) [F.Full] [F.Faithful] [IsIdempotentComplete C] :
    F.essImage.IsStableUnderRetracts where
  of_retract a hY := fullyFaithfulEssImage_of_retract F a hY

variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (S : Set D) (E : PerfectDGModuleOver A D S)

/-- 主Perfから全主導来圏へ向かう導来Hom比較。 -/
def perfectEndomorphismHomToDerived :
    PerfectModuleCategoryOver A D S ⥤ DerivedModuleCategory A (EndomorphismObject E.val) :=
  perfectModuleInclusion A D S ⋙ endomorphismDerivedHom A D E.val E.property.1

lemma perfectEndomorphismHomToDerived_full
    (hgen : endomorphismThickGeneratesPerfect A D S E) :
    (perfectEndomorphismHomToDerived A D S E).Full := by
  have : (perfectModuleInclusion A (EndomorphismObject E.val) Set.univ).Full := by
    unfold perfectModuleInclusion
    infer_instance
  change (perfectEndomorphismHomToPerfect A D S E hgen ⋙
    perfectModuleInclusion A (EndomorphismObject E.val) Set.univ).Full
  infer_instance

lemma perfectEndomorphismHomToDerived_faithful
    (hgen : endomorphismThickGeneratesPerfect A D S E) :
    (perfectEndomorphismHomToDerived A D S E).Faithful := by
  have : (perfectModuleInclusion A (EndomorphismObject E.val) Set.univ).Faithful := by
    unfold perfectModuleInclusion
    infer_instance
  change (perfectEndomorphismHomToPerfect A D S E hgen ⋙
    perfectModuleInclusion A (EndomorphismObject E.val) Set.univ).Faithful
  infer_instance

lemma perfectEndomorphismEssentialImageStableUnderRetracts
    (hgen : endomorphismThickGeneratesPerfect A D S E) :
    (perfectEndomorphismHomToDerived A D S E).essImage.IsStableUnderRetracts := by
  have := perfectEndomorphismHomToDerived_full A D S E hgen
  have := perfectEndomorphismHomToDerived_faithful A D S E hgen
  exact fullyFaithfulEssImageStableUnderRetracts _

lemma perfectEndomorphismEssentialImage_regular :
    (perfectEndomorphismHomToDerived A D S E).essImage
      ((moduleToDerived A (EndomorphismObject E.val)).obj
        (ForgetEnrichment.of (Complex A) (representable A (.point : EndomorphismObject E.val)))) :=
  ⟨⟨(moduleToDerived A D).obj (ForgetEnrichment.of (Complex A) E.val), E.property.2⟩,
    ⟨endomorphismDerivedHom_selfIso A D E.val E.property.1⟩⟩

end SerrePositivity.DifferentialGraded
