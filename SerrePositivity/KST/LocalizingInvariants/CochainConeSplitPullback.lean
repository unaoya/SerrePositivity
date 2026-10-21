module

public import SerrePositivity.KST.LocalizingInvariants.CochainConeQuotientComparison
public import SerrePositivity.KST.LocalizingInvariants.CochainConeShortExact

/-!
概要：cone の商への射と shift 境界を使い、元の複体を零切断の実 pullback と表示する。
方針：cone の包含が境界の実 kernel である普遍性を使い、元の商射も回収する。
規約：複体圏の厳密な pullback。使われ方：Postnikov derivation の乗法的模型の設計。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits CochainComplex HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants
variable {R : Type u} [CommRing R] {M K L : Complex R}
  (i : M ⟶ K) (q : K ⟶ L) (h : i ≫ q = 0)

def cochainConeToSplit : mappingCone i ⟶ L ⊞ M⟦(1 : ℤ)⟧ :=
  biprod.lift (cochainConeQuotient i q h) (mappingCone.triangle i).mor₃

@[reassoc] lemma cochainConeToSplit_fst :
    cochainConeToSplit i q h ≫ biprod.fst = cochainConeQuotient i q h := biprod.lift_fst _ _

@[reassoc] lemma cochainConeToSplit_snd :
    cochainConeToSplit i q h ≫ biprod.snd = (mappingCone.triangle i).mor₃ := biprod.lift_snd _ _

lemma cochainConeToSplit_condition :
    mappingCone.inr i ≫ cochainConeToSplit i q h = q ≫ biprod.inl := by
  apply biprod.hom_ext
  · rw [Category.assoc, cochainConeToSplit_fst, cochainConeQuotient_inr,
      Category.assoc, biprod.inl_fst, Category.comp_id]
  · rw [Category.assoc, cochainConeToSplit_snd, mappingCone.inr_triangleδ,
      Category.assoc, biprod.inl_snd, comp_zero]

lemma cochainConeSplit_zero {W : Complex R} (a : W ⟶ mappingCone i) (b : W ⟶ L)
    (w : a ≫ cochainConeToSplit i q h = b ≫ biprod.inl) :
    a ≫ (mappingCone.triangle i).mor₃ = 0 := by
  have hs := congrArg (fun t => t ≫ biprod.snd) w
  simpa only [Category.assoc, cochainConeToSplit_snd, biprod.inl_snd, comp_zero] using hs

def cochainConeSplitLift {W : Complex R} (a : W ⟶ mappingCone i) (b : W ⟶ L)
    (w : a ≫ cochainConeToSplit i q h = b ≫ biprod.inl) : W ⟶ K :=
  (KernelFork.IsLimit.lift' (cochainConeInr_isKernel i) a (cochainConeSplit_zero i q h a b w)).1

@[reassoc] lemma cochainConeSplitLift_inr {W : Complex R}
    (a : W ⟶ mappingCone i) (b : W ⟶ L)
    (w : a ≫ cochainConeToSplit i q h = b ≫ biprod.inl) :
    cochainConeSplitLift i q h a b w ≫ mappingCone.inr i = a :=
  (KernelFork.IsLimit.lift' (cochainConeInr_isKernel i) a (cochainConeSplit_zero i q h a b w)).2

lemma cochainConeSplitLift_quotient {W : Complex R} (a : W ⟶ mappingCone i) (b : W ⟶ L)
    (w : a ≫ cochainConeToSplit i q h = b ≫ biprod.inl) :
    cochainConeSplitLift i q h a b w ≫ q = b := by
  calc
    _ = (cochainConeSplitLift i q h a b w ≫ mappingCone.inr i) ≫
        cochainConeQuotient i q h := by rw [Category.assoc, cochainConeQuotient_inr]
    _ = a ≫ cochainConeQuotient i q h := by rw [cochainConeSplitLift_inr]
    _ = b := by
      have hs := congrArg (fun t => t ≫ biprod.fst) w
      simpa only [Category.assoc, cochainConeToSplit_fst, biprod.inl_fst,
        Category.comp_id] using hs

def cochainConeSplitPullback : PullbackCone (cochainConeToSplit i q h) biprod.inl :=
  PullbackCone.mk (mappingCone.inr i) q (cochainConeToSplit_condition i q h)

def cochainConeSplitPullback_isLimit : IsLimit (cochainConeSplitPullback i q h) := by
  refine PullbackCone.IsLimit.mk _
    (fun s => cochainConeSplitLift i q h s.fst s.snd s.condition) ?_ ?_ ?_
  · intro s
    exact cochainConeSplitLift_inr i q h _ _ _
  · intro s
    exact cochainConeSplitLift_quotient i q h _ _ _
  · intro s m hm _
    have := cochainConeInr_mono i
    apply (cancel_mono (mappingCone.inr i)).1
    rw [hm, cochainConeSplitLift_inr]

end SerrePositivity.KST.LocalizingInvariants
