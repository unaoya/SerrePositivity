module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovPerturbedInclusion

/-!
概要：摂動 class と零切断の複体 pullback は、元の隣接 Postnikov 上段である。
方針：元の cone との同型で持ち上げを移し、包含・元の遷移との可換性を検証する。
規約：実際に構成した二脚の普遍性。使われ方：実代数圏への pullback 普遍性の昇格。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits HomologicalComplex CochainComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] (B : Mon (Complex R)) [B.X.IsStrictlyLE 0]
  (n : ℤ) (hn : 0 ≤ n)

abbrev PostnikovUnderlyingCone := PullbackCone (postnikovPerturbedClass R B n hn).hom
  (SquareZero.zeroSection (postnikov R B n) (postnikovShiftedLayerBimodule R B n hn 1)).hom

def postnikovUnderlyingLift (s : PostnikovUnderlyingCone R B n hn) :
    s.pt ⟶ (postnikov R B (n + 1)).X :=
  cochainConeSplitLift (postnikovLayerInclusion R B n)
    (postnikovTransition R B (n + 1) n (by omega)).hom
    (postnikovLayerInclusion_transition_zero R B n)
    (s.fst ≫ (postnikovPerturbedExtensionComplexIso R B n hn).hom) s.snd (by
      change (s.fst ≫ (postnikovPerturbedExtensionComplexIso R B n hn).hom) ≫
        postnikovExtensionConeLinearClass R B n hn = _
      rw [Category.assoc, ← postnikovPerturbedClass_hom_eq]
      exact s.condition)

lemma postnikovUnderlyingLift_inclusion (s : PostnikovUnderlyingCone R B n hn) :
    postnikovUnderlyingLift R B n hn s ≫ (postnikovPerturbedInclusion R B n hn).hom = s.fst := by
  apply (cancel_mono (postnikovPerturbedExtensionComplexIso R B n hn).hom).1
  rw [Category.assoc, postnikovPerturbedInclusion_toCone]
  exact cochainConeSplitLift_inr _ _ _ _ _ _

lemma postnikovUnderlyingLift_transition (s : PostnikovUnderlyingCone R B n hn) :
    postnikovUnderlyingLift R B n hn s ≫
      (postnikovTransition R B (n + 1) n (by omega)).hom = s.snd :=
  cochainConeSplitLift_quotient _ _ _ _ _ _

def postnikovUnderlyingPullbackCone : PostnikovUnderlyingCone R B n hn :=
  PullbackCone.mk (postnikovPerturbedInclusion R B n hn).hom
    (postnikovTransition R B (n + 1) n (by omega)).hom
    (congrArg Mon.Hom.hom (postnikovPerturbedInclusion_class R B n hn))

def postnikovUnderlyingPullback_isLimit : IsLimit (postnikovUnderlyingPullbackCone R B n hn) :=
  PullbackCone.IsLimit.mk _ (postnikovUnderlyingLift R B n hn)
    (postnikovUnderlyingLift_inclusion R B n hn) (postnikovUnderlyingLift_transition R B n hn)
    (fun s m hm _ => by
      have := postnikovPerturbedInclusion_mono R B n hn
      apply (cancel_mono (postnikovPerturbedInclusion R B n hn).hom).1
      exact hm.trans (postnikovUnderlyingLift_inclusion R B n hn s).symm)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
