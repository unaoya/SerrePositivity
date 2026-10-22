module

public import SerrePositivity.KST.LocalizingInvariants.DGBimoduleImageKernel
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroCoefficientMap
public import SerrePositivity.KST.LocalizingInvariants.MonoidPullbackConeLimit

/-!
概要：係数像の平方零代数を、元の係数商と零切断の実 pullback の頂点にする。
方針：二座標と実係数像の kernel 普遍性で複体の lift を作り、代数圏へ移す。
規約：元の係数包含と底射影を保持。使われ方：像への導来持ち上げの模型比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.SquareZeroImageFiber
variable {R : Type u} [CommRing R] {A : Mon (Complex R)} {M N : Bimod A A} (f : M ⟶ N)

abbrev inclusion := SquareZero.coefficientMap A (DGBimoduleImage.inclusion f)
abbrev quotient := SquareZero.coefficientMap A (DGBimoduleCokernel.projection f)
abbrev projection := SquareZero.projection A (DGBimoduleImage.obj f)
abbrev zeroSection := SquareZero.zeroSection A (DGBimoduleCokernel.obj f)

lemma condition : inclusion f ≫ quotient f = projection f ≫ zeroSection f := by
  apply Mon.Hom.ext
  change Limits.biprod.map (𝟙 A.X) (DGBimoduleImage.inclusion f).hom ≫
    biprod.map (𝟙 A.X) (DGBimoduleCokernel.projection f).hom = biprod.fst ≫ biprod.inl
  apply biprod.hom_ext
  · simp [Category.assoc]
  · simp only [Category.assoc, biprod.map_snd, biprod.inl_snd, comp_zero]
    rw [← Category.assoc, biprod.map_snd, Category.assoc,
      DGBimoduleImage.inclusion_cokernel, comp_zero]

abbrev underlyingCone : PullbackCone (quotient f).hom (zeroSection f).hom :=
  PullbackCone.mk (inclusion f).hom (projection f).hom
    (MonoidPullback.coneCondition_hom _ _ _ _ (condition f))

variable (s : PullbackCone (quotient f).hom (zeroSection f).hom)

lemma lift_base : s.fst ≫ (biprod.fst : (SquareZero.algebra A N).X ⟶ A.X) = s.snd := by
  have h := congrArg (fun t => t ≫
    (biprod.fst : (SquareZero.algebra A (DGBimoduleCokernel.obj f)).X ⟶ A.X)) s.condition
  change (s.fst ≫ biprod.map (𝟙 A.X) (DGBimoduleCokernel.projection f).hom) ≫
    biprod.fst = (s.snd ≫ biprod.inl) ≫ biprod.fst at h
  simpa only [Category.assoc, biprod.map_fst, Category.comp_id, biprod.inl_fst] using h

lemma lift_zero : (s.fst ≫ (biprod.snd : (SquareZero.algebra A N).X ⟶ N.X)) ≫
    (DGBimoduleCokernel.projection f).hom = 0 := by
  have h := congrArg (fun t => t ≫
    (biprod.snd : (SquareZero.algebra A (DGBimoduleCokernel.obj f)).X ⟶ _)) s.condition
  change (s.fst ≫ biprod.map (𝟙 A.X) (DGBimoduleCokernel.projection f).hom) ≫
    biprod.snd = (s.snd ≫ biprod.inl) ≫ biprod.snd at h
  simpa only [Category.assoc, biprod.map_snd, biprod.inl_snd, comp_zero] using h

def underlyingLift : s.pt ⟶ (SquareZero.algebra A (DGBimoduleImage.obj f)).X :=
  biprod.lift s.snd (DGBimoduleImage.chainLift f (s.fst ≫ biprod.snd) (lift_zero f s))

lemma underlyingLift_inclusion : underlyingLift f s ≫ (inclusion f).hom = s.fst := by
  apply biprod.hom_ext
  · change underlyingLift f s ≫ (biprod.map (𝟙 A.X) (DGBimoduleImage.inclusion f).hom) ≫
      biprod.fst = s.fst ≫ biprod.fst
    rw [biprod.map_fst, Category.comp_id, underlyingLift, biprod.lift_fst]
    exact (lift_base f s).symm
  · change underlyingLift f s ≫ (biprod.map (𝟙 A.X) (DGBimoduleImage.inclusion f).hom) ≫
      biprod.snd = s.fst ≫ biprod.snd
    rw [biprod.map_snd, ← Category.assoc, underlyingLift, biprod.lift_snd]
    exact DGBimoduleImage.chainLift_inclusion _ _ _

lemma underlyingLift_projection : underlyingLift f s ≫ (projection f).hom = s.snd :=
  biprod.lift_fst _ _

def underlying_isLimit : IsLimit (underlyingCone f) :=
  PullbackCone.IsLimit.mk _ (underlyingLift f) (underlyingLift_inclusion f)
    (underlyingLift_projection f) (fun s m hi hp => by
      apply biprod.hom_ext
      · exact hp.trans (underlyingLift_projection f s).symm
      · have := DGBimoduleImage.inclusion_mono f
        apply (cancel_mono (DGBimoduleImage.inclusion f).hom).1
        have h := congrArg (fun t => t ≫
          (biprod.snd : (SquareZero.algebra A N).X ⟶ N.X)) hi
        change (m ≫ biprod.map (𝟙 A.X) (DGBimoduleImage.inclusion f).hom) ≫
          biprod.snd = s.fst ≫ biprod.snd at h
        rw [Category.assoc, biprod.map_snd, ← Category.assoc] at h
        rw [underlyingLift, biprod.lift_snd]
        exact h.trans (DGBimoduleImage.chainLift_inclusion f _ (lift_zero f s)).symm)

def cone : PullbackCone (quotient f) (zeroSection f) :=
  PullbackCone.mk (inclusion f) (projection f) (condition f)

def isLimit : IsLimit (cone f) :=
  MonoidPullback.isLimit_of_underlying _ _ _ _ (condition f) (underlying_isLimit f)

end SerrePositivity.KST.LocalizingInvariants.SquareZeroImageFiber
