module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovLayer
public import SerrePositivity.KST.LocalizingInvariants.CochainTruncationLift
public import SerrePositivity.KST.LocalizingInvariants.BimoduleAlongMono

/-!
概要：Postnikov cycles 層への左右作用を、元の代数の積から実 chain map として構成する。
方針：tensor の上界から smart τ≤k への持ち上げを行い、包含の単射性で作用則を示す。
規約：元の包含は正則双加群への射。使われ方：Postnikov 拡大の係数双加群。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory
open scoped MonObj
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] (B : Mon (Complex R)) [B.X.IsStrictlyLE 0] (n : ℤ)

instance postnikov_nonpositive : (postnikov R B n).X.IsStrictlyLE 0 :=
  postnikovComplex_nonpositive R B n

instance postnikovQuotient_hom_epi : Epi (postnikovQuotient R B n).hom :=
  TruncationDesc.projection_epi B.X (-n)

local instance leftLayerTensor_upperBound :
    ((postnikov R B (n + 1)).X ⊗ postnikovLayer R B n).IsStrictlyLE (-(n + 1)) := by
  change (cochainTensor _ _).IsStrictlyLE _
  simpa only [zero_add] using
    cochainTensor_isStrictlyLE (postnikov R B (n + 1)).X (postnikovLayer R B n) 0 (-(n + 1))

local instance rightLayerTensor_upperBound :
    (postnikovLayer R B n ⊗ (postnikov R B (n + 1)).X).IsStrictlyLE (-(n + 1)) := by
  change (cochainTensor _ _).IsStrictlyLE _
  simpa only [add_zero] using
    cochainTensor_isStrictlyLE (postnikovLayer R B n) (postnikov R B (n + 1)).X (-(n + 1)) 0

def postnikovLayerActLeft :
    (postnikov R B (n + 1)).X ⊗ postnikovLayer R B n ⟶ postnikovLayer R B n :=
  TruncationLift.lift (-(n + 1))
    (((postnikov R B (n + 1)).X ◁ postnikovLayerInclusion R B n) ≫
      μ[(postnikov R B (n + 1)).X])

def postnikovLayerActRight :
    postnikovLayer R B n ⊗ (postnikov R B (n + 1)).X ⟶ postnikovLayer R B n :=
  TruncationLift.lift (-(n + 1))
    ((postnikovLayerInclusion R B n ▷ (postnikov R B (n + 1)).X) ≫
      μ[(postnikov R B (n + 1)).X])

lemma postnikovLayerActLeft_inclusion :
    postnikovLayerActLeft R B n ≫ postnikovLayerInclusion R B n =
      ((postnikov R B (n + 1)).X ◁ postnikovLayerInclusion R B n) ≫
        μ[(postnikov R B (n + 1)).X] := TruncationLift.lift_inclusion _ _

lemma postnikovLayerActRight_inclusion :
    postnikovLayerActRight R B n ≫ postnikovLayerInclusion R B n =
      (postnikovLayerInclusion R B n ▷ (postnikov R B (n + 1)).X) ≫
        μ[(postnikov R B (n + 1)).X] := TruncationLift.lift_inclusion _ _

def postnikovLayerBimodule : Bimod (postnikov R B (n + 1)) (postnikov R B (n + 1)) :=
  bimoduleAlongMono _ (postnikovLayerInclusion R B n)
    (postnikovLayerActLeft R B n) (postnikovLayerActRight R B n)
    (postnikovLayerActLeft_inclusion R B n) (postnikovLayerActRight_inclusion R B n)

def postnikovLayerInclusionBimodule :
    postnikovLayerBimodule R B n ⟶ Bimod.regular (postnikov R B (n + 1)) where
  hom := postnikovLayerInclusion R B n
  left_act_hom := postnikovLayerActLeft_inclusion R B n
  right_act_hom := postnikovLayerActRight_inclusion R B n

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
