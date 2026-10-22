module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovUnderlyingPullback
public import SerrePositivity.KST.LocalizingInvariants.MonoidPullbackConeLimit

/-!
概要：元の隣接 Postnikov 上段は、実 class と零切断の実代数 pullback である。
方針：構成した実二脚の複体での普遍性を、単位・積を保持して実代数圏へ移す。
規約：元の上段を頂点とする実極限錐。使われ方：非分裂拡大の homotopy pullback 比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] (B : Mon (Complex R)) [B.X.IsStrictlyLE 0]
  (n : ℤ) (hn : 0 ≤ n)

def postnikovAlgebraPullbackCone : PullbackCone (postnikovPerturbedClass R B n hn)
    (SquareZero.zeroSection (postnikov R B n) (postnikovShiftedLayerBimodule R B n hn 1)) :=
  PullbackCone.mk (postnikovPerturbedInclusion R B n hn)
    (postnikovTransition R B (n + 1) n (by omega)) (postnikovPerturbedInclusion_class R B n hn)

def postnikovAlgebraPullback_isLimit : IsLimit (postnikovAlgebraPullbackCone R B n hn) :=
  MonoidPullback.isLimit_of_underlying _ _ _ _ (postnikovPerturbedInclusion_class R B n hn)
    (postnikovUnderlyingPullback_isLimit R B n hn)

def postnikovStrictPullbackIso : postnikov R B (n + 1) ≅
    MonoidPullback.obj (postnikovPerturbedClass R B n hn)
      (SquareZero.zeroSection (postnikov R B n) (postnikovShiftedLayerBimodule R B n hn 1)) :=
  (postnikovAlgebraPullback_isLimit R B n hn).conePointUniqueUpToIso (MonoidPullback.isLimit _ _)

lemma postnikovStrictPullbackIso_fst : (postnikovStrictPullbackIso R B n hn).hom ≫
    MonoidPullback.fst (postnikovPerturbedClass R B n hn)
      (SquareZero.zeroSection (postnikov R B n) (postnikovShiftedLayerBimodule R B n hn 1)) =
        postnikovPerturbedInclusion R B n hn :=
  (postnikovAlgebraPullback_isLimit R B n hn).conePointUniqueUpToIso_hom_comp
    (MonoidPullback.isLimit _ _) WalkingCospan.left

lemma postnikovStrictPullbackIso_snd : (postnikovStrictPullbackIso R B n hn).hom ≫
    MonoidPullback.snd (postnikovPerturbedClass R B n hn)
      (SquareZero.zeroSection (postnikov R B n) (postnikovShiftedLayerBimodule R B n hn 1)) =
        postnikovTransition R B (n + 1) n (by omega) :=
  (postnikovAlgebraPullback_isLimit R B n hn).conePointUniqueUpToIso_hom_comp
    (MonoidPullback.isLimit _ _) WalkingCospan.right

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
