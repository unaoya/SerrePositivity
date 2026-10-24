module

public import
SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightFixedTransitionZeroProjection

/-!
概要：fixed Γ の遷移・標準 class・互換性を同じ零底上の実相対経路へ移す。
方針：元の零底射の射影式を保つ底付き平方零代数射で移す。
規約：元の三経路の全射と端点を保持。使われ方：反転・合成の右像比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
open ProExcision
variable (R : Type u) [CommRing R] {n : ℤ} (hn : 0 ≤ n)
  {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {i m : ℕ} {hi : i ≤ m} (c : NonpositiveInverseRoof R (f.map (lowerFunctor R n hn)) i m hi)
  (d : PostnikovCommonLayerInverse R hn f c) {j : ℕ} (hj : j ≤ i)

attribute [local instance] PostnikovRoofZeroSpan.refined_source_nonpositive
  PostnikovRoofZeroSpan.refined_target_nonpositive

def postnikovCommonClassFixedZeroBase :=
  postnikovCommonClassRetractBase R hn f c d (hj := hj) ≫
    postnikovTransition R (A.obj j).obj n 0 (by omega) ≫ postnikovMap R (f.app j).hom 0

def postnikovCommonClassFixedZeroMap :=
  postnikovCommonClassTransitionToZero R hn f c d hj ≫ postnikovZeroClassMap R n 1 (f.app j).hom

lemma postnikovCommonClassFixedZeroMap_projection :
    postnikovCommonClassFixedZeroMap R hn f c d hj ≫ SquareZero.projection _ _ =
      SquareZero.projection _ _ ≫ postnikovCommonClassFixedZeroBase R hn f c d hj := by
  rw [postnikovCommonClassFixedZeroMap, Category.assoc, postnikovZeroClassMap_projection,
    ← Category.assoc, postnikovCommonClassTransitionToZero_projection]
  simp only [postnikovCommonClassFixedZeroBase, Category.assoc]

variable (e : PostnikovZeroLayerInverse R n f j i hj)

def postnikovCommonClassFixedTransitionMappedRelative :=
  ((postnikovCommonClassFixedTransitionRelative R hn f c d e).precomp
    (cellPathNonpositiveProjection R (postnikovCommonRightZeroGlueSource R hn f c d))).mapOver
    (postnikovCommonClassFixedZeroBase R hn f c d hj)
    (postnikovCommonClassFixedZeroMap R hn f c d hj)
    (postnikovCommonClassFixedZeroMap_projection R hn f c d hj)

def postnikovCommonClassFixedStandardMappedRelative :=
  ((postnikovCommonClassStandardRelative R hn f c d (hj := hj)).precomp
    (cellPathNonpositiveProjection R (postnikovCommonRightZeroGlueSource R hn f c d))).mapOver
    (postnikovCommonClassFixedZeroBase R hn f c d hj)
    (postnikovCommonClassFixedZeroMap R hn f c d hj)
    (postnikovCommonClassFixedZeroMap_projection R hn f c d hj)

def postnikovCommonClassFixedCompatibilityMappedRelative :=
  (postnikovCommonClassFixedGlueCompatibility R hn f c d e).mapOver
    (postnikovCommonClassFixedZeroBase R hn f c d hj)
    (postnikovCommonClassFixedZeroMap R hn f c d hj)
    (postnikovCommonClassFixedZeroMap_projection R hn f c d hj)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
