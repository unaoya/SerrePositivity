module

public import SerrePositivity.InfinityCategories.F1.PullbackTerminalProductIso
public import SerrePositivity.InfinityCategories.F1.CocartesianHornBoundaryHomPullbacks
public import SerrePositivity.InfinityCategories.F1.CocartesianZeroBoundaryComparison

/-!
概要：一次元標準境界上の元の native Hom と分類先 Hom を、同じ両端の直積へ分解する。
方針：空の共有境界上の終対象性と、同じホーン・面の厳密な pullback を使う。
規約：両射影は実際の二端点への直接制限を保持する。
使われ方：両端の零次元比較から一次元境界の比較を構成する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
variable {B : SSet.{u}} (i : Fin 2) (σ : (Δ[1] : SSet.{u}) ⟶ B)

section Source
variable {E F : SSet.{u}} [Quasicategory B]
  (p : E ⟶ B) [CocartesianFibration p] (q : F ⟶ B) [CocartesianFibration q]

/-- 元の一次元境界の native core と、同じ両端の native core の直積の同型。 -/
def cocartesianOneBoundaryNativeProductIso :=
  pullbackTerminalProductIso (cocartesianHornBoundary_native_isPullback 0 i σ p q)
    (cocartesianPullbackNativeLift_isTerminal_of_isInitial p q
      (HornBoundaryOver.shared 0 i σ) zeroSimplexBoundary_isInitial)

/-- 同じ native 積分解の第一射影は、元の面側の端点制限。 -/
lemma cocartesianOneBoundaryNativeProductIso_hom_fst :
    (cocartesianOneBoundaryNativeProductIso i σ p q).hom ≫ fst _ _ =
      cocartesianPullbackNativeLiftPre p q (HornBoundaryOver.faceInclusion 0 i σ) :=
  pullbackTerminalProductIso_hom_fst _ _

/-- 同じ native 積分解の第二射影は、元のホーン側の端点制限。 -/
lemma cocartesianOneBoundaryNativeProductIso_hom_snd :
    (cocartesianOneBoundaryNativeProductIso i σ p q).hom ≫ snd _ _ =
      cocartesianPullbackNativeLiftPre p q (HornBoundaryOver.hornInclusion 0 i σ) :=
  pullbackTerminalProductIso_hom_snd _ _
end Source

section Target
variable {X : SSet.{u + 1}} (P Q : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ X)

/-- 同じ一次元境界の分類先 Hom も、同じ両端の Hom の直積と同型。 -/
def cocartesianOneBoundaryIntervalProductIso :=
  pullbackTerminalProductIso (cocartesianHornBoundary_interval_isPullback 0 i σ P Q)
    (intervalDiagramHom_isTerminal_of_isInitial _ _
      (uliftSSet_isInitial_of_isInitial zeroSimplexBoundary_isInitial))

/-- 同じ target 積分解の第一射影も、元の面側の端点制限。 -/
lemma cocartesianOneBoundaryIntervalProductIso_hom_fst :
    (cocartesianOneBoundaryIntervalProductIso i σ P Q).hom ≫ fst _ _ =
      intervalDiagramOverPre P Q (uliftOverMorphism (HornBoundaryOver.faceInclusion 0 i σ)) :=
  pullbackTerminalProductIso_hom_fst _ _

/-- 同じ target 積分解の第二射影も、元のホーン側の端点制限。 -/
lemma cocartesianOneBoundaryIntervalProductIso_hom_snd :
    (cocartesianOneBoundaryIntervalProductIso i σ P Q).hom ≫ snd _ _ =
      intervalDiagramOverPre P Q (uliftOverMorphism (HornBoundaryOver.hornInclusion 0 i σ)) :=
  pullbackTerminalProductIso_hom_snd _ _
end Target

end SerrePositivity.InfinityCategories
