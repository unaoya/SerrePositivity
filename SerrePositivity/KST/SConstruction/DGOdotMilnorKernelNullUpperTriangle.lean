module
public import SerrePositivity.KST.SConstruction.DGPerfectComparisonNullSecond
public import SerrePositivity.KST.SConstruction.DGOdotMilnorKernelTargetContraction

/-!
概要：元厚核からの実逆回転を V へ厳密因子化し、同じ共有対角の S 上二単体を作る。
方針：元第二 graph の対象別収縮を raw cone 判定へ代入する。
規約：元 cell 包含・実中央辺の合成を対角に保持し、新しい主仮定を加えない。
使われ方：K-S2 の元下二単体と貼る比較面。ν 面の全比較と三認証は別工程。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet DifferentialGraded InfinityCategories
open scoped Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "B" => DGOdotGluing R d
local notation "P" => DGCategoryCellResolution.Source R (B)
local notation "I" => dgQuotientImage R (DGLaxQuotientEndInput.diagonal (dgOdotQuotientInput R d))
local notation "K" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientThickFlatKernel R (B) (I)
local notation "Q" => DGQuotient.QuotientObject (P) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGNullObjects R (B) (I))
local notation "k" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientThickFlatKernelInclusion R (B) (I)
local notation "H" => dgOdotMilnorRightAxisLift R d
local notation "U" => DGOdotMilnorRightAxisBase R d
local notation "F" => dgOdotMilnorRightAxisQuotientSource R d
local notation "G" => dgOdotMilnorRightAxisQuotientTarget R d
local notation "τ" => dgOdotMilnorRightAxisQuotientComparison R d

/-- 概要：元厚核関手の実逆回転 cone は各対象で可縮。
方針：同じ Γ の対象別収縮を元小実像・raw cone 判定へ渡す。
規約：Γ 全体の h-射影性や自然収縮は使わない。使われ方：V 因子化の無条件入力。 -/
lemma dgOdotMilnorKernelLift_nullProperty (x : K) :
    dgIdentityHomGluingNullProperty R (U) ((H).obj ((k).obj x)) :=
  dgPerfectComparisonInverseRotation_nullProperty R (Q) (F) (G) (τ) ((k).obj x)
    (dgOdotMilnorKernelTarget_objectwise_contractible R d x)

/-- 概要：元厚核からの実中央関手の厳密 V 因子化。
方針：元の全 Hom と証明済み cone 可縮性を保持する。
規約：元の共有対角を変更しない。使われ方：上二単体の第一短辺の元 dg 関手。 -/
def dgOdotMilnorKernelNullFactor :
    DGFunctor R (K) (DGIdentityHomGluingNullDomain R (U)) :=
  dgIdentityHomGluingNullFactor R (U) ((k).comp (H))
    (dgOdotMilnorKernelLift_nullProperty R d)

/-- 概要：元厚核から V への同じ厳密因子化の固定 S 辺。
方針：元実関手を共通宇宙へ持ち上げる。
規約：元始域を保持。使われ方：上二単体の第一短辺。 -/
def dgOdotMilnorKernelNullFactorInputMap :
    dgOdotMilnorFlatKernelInput R d ⟶ dgIdentityHomGluingNullInput R (U) :=
  dgIdentityHomGluingNullFactorInputMap R (U) ((k).comp (H))
    (dgOdotMilnorKernelLift_nullProperty R d)

/-- 概要：元厚核包含と元実中央辺の厳密合成を対角に持つ S 上二単体。
方針：V への厳密因子化の合成二単体を元合成辺へ照合する。
規約：K-S2 の共有対角そのもの。使われ方：共通長方形の比較面。 -/
def dgOdotMilnorKernelNullUpperTriangle : SSet.Edge.CompStruct
    (X := dgKInputInfinity.{u, u + 1} R)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgOdotMilnorKernelNullFactorInputMap R d))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgIdentityHomGluingNullInputMap R (U)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgOdotMilnorFlatKernelInputMap R d ≫
      dgOdotMilnorRightAxisInputMap R d)) :=
  dgIdentityHomGluingNullFactorCompositeTriangle R (U) (P) (k) (H)
    (dgOdotMilnorKernelLift_nullProperty R d)

end SerrePositivity.KST.SConstruction
