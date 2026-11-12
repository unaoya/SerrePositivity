module
public import SerrePositivity.KST.SConstruction.McCarthyLastMotion
public import SerrePositivity.KST.SConstruction.CofiberEvaluations

/-! # McCarthy の λ と μ を結ぶ coherent な変換
概要：動かす前後の添字で制限した図式に標準恒等 cofiber 関手を適用し、上辺の変換を作る。
方針：Ar 上の prism に元の図式と標準零 cofiber 関手を後合成する。
規約：零対象を指定するが元の gapped 図式の零対角は変更しない。使われ方：McCarthy の押し出し ρ。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：元の図式の添字 α の制限から標準恒等 cofiber の λ 図式を作る。
方針：添字制限と標準零 cofiber 関手の後合成。
規約：A の gapped 性は定義には不要。使われ方：押し出し span の共通始点。 -/
def mcCarthyLambda {n m : ℕ} {C : SSet.{u}} [Quasicategory C]
    (z : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroVertex C) (A : arNerve m ⟶ C) (α : Fin (n + 1) →o Fin (m + 1)) :
    arNerve n ⟶ cofiberDiagrams C :=
  arNerveMap α ≫ A ≫ zeroCofiberFunctor z false

/-- 概要：動かした添字による標準恒等 cofiber の μ 図式。
方針：λ の添字を最後の頂点への収縮で変更する。
規約：全ての時刻の単体を許す。使われ方：押し出し span の上辺の終点。 -/
def mcCarthyMu {n m : ℕ} {C : SSet.{u}} [Quasicategory C]
    (z : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroVertex C) (A : arNerve m ⟶ C) (α : Fin (n + 1) →o Fin (m + 1))
    (τ : Fin (n + 1) →o Fin 2) : arNerve n ⟶ cofiberDiagrams C :=
  mcCarthyLambda z A (mcCarthyMovedOrder α τ)

/-- 概要：λ と μ を結ぶ cofiber 図式の coherent な prism。
方針：Ar の添字の変換に元の図式と標準 cofiber 関手を後合成する。
規約：時刻は第一因子。使われ方：McCarthy の押し出しの上辺。 -/
def mcCarthyLambdaMu {n m : ℕ} {C : SSet.{u}} [Quasicategory C]
    (z : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroVertex C) (A : arNerve m ⟶ C) (α : Fin (n + 1) →o Fin (m + 1))
    (τ : Fin (n + 1) →o Fin 2) : (Δ[1] : SSet.{u}) ⊗ arNerve n ⟶ cofiberDiagrams C :=
  mcCarthyArMotion α τ ≫ A ≫ zeroCofiberFunctor z false

/-- 概要：上辺の prism の始点は λ。
方針：Ar の prism の始点の式。
規約：射の厳密な等号。使われ方：span の共通始点の照合。 -/
lemma mcCarthyLambdaMu_zero {n m : ℕ} {C : SSet.{u}} [Quasicategory C]
    (z : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroVertex C) (A : arNerve m ⟶ C) (α : Fin (n + 1) →o Fin (m + 1))
    (τ : Fin (n + 1) →o Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (arNerve n) ≫ mcCarthyLambdaMu z A α τ = mcCarthyLambda z A α := by
  rw [mcCarthyLambdaMu, ← Category.assoc, mcCarthyArMotion_zero]
  rfl

/-- 概要：上辺の prism の終点は μ。
方針：Ar の prism の終点の式。
規約：射の厳密な等号。使われ方：span の上辺の終点の照合。 -/
lemma mcCarthyLambdaMu_one {n m : ℕ} {C : SSet.{u}} [Quasicategory C]
    (z : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroVertex C) (A : arNerve m ⟶ C) (α : Fin (n + 1) →o Fin (m + 1))
    (τ : Fin (n + 1) →o Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (arNerve n) ≫ mcCarthyLambdaMu z A α τ = mcCarthyMu z A α τ := by
  rw [mcCarthyLambdaMu, ← Category.assoc, mcCarthyArMotion_one]
  rfl

/-- 概要：上辺の prism は全ての面・退化の制限と両立する。
方針：Ar の prism の前合成の式。
規約：prism 全体の厳密な自然性。使われ方：ρ の単体恒等式。 -/
lemma mcCarthyLambdaMu_pre {l n m : ℕ} {C : SSet.{u}} [Quasicategory C]
    (z : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroVertex C) (A : arNerve m ⟶ C) (α : Fin (n + 1) →o Fin (m + 1))
    (τ : Fin (n + 1) →o Fin 2) (σ : Fin (l + 1) →o Fin (n + 1)) :
    (Δ[1] ◁ arNerveMap σ) ≫ mcCarthyLambdaMu z A α τ =
      mcCarthyLambdaMu z A (α.comp σ) (τ.comp σ) := by
  rw [mcCarthyLambdaMu, ← Category.assoc, mcCarthyArMotion_pre]
  rfl

/-- 概要：λ 図式は gapped 図式から gapped 図式を作る。
方針：添字制限と標準零 cofiber 関手の完全性。
規約：C は安定な quasicategory。使われ方：span を S_n に持ち上げる頂点条件。 -/
lemma mcCarthyLambda_isGapped {n m : ℕ} {C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C]
    (z : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroVertex C) (A : arNerve m ⟶ C) (hA : IsGapped A)
    (α : Fin (n + 1) →o Fin (m + 1)) : IsGapped (mcCarthyLambda z A α) :=
  (hA.precomp α).postcomp _ (zeroCofiberFunctor_preservesSConstructionData z false)

/-- 概要：μ 図式も gapped 図式から gapped 図式を作る。
方針：動かした添字で λ の保存を適用する。
規約：全ての時刻の単体を含む。使われ方：span の終点の頂点条件。 -/
lemma mcCarthyMu_isGapped {n m : ℕ} {C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C]
    (z : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroVertex C) (A : arNerve m ⟶ C) (hA : IsGapped A)
    (α : Fin (n + 1) →o Fin (m + 1)) (τ : Fin (n + 1) →o Fin 2) :
    IsGapped (mcCarthyMu z A α τ) := mcCarthyLambda_isGapped z A hA _

/-- 概要：時刻の単体が全て零なら上辺の変換は λ で一定。
方針：Ar の零時刻の prism の式を後合成する。
規約：頂点の等号だけでなく変換の厳密な等号。使われ方：ρ の恒等押し出しの正規化。 -/
lemma mcCarthyLambdaMu_timeZero {n m : ℕ} {C : SSet.{u}} [Quasicategory C]
    (z : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroVertex C) (A : arNerve m ⟶ C) (α : Fin (n + 1) →o Fin (m + 1)) :
    mcCarthyLambdaMu z A α (OrderHom.const _ 0) =
      CartesianMonoidalCategory.snd (Δ[1] : SSet.{u}) (arNerve n) ≫ mcCarthyLambda z A α := by
  rw [mcCarthyLambdaMu, mcCarthyArMotion_timeZero, Category.assoc]
  rfl

end SerrePositivity.KST.SConstruction
