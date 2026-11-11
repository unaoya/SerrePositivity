module

public import SerrePositivity.HomologicalAlgebra.UnboundedSemifreeModel
public import SerrePositivity.CommutativeAlgebra.Koszul.UnboundedTensor
public import SerrePositivity.HomologicalAlgebra.RestrictedBaseChangeComplex

/-!
# 鎖複体の実際の模型上の完全 Tor 振幅

## 概要
任意の非有界複体の半自由分解上で、標的の有限 Koszul 複体を施したときの下界を指定する。

## 方針
既存の半自由模型と通常の底変換をそのまま使う。

## 規約
BS 著者版 Construction 6.1、Lemma 4.22 の古典的な入力。∞ 圏の対象を型に含めない。

## 使われ方
完全 Tor 上界三を、全ての半自由分解に対する主張として渡す。
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits DifferentialGraded InfinityCategories

variable {R S : Type u} [CommRing R] [CommRing S]

/-- 概要：実際の半自由模型上での完全 Tor 振幅の上界。
方針：全ての分解射について、底変換後の Koszul 模型のホモロジーを評価する。
規約：BS 著者版 Construction 6.1。複体は上に有界とは限らない。
使われ方：∞ 側の有限振幅への接続の古典的な入力。 -/
@[expose] def HasCochainCompleteTorAmplitude (f : R →+* S) {r : ℕ} (x : Fin r → R) (c : ℕ) : Prop :=
  ∀ (L K : CochainComplex (ModuleCat.{u} R) ℤ) (q : L ⟶ K), QuasiIso q →
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree R L → ∀ (m : ℤ),
      (∀ i : ℤ, i < m → IsZero (K.homology i)) →
        ∀ i : ℤ, i < m - (c : ℤ) →
          IsZero ((koszulComplexOn (f ∘ x) (baseChange f L)).homology i)

/-- 概要：振幅の上界があれば、任意の非有界入力に実在する評価模型がある。
方針：既存の半自由分解を選び、全ての分解を検査する振幅の条件を適用する。
規約：BS 著者版 Construction 6.1。模型の存在を仮定しない。
使われ方：完全振幅の数値上界を任意の入力へ適用する。 -/
theorem exists_cochainCompleteTor_model (f : R →+* S) {r : ℕ} (x : Fin r → R) (c : ℕ)
    (hf : HasCochainCompleteTorAmplitude f x c)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (m : ℤ)
    (hK : ∀ i : ℤ, i < m → IsZero (K.homology i)) :
    ∃ (L : CochainComplex (ModuleCat.{u} R) ℤ) (q : L ⟶ K), QuasiIso q ∧
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree R L ∧ complexKFlat R L ∧ complexKFlat S (baseChange f L) ∧
        ∀ i : ℤ, i < m - (c : ℤ) →
          IsZero ((koszulComplexOn (f ∘ x) (baseChange f L)).homology i) := by
  obtain ⟨L, q, hL, hq, _, hFlat, hBase⟩ := exists_unbounded_baseChange_model f K
  exact ⟨L, q, hq, hL, hFlat, hBase, hf L K q hq hL m hK⟩

end SerrePositivity
