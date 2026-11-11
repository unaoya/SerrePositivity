module

public import SerrePositivity.CommutativeAlgebra.Koszul.Resolution
public import SerrePositivity.HomologicalAlgebra.CochainTensor.Cone
public import SerrePositivity.DifferentialGraded.Tensor.Enriched
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ComplexCompletion.Basic

/-!
# 有限 Koszul 複体と非有界テンソル模型

## 概要
有限 Koszul 複体の K-flat 性、任意の複体とのテンソルの反復錐表示と次数の下界を与える。

## 方針
単位複体から有限回の写像錐を取り、テンソルと錐の比較を使う。

## 規約
上に有界という制約を置かない。BS 著者版 Construction 6.1 の Tor 振幅の入力。

## 使われ方
正則列の商の導来テンソルを、実際の非有界複体の模型で計算する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open DerivedCompletion DifferentialGraded

variable {R : Type u} [CommRing R]

/-- 概要：有限 Koszul 複体は任意の非有界 acyclic 複体とのテンソルを消す。
方針：単位複体からの錐による有限帰納法。
規約：正則性を仮定しない。
使われ方：BS 著者版 Construction 6.1 の非有界な模型の比較。 -/
theorem koszulComplex_isKFlat : ∀ {r : ℕ} (x : Fin r → R), complexKFlat R (koszulComplex x)
  | 0, _ => complexKFlat_unit R
  | r + 1, x => complexKFlat_cone R
      (smulId (x (Fin.last r)) (koszulComplex (Fin.init x)))
      (koszulComplex_isKFlat (Fin.init x)) (koszulComplex_isKFlat (Fin.init x))

/-- 概要：Koszul 複体と任意の複体の全テンソルは反復スカラー錐と同型。
方針：テンソルと写像錐を交換し、各段で既存の比較を適用する。
規約：BS 著者版 Construction 6.1 の通常の鎖複体の模型。
使われ方：実際の導来テンソルの下界の評価。 -/
def koszulCochainTensorIso : ∀ {r : ℕ} (x : Fin r → R)
    (K : CochainComplex (ModuleCat.{u} R) ℤ),
    cochainTensor (koszulComplex x) K ≅ koszulComplexOn x K
  | 0, _, K => cochainTensorLeftUnitor K
  | r + 1, x, K => by
    let a := x (Fin.last r)
    let L := koszulComplex (Fin.init x)
    have he : cochainTensorMap (smulId a L) (𝟙 K) = smulId a (cochainTensor L K) := by
      change cochainTensorMap (a • 𝟙 L) (𝟙 K) = a • 𝟙 (cochainTensor L K)
      rw [cochainTensorMap_smul_left]
      have hid : cochainTensorMap (𝟙 L) (𝟙 K) = 𝟙 (cochainTensor L K) := by
        exact ((cochainTensorFixedRight K).map_id L)
      rw [hid]
    have heCone : CochainComplex.mappingCone (cochainTensorMap (smulId a L) (𝟙 K)) =
        (scalarConeFunctor a).obj (cochainTensor L K) := by
      rw [he]
      rfl
    exact cochainTensorConeLeft (smulId a L) K ≪≫
      eqToIso heCone ≪≫
      (scalarConeFunctor a).mapIso (koszulCochainTensorIso (Fin.init x) K)

/-- 概要：r 元の Koszul 反復はコホモロジーの下界を高々 r 下げる。
方針：写像錐の長完全列で有限帰納する。
規約：元の複体は任意、BS 著者版 Construction 6.1 の振幅の評価。
使われ方：上に有界でない入力を含む下界の評価。 -/
theorem koszulComplexOn_homology_isZero_below
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (m : ℤ)
    (hK : ∀ i : ℤ, i < m → IsZero (K.homology i)) :
    ∀ {r : ℕ} (x : Fin r → R) (i : ℤ), i < m - (r : ℤ) →
      IsZero ((koszulComplexOn x K).homology i)
  | 0, _, i, hi => hK i (by omega)
  | r + 1, x, i, hi =>
    (Cone.exact₃ (smulId (x (Fin.last r)) (koszulComplexOn (Fin.init x) K))
      i (i + 1) rfl).isZero_X₂
        ((koszulComplexOn_homology_isZero_below K m hK (Fin.init x) i (by omega)).eq_zero_of_src _)
        ((koszulComplexOn_homology_isZero_below K m hK (Fin.init x) (i + 1) (by omega)).eq_zero_of_tgt _)

/-- 概要：K-flat な分解を用いると、Koszul 商の計算の二つの標準比較は擬同型。
方針：左の有限自由 Koszul 複体と右の K-flat 複体で、それぞれ準同型を保つ。
規約：BS 著者版 Construction 6.1。任意の非有界複体と実際の分解射を入力する。
使われ方：反復錐模型が導来テンソルを計算することの照合。 -/
theorem koszulTensor_resolution_comparisons
    {r : ℕ} (x : Fin r → R) (hx : IsKoszulResolution x)
    {P K : CochainComplex (ModuleCat.{u} R) ℤ} (q : P ⟶ K) [QuasiIso q]
    (hP : complexKFlat R P) :
    QuasiIso (cochainTensorMap (𝟙 (koszulComplex x)) q) ∧
      QuasiIso (cochainTensorMap (koszulAugmentation hx) (𝟙 P)) :=
  ⟨complexKFlat_quasiIso_right R (koszulComplex_isKFlat x) q,
    complexKFlat_quasiIso_left R hP (koszulAugmentation hx)⟩

end SerrePositivity
