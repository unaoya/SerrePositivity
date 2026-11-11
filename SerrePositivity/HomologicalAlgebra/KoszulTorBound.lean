module

public import SerrePositivity.HomologicalAlgebra.KoszulTorComparison
public import SerrePositivity.HomologicalAlgebra.TorSymmetry

/-!
# Koszul 分解の長さによる Tor の上界

## 概要
r 元の Koszul 分解を持つ商の Tor は r より大きい次数で消える。

## 方針
任意の係数加群とのテンソル模型の -r 次未満の項が零であることを使う。

## 規約
係数加群に正則性・有限性・完備性の条件を課さない。

## 使われ方
BS 著者版 Construction 6.1 の mod p の Tor 次元。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits MonoidalCategory

variable {R : Type u} [CommRing R]

/-- 概要：Koszul 分解を持つ商の Tor 次元は元の数以下。
方針：通常の射影分解と Tor の標準比較を使い、模型の零の項で評価する。
規約：任意の係数加群、BS 著者版 Construction 6.1 の一元商を含む。
使われ方：平坦射を後に合成する場合の Tor の上界。 -/
theorem torModule_koszulQuotient_subsingleton_of_length_lt
    {r : ℕ} (z : Fin r → R) (hz : IsKoszulResolution z)
    (M : ModuleCat.{u} R) (i : ℕ) (hi : r < i) :
    Subsingleton (TorModule R i (R ⧸ Ideal.span (Set.range z)) M) := by
  let Q := ModuleCat.of R (R ⧸ Ideal.span (Set.range z))
  let F := (tensoringLeft (ModuleCat.{u} R)).obj M
  have hX : IsZero (((koszulTensorModuleFunctor z).obj M).X (-(i : ℤ))) :=
    F.map_isZero (koszulComplex_isZero_X_of_lt z (-(i : ℤ)) (by omega))
  have hH := isZero_homology_of_isZero_X ((koszulTensorModuleFunctor z).obj M) (-(i : ℤ)) hX
  let e := (torComm i Q M).toModuleIso ≪≫ (koszulTorComparison z hz i).app M
  have hzH : IsZero ((koszulTensorModuleHomologyFunctor z i).obj M) := hH
  letI : Subsingleton ((koszulTensorModuleHomologyFunctor z i).obj M) :=
    ModuleCat.subsingleton_of_isZero hzH
  exact e.toLinearEquiv.injective.subsingleton

/-- 概要：同じ Tor の上界を商環への係数拡大の導来関手で述べる。
方針：一つの射影分解から通常の Tor と係数拡大の Tor を比較する。
規約：BS 著者版 Construction 6.1 の通常の振幅。
使われ方：商の後に平坦射を合成する場合。 -/
theorem torAlg_koszulQuotient_subsingleton_of_length_lt
    {r : ℕ} (z : Fin r → R) (hz : IsKoszulResolution z)
    (M : ModuleCat.{u} R) (i : ℕ) (hi : r < i) :
    Subsingleton (TorAlg (Ideal.Quotient.mk (Ideal.span (Set.range z))) i M) := by
  let Q := R ⧸ Ideal.span (Set.range z)
  let P := extRes (projectiveResolution M)
  have hP := isResolutionOf_extRes (projectiveResolution M)
  letI := torModule_koszulQuotient_subsingleton_of_length_lt z hz M i hi
  let e₁ := ordinaryTorIso (R := R) (T := Q) M P hP i
  letI : Subsingleton ((baseChange (algebraMap R Q) P).homology (-(i : ℤ))) :=
    e₁.injective.subsingleton
  exact (torIsoCochain (Ideal.Quotient.mk (Ideal.span (Set.range z))) hP i).toLinearEquiv.injective.subsingleton

/-- 概要：正則な主元による商の Tor は二次以上で消える。
方針：一元 Koszul 分解を長さの一般の判定に入力する。
規約：任意の係数加群、BS 著者版 Construction 6.1。
使われ方：mod p の式 (6) の最初の射。 -/
theorem torAlg_principalQuotient_subsingleton_of_one_lt
    (a : R) (ha : IsSMulRegular R a) (M : ModuleCat.{u} R) (i : ℕ) (hi : 1 < i) :
    Subsingleton (TorAlg (Ideal.Quotient.mk (Ideal.span {a})) i M) := by
  have hz : IsKoszulResolution (fun _ : Fin 1 => a) := by
    apply isKoszulResolution_of_isWeaklyRegular
    rw [show List.ofFn (fun _ : Fin 1 => a) = [a] by simp [List.ofFn_succ]]
    exact (RingTheory.Sequence.isWeaklyRegular_singleton_iff _ _).mpr ha
  have he : Set.range (fun _ : Fin 1 => a) = {a} := by ext x; simp
  have h := torAlg_koszulQuotient_subsingleton_of_length_lt (fun _ : Fin 1 => a) hz M i hi
  rw [he] at h
  exact h

end SerrePositivity
