module

public import SerrePositivity.AlgebraicGeometry.LocalGenericDetection
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Localization.LocalizationLocalization

/-!
概要：KST §5、Stacks 0810・05DH の局所基底上の一般点局所環と元の代数の局所化の比較。
方針：拡大素点の縮約を計算し、二段階の局所化の普遍条件を使う。
規約：B の作用は実際の環写像から明示的に選ぶ。
使われ方：一般点局所環の族による消滅検出を元の表示行列の局所化へ接続する。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry
open scoped TensorProduct

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
  [IsNoetherianRing A] [Module.Flat A B] [Algebra.FinitePresentation A B]
  [GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap A B)))]

/--
概要：局所基底上の一般点局所環への元の代数の作用。
方針：実際の環写像から代数構造を選ぶ。
規約：KST §5、Stacks 0810・05DH、大域インスタンスにはしない。
使われ方：二段階の局所化のスカラー塔と代数同型。
-/
@[instance_reducible]
def localGenericAlgebra (P : PrimeSpectrum A) : Algebra B (LocalGenericRing A B P) :=
  (localGenericMap A B P).toAlgebra

/--
概要：元の代数から局所基底変更環を経由する作用は一般点局所環上でスカラー塔をなす。
方針：実際の環写像の合成の定義を使う。
規約：KST §5、Stacks 0810・05DH、右因子からの作用を明示する。
使われ方：局所化を二段階で行う普遍条件の適用。
-/
theorem localGenericAlgebra_isScalarTower (P : PrimeSpectrum A) :
    letI : Algebra B ((Localization.AtPrime P.asIdeal) ⊗[A] B) :=
      Algebra.TensorProduct.rightAlgebra
    letI : Algebra B (LocalGenericRing A B P) := localGenericAlgebra A B P
    IsScalarTower B ((Localization.AtPrime P.asIdeal) ⊗[A] B) (LocalGenericRing A B P) := by
  let : Algebra B ((Localization.AtPrime P.asIdeal) ⊗[A] B) :=
    Algebra.TensorProduct.rightAlgebra
  let : Algebra B (LocalGenericRing A B P) := localGenericAlgebra A B P
  infer_instance

/--
概要：局所基底上の閉ファイバー一般点を元の代数へ縮約すると元の拡大素点となる。
方針：極大イデアルの拡大を元の拡大素点の像へ書き換え、局所化の拡大縮約を使う。
規約：KST §5、Stacks 0810・05DH、分裂表示はこの比較には不要。
使われ方：一般点局所環を元の代数の局所化として同定する。
-/
theorem localizedBaseGenericPrime_comap (P : PrimeSpectrum A) :
    letI : Algebra B ((Localization.AtPrime P.asIdeal) ⊗[A] B) :=
      Algebra.TensorProduct.rightAlgebra
    (localizedBaseGenericPrime A B P).asIdeal.comap
      (algebraMap B ((Localization.AtPrime P.asIdeal) ⊗[A] B)) =
        (geometricallyIntegralGenericPrime A B P).asIdeal := by
  let C := Localization.AtPrime P.asIdeal
  let D := C ⊗[A] B
  let : Algebra B D := Algebra.TensorProduct.rightAlgebra
  let Q := (geometricallyIntegralGenericPrime A B P).asIdeal
  let : (P.asIdeal.map (algebraMap A B)).IsPrime :=
    ideal_map_isPrime_of_geometricallyIntegral A B P.asIdeal
  let T := Algebra.algebraMapSubmonoid B P.asIdeal.primeCompl
  have hQ : Q.comap (algebraMap A B) = P.asIdeal :=
    congrArg PrimeSpectrum.asIdeal (geometricallyIntegralGenericPrime_comap A B P)
  have hdis : Disjoint (T : Set B) (Q : Set B) := by
    rw [Set.disjoint_left]
    rintro b ⟨a, ha, rfl⟩ hb
    have haQ : a ∈ Q.comap (algebraMap A B) := hb
    rw [hQ] at haQ
    exact ha haQ
  change ((IsLocalRing.maximalIdeal C).map (algebraMap C D)).comap (algebraMap B D) = Q
  rw [← Localization.AtPrime.map_eq_maximalIdeal (I := P.asIdeal), Ideal.map_map,
    ← IsScalarTower.algebraMap_eq A C D, IsScalarTower.algebraMap_eq A B D,
    ← Ideal.map_map]
  exact IsLocalization.under_map_of_isPrime_disjoint T D inferInstance hdis

/--
概要：局所基底上の一般点局所環は元の代数の拡大素点による局所化である。
方針：二段階の局所化の普遍条件に縮約素点の等式を適用する。
規約：KST §5、Stacks 0810・05DH、元の代数の作用を明示して述べる。
使われ方：元の代数の標準的な素点局所化との実際の同型。
-/
theorem localGenericAlgebra_isLocalization (P : PrimeSpectrum A) :
    letI : Algebra B (LocalGenericRing A B P) := localGenericAlgebra A B P
    IsLocalization.AtPrime (LocalGenericRing A B P)
      (geometricallyIntegralGenericPrime A B P).asIdeal := by
  let C := Localization.AtPrime P.asIdeal
  let D := C ⊗[A] B
  let : Algebra B D := Algebra.TensorProduct.rightAlgebra
  let : Algebra B (LocalGenericRing A B P) := localGenericAlgebra A B P
  let : IsScalarTower B D (LocalGenericRing A B P) := localGenericAlgebra_isScalarTower A B P
  let : @IsScalarTower B D (LocalGenericRing A B P)
      (inferInstance : Algebra B D).toSMul
      (inferInstance : Algebra D (LocalGenericRing A B P)).toSMul
      (localGenericAlgebra A B P).toSMul :=
    IsScalarTower.of_algebraMap_eq' (R := B) (S := D) (A := LocalGenericRing A B P) rfl
  have h := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
    (Algebra.algebraMapSubmonoid B P.asIdeal.primeCompl)
    (T := LocalGenericRing A B P) (localizedBaseGenericPrime A B P).asIdeal
  have hs : ((localizedBaseGenericPrime A B P).asIdeal.comap (algebraMap B D)).primeCompl =
      (geometricallyIntegralGenericPrime A B P).asIdeal.primeCompl := by
    ext b
    change b ∉ (localizedBaseGenericPrime A B P).asIdeal.comap (algebraMap B D) ↔
      b ∉ (geometricallyIntegralGenericPrime A B P).asIdeal
    rw [localizedBaseGenericPrime_comap A B P]
  change IsLocalization ((localizedBaseGenericPrime A B P).asIdeal.comap
    (algebraMap B D)).primeCompl (LocalGenericRing A B P) at h
  rw [hs] at h
  exact h

/--
概要：局所基底上の一般点局所環と元の代数の拡大素点局所化との実際の代数同型。
方針：同じ乗法的集合による二つの局所化の一意性を使う。
規約：KST §5、Stacks 0810・05DH、同型は元の代数 B 上で取る。
使われ方：局所的な階数と消滅判定を二つの対象の間で運ぶ。
-/
def localGenericComparison (P : PrimeSpectrum A) :
    letI : Algebra B (LocalGenericRing A B P) := localGenericAlgebra A B P
    LocalGenericRing A B P ≃ₐ[B]
      Localization.AtPrime (geometricallyIntegralGenericPrime A B P).asIdeal := by
  let : Algebra B (LocalGenericRing A B P) := localGenericAlgebra A B P
  let : IsLocalization.AtPrime (LocalGenericRing A B P)
      (geometricallyIntegralGenericPrime A B P).asIdeal := localGenericAlgebra_isLocalization A B P
  exact IsLocalization.algEquiv (geometricallyIntegralGenericPrime A B P).asIdeal.primeCompl _ _

/--
概要：一般点局所環の比較同型は元の代数からの環写像を保つ。
方針：実際の B 代数同型の係数保存を使う。
規約：KST §5、Stacks 0810・05DH、比較の向きを局所基底側から元の代数側へ固定する。
使われ方：元やイデアルの像の消滅を比較する。
-/
theorem localGenericComparison_map (P : PrimeSpectrum A) (b : B) :
    letI : Algebra B (LocalGenericRing A B P) := localGenericAlgebra A B P
    localGenericComparison A B P (localGenericMap A B P b) =
      algebraMap B (Localization.AtPrime (geometricallyIntegralGenericPrime A B P).asIdeal) b := by
  let : Algebra B (LocalGenericRing A B P) := localGenericAlgebra A B P
  exact (localGenericComparison A B P).commutes b

variable {ι : Type*} (e : B →ₗ[A] (ι →₀ A)) (p : (ι →₀ A) →ₗ[A] B)
  (hpe : p.comp e = LinearMap.id)

include e p hpe

/--
概要：元の代数の拡大素点による局所化の族は分裂代数の元を検出する。
方針：局所基底上の一般点局所環との実同型で既証の写像の族の単射性へ戻す。
規約：KST §5、Stacks 0810・05DH、元の代数の実分裂を入力する。
使われ方：高次小行列式の消滅を B_(PB) の族で検出する。
-/
theorem genericPrimeMap_family_injective :
    Function.Injective (fun b : B => fun P : PrimeSpectrum A =>
      algebraMap B (Localization.AtPrime (geometricallyIntegralGenericPrime A B P).asIdeal) b) := by
  intro x y hxy
  apply localGenericMap_family_injective A B e p hpe
  funext P
  let : Algebra B (LocalGenericRing A B P) := localGenericAlgebra A B P
  apply (localGenericComparison A B P).injective
  rw [localGenericComparison_map, localGenericComparison_map]
  exact congrFun hxy P

/--
概要：全ての拡大素点局所化で像が零イデアルなら元のイデアルも零。
方針：元の代数から拡大素点局所化の族への単射性を各イデアル元に使う。
規約：KST §5、Stacks 0810・05DH、イデアルの有限生成性は不要。
使われ方：一定の一般階数から高次小行列式イデアルの消滅を導く。
-/
theorem ideal_eq_bot_of_genericPrime_maps_eq_bot (J : Ideal B)
    (hJ : ∀ P : PrimeSpectrum A,
      J.map (algebraMap B
        (Localization.AtPrime (geometricallyIntegralGenericPrime A B P).asIdeal)) = ⊥) :
    J = ⊥ := by
  apply bot_unique
  intro b hb
  apply (Ideal.mem_bot).mpr
  apply genericPrimeMap_family_injective A B e p hpe
  funext P
  change algebraMap B
      (Localization.AtPrime (geometricallyIntegralGenericPrime A B P).asIdeal) b =
    algebraMap B (Localization.AtPrime (geometricallyIntegralGenericPrime A B P).asIdeal) 0
  rw [map_zero]
  have hmem := Ideal.mem_map_of_mem
    (algebraMap B (Localization.AtPrime (geometricallyIntegralGenericPrime A B P).asIdeal)) hb
  rw [hJ P] at hmem
  exact (Ideal.mem_bot).mp hmem

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
