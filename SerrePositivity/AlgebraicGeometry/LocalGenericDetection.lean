module

public import SerrePositivity.AlgebraicGeometry.GeometricallyIntegralFiberRegularity
public import SerrePositivity.AlgebraicGeometry.SplitAlgebraTensorCoefficients
public import Mathlib.RingTheory.Spectrum.Maximal.Localization

/-!
概要：KST §5、Stacks 0810・05DH の特別な局所化の族による等式の検出。
方針：基礎環を各素点で局所化し、閉ファイバーの一般点へ移して全係数を検出する。
規約：途中のテンソル積環とその一般点局所化を実際に構成する。
使われ方：高次小行列式の消滅を特別な局所環の族から元の代数へ戻す。
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
概要：基礎環を素点で局所化した後の閉ファイバーの一般点。
方針：テンソル基底変更の幾何学的整性から拡大極大イデアルを素点とする。
規約：KST §5、Stacks 0810・05DH、基底変更先の環を明示する。
使われ方：消滅判定に用いる局所環の定義。
-/
def localizedBaseGenericPrime (P : PrimeSpectrum A) :
    PrimeSpectrum ((Localization.AtPrime P.asIdeal) ⊗[A] B) := by
  let C := Localization.AtPrime P.asIdeal
  let D := C ⊗[A] B
  let : GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap C D))) :=
    geometricallyIntegral_tensorProjection A B C
  exact geometricallyIntegralGenericPrime C D ⟨IsLocalRing.maximalIdeal C, inferInstance⟩

/--
概要：局所化した基礎環の閉ファイバーの一般点における実際の局所環。
方針：構成した素イデアルでテンソル基底変更環を局所化する。
規約：KST §5、Stacks 0810・05DH、元の代数の局所化との同一視は定義に含めない。
使われ方：元の代数の元を検出する写像の終域。
-/
abbrev LocalGenericRing (P : PrimeSpectrum A) :=
  Localization.AtPrime (localizedBaseGenericPrime A B P).asIdeal

/--
概要：元の代数から局所基底上の一般点局所環への実際の環写像。
方針：テンソル積への右因子の包含と一般点局所化を合成する。
規約：KST §5、Stacks 0810・05DH、環準同型として保持する。
使われ方：全素点を通じた等式の検出。
-/
def localGenericMap (P : PrimeSpectrum A) : B →+* LocalGenericRing A B P :=
  (algebraMap ((Localization.AtPrime P.asIdeal) ⊗[A] B) (LocalGenericRing A B P)).comp
    Algebra.TensorProduct.includeRight.toRingHom

variable {ι : Type*} (e : B →ₗ[A] (ι →₀ A)) (p : (ι →₀ A) →ₗ[A] B)
  (hpe : p.comp e = LinearMap.id)

include e p hpe

/--
概要：局所基底上のテンソル代数からその閉ファイバーの一般点局所環への写像は単射。
方針：分裂表示を基底変更し、局所基礎環上の既証の単射性を適用する。
規約：KST §5、Stacks 0810・05DH、任意の基礎素点を扱う。
使われ方：一般点局所環での等式を基底変更代数へ戻す。
-/
theorem localGeneric_structureMap_injective (P : PrimeSpectrum A) :
    Function.Injective (algebraMap ((Localization.AtPrime P.asIdeal) ⊗[A] B)
      (LocalGenericRing A B P)) := by
  let C := Localization.AtPrime P.asIdeal
  let D := C ⊗[A] B
  let : GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap C D))) :=
    geometricallyIntegral_tensorProjection A B C
  exact geometricallyIntegral_split_extendedMaximalLocalization_injective C D
    (splitAlgebraTensorEmbedding (C := C) e) (splitAlgebraTensorRetraction (C := C) p)
    (splitAlgebraTensorRetraction_comp_embedding e p hpe)

/--
概要：全基礎素点の一般点局所環への像は元の分裂代数の元を検出する。
方針：各局所基底上での単射性と全素点局所化による各係数の検出を使う。
規約：KST §5、Stacks 0810・05DH、基礎環上の実際の分裂表示を入力する。
使われ方：局所的に消えた高次小行列式を元の代数で零とする。
-/
theorem localGenericMap_family_injective :
    Function.Injective (fun b : B => fun P : PrimeSpectrum A => localGenericMap A B P b) := by
  intro x y hxy
  have he : e x = e y := by
    ext i
    apply PrimeSpectrum.toPiLocalization_injective A
    funext P
    let C := Localization.AtPrime P.asIdeal
    change algebraMap A C (e x i) = algebraMap A C (e y i)
    have hP := congrFun hxy P
    change algebraMap (C ⊗[A] B) (LocalGenericRing A B P) ((1 : C) ⊗ₜ[A] x) =
      algebraMap (C ⊗[A] B) (LocalGenericRing A B P) ((1 : C) ⊗ₜ[A] y) at hP
    have hD := localGeneric_structureMap_injective A B e p hpe P hP
    have hc := congrArg (fun z : C ⊗[A] B => splitAlgebraTensorEmbedding e z i) hD
    simpa only [splitAlgebraTensorEmbedding_tmul, mul_one] using hc
  have hp := congrArg p he
  simpa only [← LinearMap.comp_apply, hpe, LinearMap.id_apply] using hp

/--
概要：全基礎素点の一般点局所環で像が零の元は零。
方針：実際の環写像の族の単射性を零との比較に適用する。
規約：KST §5、Stacks 0810・05DH、実分裂の下で述べる。
使われ方：小行列式などの局所的消滅の検出。
-/
theorem eq_zero_of_localGenericMap_eq_zero (b : B)
    (hb : ∀ P : PrimeSpectrum A, localGenericMap A B P b = 0) : b = 0 := by
  apply localGenericMap_family_injective A B e p hpe
  funext P
  simpa only [map_zero] using hb P

/--
概要：全基礎素点の一般点局所環への像が零イデアルなら元のイデアルも零。
方針：各イデアル元の像を拡大イデアルに入れ、環写像の族による消滅判定を使う。
規約：KST §5、Stacks 0810・05DH、イデアルの有限生成性は不要。
使われ方：局所自由階数から高次小行列式イデアルの消滅を得る。
-/
theorem ideal_eq_bot_of_localGeneric_maps_eq_bot (J : Ideal B)
    (hJ : ∀ P : PrimeSpectrum A, J.map (localGenericMap A B P) = ⊥) : J = ⊥ := by
  apply bot_unique
  intro b hb
  apply (Ideal.mem_bot).mpr
  apply eq_zero_of_localGenericMap_eq_zero A B e p hpe
  intro P
  have hmem := Ideal.mem_map_of_mem (localGenericMap A B P) hb
  rw [hJ P] at hmem
  exact (Ideal.mem_bot).mp hmem

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
