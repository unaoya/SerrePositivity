module

public import SerrePositivity.AlgebraicGeometry.BoundaryTorsionLocalization
public import Mathlib.Algebra.Module.LocalizedModule.IsLocalization
public import Mathlib.RingTheory.Flat.Localization

/-!
概要：KST §5、Stacks 0815 の加群の純変換と係数環の局所化の可換性。
方針：商の間の実際の写像について、局所化の三つの普遍条件を確認する。
規約：境界元の正則性・Noether 性・有限性を要求しない。
使われ方：生成元チャートから任意のチャートへ純変換の平坦性を移す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry

variable {R A M N : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [Module A N] [IsScalarTower R A N]

/--
概要：加群の純変換から係数環を拡大した加群の純変換への写像。
方針：境界ねじれを保つ線形写像を商へ降ろす。
規約：KST §5、Stacks 0815、対象側は拡大した環上で商を取る。
使われ方：局所化の場合の実際の比較写像。
-/
def pureTransformBaseLocalizationMap (f : R) (η : M →ₗ[R] N) :
    modulePureTransform f M →ₗ[R] modulePureTransform (algebraMap R A f) N :=
  (boundaryTorsion f M).liftQ
    (((boundaryTorsion (algebraMap R A f) N).mkQ.restrictScalars R).comp η) (by
      intro m hm
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      exact (mem_boundaryTorsion_algebraMap_iff (A := A) f (η m)).mpr
        (boundaryTorsion_map_le f η hm))

/--
概要：純変換の係数拡大の比較写像は代表元の写像を保つ。
方針：商への降下の定義を使う。
規約：KST §5、Stacks 0815、元の環上線形な式。
使われ方：局所化の普遍条件の検証。
-/
theorem pureTransformBaseLocalizationMap_mk (f : R) (η : M →ₗ[R] N) (m : M) :
    pureTransformBaseLocalizationMap (A := A) f η (Submodule.Quotient.mk m) =
      Submodule.Quotient.mk (η m) := rfl

/--
概要：局所化された係数環上の純変換は元の純変換の局所化。
方針：単元の作用、代表元の分母消去、境界ねじれの所属判定を使う。
規約：KST §5、Stacks 0815、元の加群の局所化写像を指定する。
使われ方：開チャートの重なりで純変換を比較する。
-/
instance pureTransformBaseLocalizationMap_isLocalizedModule
    (S : Submonoid R) [IsLocalization S A] (f : R) (η : M →ₗ[R] N)
    [IsLocalizedModule S η] :
    IsLocalizedModule S (pureTransformBaseLocalizationMap (A := A) f η) where
  map_units s := by
    rw [Module.End.isUnit_iff]
    change Function.Bijective (fun q : modulePureTransform (algebraMap R A f) N => s.val • q)
    have hs : IsUnit (algebraMap R A s.val) := IsLocalization.map_units A s
    simpa only [algebraMap_smul] using
      (hs.smul_bijective : Function.Bijective
        (fun q : modulePureTransform (algebraMap R A f) N => algebraMap R A s.val • q))
  surj y := by
    obtain ⟨n, rfl⟩ := Submodule.Quotient.mk_surjective
      (boundaryTorsion (algebraMap R A f) N) y
    obtain ⟨⟨m, s⟩, hs⟩ := IsLocalizedModule.surj S η n
    refine ⟨⟨Submodule.Quotient.mk m, s⟩, ?_⟩
    change s.val • (Submodule.Quotient.mk n : modulePureTransform (algebraMap R A f) N) =
      Submodule.Quotient.mk (η m)
    rw [← Submodule.Quotient.mk_smul]
    exact congrArg Submodule.Quotient.mk hs
  exists_of_eq {x y} hxy := by
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective (boundaryTorsion f M) x
    obtain ⟨k, rfl⟩ := Submodule.Quotient.mk_surjective (boundaryTorsion f M) y
    change (Submodule.Quotient.mk (η m) : modulePureTransform (algebraMap R A f) N) =
      Submodule.Quotient.mk (η k) at hxy
    have ht := (Submodule.Quotient.eq (boundaryTorsion (algebraMap R A f) N)).mp hxy
    have htR : η (m - k) ∈ boundaryTorsion f N := by
      apply (mem_boundaryTorsion_algebraMap_iff (A := A) f _).mp
      simpa only [η.map_sub] using ht
    obtain ⟨s, hs⟩ := (localized_mem_boundaryTorsion_iff S f η (m - k)).mp htR
    refine ⟨s, ?_⟩
    change s.val • (Submodule.Quotient.mk m : modulePureTransform f M) =
      s.val • Submodule.Quotient.mk k
    rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul]
    apply (Submodule.Quotient.eq _).mpr
    simpa only [smul_sub] using hs

/--
概要：純変換の局所化と局所化先の純変換の実際の線形同型。
方針：二つの局所化写像の普遍条件を比較する。
規約：KST §5、Stacks 0815、元の環上線形な比較。
使われ方：チャートの重なりでの純変換の同定。
-/
def pureTransformBaseLocalizationEquiv (S : Submonoid R) [IsLocalization S A]
    (f : R) (η : M →ₗ[R] N) [IsLocalizedModule S η] :
    LocalizedModule S (modulePureTransform f M) ≃ₗ[R]
      modulePureTransform (algebraMap R A f) N :=
  IsLocalizedModule.linearEquiv S
    (LocalizedModule.mkLinearMap S (modulePureTransform f M))
    (pureTransformBaseLocalizationMap (A := A) f η)

/--
概要：平坦な純変換は係数局所化後も平坦。
方針：純変換の比較写像が局所化であることから平坦性を保存する。
規約：KST §5、Stacks 0815、平坦性はそれぞれの係数環について主張する。
使われ方：自由化された生成元チャートからその基本開部分への平坦性の移送。
-/
theorem pureTransformBaseLocalization_flat (S : Submonoid R) [IsLocalization S A]
    (f : R) (η : M →ₗ[R] N) [IsLocalizedModule S η]
    [Module.Flat R (modulePureTransform f M)] :
    Module.Flat A (modulePureTransform (algebraMap R A f) N) :=
  Module.Flat.of_isLocalizedModule A S (pureTransformBaseLocalizationMap (A := A) f η)

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
