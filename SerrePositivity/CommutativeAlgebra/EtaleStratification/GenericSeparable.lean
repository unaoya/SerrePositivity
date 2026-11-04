module

public import SerrePositivity.CommutativeAlgebra.EtaleStratification.FiniteFieldProduct
public import SerrePositivity.CommutativeAlgebra.EtaleStratification.Factorization
public import Mathlib.RingTheory.Localization.Pi

/-!
# 一般点での純非分離部分の積

## 概要
有限個の有限純非分離体拡大の積の射は普遍同相。

## 方針
有限性と単射性から整性・Spec 全射性を得る。
体値点は一成分を経由し、冪等元で成分を特定した後に純非分離性による一意性を使う。

## 規約
積の射は成分ごとの構造射。

## 使われ方
一般点で取り出した分離部分の後半の射。
-/

@[expose] public section
noncomputable section
universe u

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.CommutativeAlgebra

/-- 有限純非分離体拡大の有限積は普遍同相。 -/
theorem isUniversalHomeomorphism_pi_of_isPurelyInseparable
    {ι : Type*} [Finite ι] (M L : ι → Type u)
    [∀ i, Field (M i)] [∀ i, Field (L i)] [∀ i, Algebra (M i) (L i)]
    [∀ i, Module.Finite (M i) (L i)] [∀ i, IsPurelyInseparable (M i) (L i)] :
    IsUniversalHomeomorphism (RingHom.pi (fun i ↦
      (algebraMap (M i) (L i)).comp (Pi.evalRingHom M i))) := by
  classical
  let : ∀ i, Algebra (∀ j, M j) (M i) := fun i ↦ (Pi.evalRingHom M i).toAlgebra
  let : ∀ i, Algebra (∀ j, M j) (L i) := fun i ↦
    ((algebraMap (M i) (L i)).comp (Pi.evalRingHom M i)).toAlgebra
  let : ∀ i, IsScalarTower (∀ j, M j) (M i) (L i) := fun _ ↦
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : ∀ i, Module.Finite (∀ j, M j) (M i) := fun i ↦ (finite_etale_pi_component M i).1
  let : ∀ i, Module.Finite (∀ j, M j) (L i) := fun i ↦ Module.Finite.trans (M i) (L i)
  let F := RingHom.pi (fun i ↦ (algebraMap (M i) (L i)).comp (Pi.evalRingHom M i))
  let : Algebra (∀ i, M i) (∀ i, L i) := F.toAlgebra
  let : Module (∀ i, M i) (∀ i, L i) := Pi.module ι L (∀ i, M i)
  let : Module.Finite (∀ i, M i) (∀ i, L i) := Module.Finite.pi
  have hFint : F.IsIntegral := by
    change (algebraMap (∀ i, M i) (∀ i, L i)).IsIntegral
    exact Algebra.IsIntegral.isIntegral
  have hFinj : Function.Injective F := by
    intro x y h
    funext i
    exact (algebraMap (M i) (L i)).injective (congrFun h i)
  apply isUniversalHomeomorphism_of_injective_fieldMaps F hFint (hFint.comap_surjective hFinj)
  intro K _ u v huv
  obtain ⟨i, a, ha⟩ := exists_field_factor L K u
  obtain ⟨j, b, hb⟩ := exists_field_factor L K v
  have hij : i = j := by
    by_contra hij
    have he := RingHom.congr_fun huv (Pi.single i (1 : M i))
    rw [← ha, ← hb] at he
    simpa [F, hij, Ne.symm hij] using he
  subst j
  have hab : a.comp (algebraMap (M i) (L i)) = b.comp (algebraMap (M i) (L i)) := by
    ext x
    have he := RingHom.congr_fun huv (Pi.single i x)
    rw [← ha, ← hb] at he
    simpa [F] using he
  have he : a = b := IsPurelyInseparable.injective_comp_algebraMap (M i) (L i) K hab
  rw [he] at ha
  exact ha.symm.trans hb

/-- 体の射は、p 可逆な場合に同型なら、p 反転後は常に同型。 -/
theorem invertPrimeMap_bijective_of_field {M L : Type u} [Field M] [Field L]
    (p : ℕ) (f : M →+* L) (hf : IsUnit (p : M) → Function.Bijective f) :
    Function.Bijective (invertPrimeMap p f) := by
  by_cases hp : (p : M) = 0
  · have hpL : (p : L) = 0 := by simpa only [map_natCast, map_zero] using congrArg f hp
    let : Subsingleton (Localization.Away (p : M)) := IsLocalization.subsingleton
      (M := Submonoid.powers (p : M)) (by rw [hp]; exact Submonoid.mem_powers 0)
    let : Subsingleton (Localization.Away (p : L)) := IsLocalization.subsingleton
      (M := Submonoid.powers (p : L)) (by rw [hpL]; exact Submonoid.mem_powers 0)
    exact ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun y ↦ ⟨0, Subsingleton.elim _ _⟩⟩
  · exact invertPrimeMap_bijective p f (hf (isUnit_iff_ne_zero.mpr hp))

/-- 成分ごとの p 反転後の同型は、有限積の p 反転後の同型を与える。 -/
theorem invertPrimeMap_pi_bijective {ι : Type*} [Finite ι]
    (M L : ι → Type u) [∀ i, CommRing (M i)] [∀ i, CommRing (L i)]
    (p : ℕ) (f : ∀ i, M i →+* L i) (hf : ∀ i, Function.Bijective (invertPrimeMap p (f i))) :
    Function.Bijective (invertPrimeMap p (RingHom.pi (fun i ↦ (f i).comp (Pi.evalRingHom M i)))) := by
  let M' (i : ι) := Localization.Away (p : M i)
  let L' (i : ι) := Localization.Away (p : L i)
  let : ∀ i, IsLocalization ((Submonoid.powers (p : ∀ i, M i)).map (Pi.evalRingHom M i))
      (M' i) := fun i ↦ by
    simp only [Submonoid.map_powers, map_natCast]
    infer_instance
  let : ∀ i, IsLocalization ((Submonoid.powers (p : ∀ i, L i)).map (Pi.evalRingHom L i))
      (L' i) := fun i ↦ by
    simp only [Submonoid.map_powers, map_natCast]
    infer_instance
  let : IsLocalization (Submonoid.powers (p : ∀ i, M i)) (∀ i, M' i) :=
    (IsLocalization.iff_map_piEvalRingHom M (∀ i, M' i) _).mpr inferInstance
  let : IsLocalization (Submonoid.powers (p : ∀ i, L i)) (∀ i, L' i) :=
    (IsLocalization.iff_map_piEvalRingHom L (∀ i, L' i) _).mpr inferInstance
  let eM := IsLocalization.algEquiv (Submonoid.powers (p : ∀ i, M i))
    (Localization.Away (p : ∀ i, M i)) (∀ i, M' i)
  let eL := IsLocalization.algEquiv (Submonoid.powers (p : ∀ i, L i))
    (Localization.Away (p : ∀ i, L i)) (∀ i, L' i)
  let F := RingHom.pi (fun i ↦ (f i).comp (Pi.evalRingHom M i))
  let F' := RingHom.pi (fun i ↦ (invertPrimeMap p (f i)).comp (Pi.evalRingHom M' i))
  have hF' : Function.Bijective F' := by
    constructor
    · intro x y he
      funext i
      exact (hf i).injective (congrFun he i)
    · intro y
      choose x hx using fun i ↦ (hf i).surjective (y i)
      exact ⟨x, funext hx⟩
  have he : eL.toRingHom.comp (invertPrimeMap p F) = F'.comp eM.toRingHom := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (p : ∀ i, M i))
    ext x i
    change eL (invertPrimeMap p F (algebraMap (∀ i, M i) _ x)) i =
      invertPrimeMap p (f i) (eM (algebraMap (∀ i, M i) _ x) i)
    rw [invertPrimeMap_algebraMap, eL.commutes, eM.commutes]
    change algebraMap (L i) (L' i) (f i (x i)) =
      invertPrimeMap p (f i) (algebraMap (M i) (M' i) (x i))
    exact (invertPrimeMap_algebraMap p (f i) (x i)).symm
  have hbij : Function.Bijective (eL.toRingHom.comp (invertPrimeMap p F)) := by
    rw [he]
    exact hF'.comp eM.bijective
  refine ⟨fun x y h ↦ hbij.injective (congrArg eL h), ?_⟩
  intro y
  obtain ⟨x, hx⟩ := hbij.surjective (eL y)
  exact ⟨x, eL.injective hx⟩

end SerrePositivity.CommutativeAlgebra
