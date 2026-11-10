module

public import SerrePositivity.HomologicalAlgebra.BicomplexRowQuasiIso
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.Algebra.Homology.TotalComplexSymmetry
import all SerrePositivity.HomologicalAlgebra.BicomplexComponents

/-!
# 第一象限双複体の列ごとの比較

## 概要
第一象限の列ごとの全射擬同型から総複体の擬同型を得る。

## 方針
核の列の完全性を総複体に移す。各総次数の直和は有限なので短完全性を保つ。

## 規約
横次数で符号付けした総複体を使う。

## 使われ方
pd de Rham 双複体を差座標のない定数列へ比較する。
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace SerrePositivity.HomologicalAlgebra

variable {R : Type u} [CommRing R]
local notation "up" => ComplexShape.up ℕ

private instance : TotalComplexShapeSymmetry up up up where
  symm a b := Nat.add_comm b a
  σ a b := (-1 : ℤˣ) ^ (a * b)
  σ_ε₁ := by
    rintro a _ rfl b
    change (-1 : ℤˣ) ^ (a * b) * 1 = (-1 : ℤˣ)^b * (-1 : ℤˣ)^((a + 1) * b)
    rw [Nat.add_mul, Nat.one_mul, pow_add, mul_one]
    rw [← mul_assoc, mul_comm ((-1 : ℤˣ)^b) ((-1 : ℤˣ)^(a * b)), mul_assoc,
      Int.units_mul_self, mul_one]
  σ_ε₂ := by
    rintro a b _ rfl
    change (-1 : ℤˣ) ^ (a * b) * (-1 : ℤˣ)^a = 1 * (-1 : ℤˣ)^(a * (b + 1))
    rw [Nat.mul_add, Nat.mul_one, pow_add, one_mul]

variable {K L : (HomologicalComplex₂ (ModuleCat.{u} R) up up)} (f : K ⟶ L)

private theorem total_map_component (n : ℕ) (t : totalIndex n) :
    (HomologicalComplex₂.total.map f up).f n ≫ componentAt L n t =
      componentAt K n t ≫ (f.f t.1.1).f t.1.2 := by
  apply HomologicalComplex₂.total.hom_ext
  intro a b h
  let s : totalIndex n := ⟨(a, b), h⟩
  change insertAt K n s ≫ (_ ≫ _) = insertAt K n s ≫ (_ ≫ _)
  have hm : insertAt K n s ≫ (HomologicalComplex₂.total.map f up).f n =
      (f.f s.1.1).f s.1.2 ≫ insertAt L n s := HomologicalComplex₂.ιTotal_map K L f up _ _ _ _
  rw [← Category.assoc, hm, Category.assoc, ← Category.assoc (insertAt K n s)]
  by_cases ht : s = t
  · subst t
    rw [insertAt_componentAt_eq, insertAt_componentAt_eq, Category.comp_id, Category.id_comp]
  · rw [insertAt_componentAt_ne L _ _ ht, insertAt_componentAt_ne K _ _ ht, comp_zero, zero_comp]

private theorem component_sum_insert (n : ℕ) (x : ∀ t : totalIndex n, (K.X t.1.1).X t.1.2)
    (t : totalIndex n) :
    componentAt K n t (∑ s : totalIndex n, insertAt K n s (x s)) = x t := by
  classical
  rw [map_sum, Finset.sum_eq_single t]
  · exact ConcreteCategory.congr_hom (insertAt_componentAt_eq K t) (x t)
  · intro s _ hs
    exact ConcreteCategory.congr_hom (insertAt_componentAt_ne K s t hs) (x s)
  · simp

private theorem total_map_injective (n : ℕ)
    (h : ∀ a b, Function.Injective ((f.f a).f b)) :
    Function.Injective ((HomologicalComplex₂.total.map f up).f n) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  apply totalComponent_ext_zero K
  intro a b hab
  let t : totalIndex n := ⟨(a, b), hab⟩
  apply h a b
  rw [map_zero]
  have hm := ConcreteCategory.congr_hom (total_map_component f n t) x
  change componentAt L n t ((HomologicalComplex₂.total.map f up).f n x) =
    (f.f a).f b (componentAt K n t x) at hm
  rw [hx, map_zero] at hm
  exact hm.symm

private theorem total_map_surjective (n : ℕ)
    (h : ∀ a b, Function.Surjective ((f.f a).f b)) :
    Function.Surjective ((HomologicalComplex₂.total.map f up).f n) := by
  classical
  intro x
  choose y hy using fun t : totalIndex n => h t.1.1 t.1.2 (componentAt L n t x)
  refine ⟨∑ t : totalIndex n, insertAt K n t (y t), ?_⟩
  apply sub_eq_zero.mp
  apply totalComponent_ext_zero L
  intro a b hab
  let t : totalIndex n := ⟨(a, b), hab⟩
  rw [map_sub]
  have hm := ConcreteCategory.congr_hom (total_map_component f n t)
    (∑ s : totalIndex n, insertAt K n s (y s))
  change componentAt L n t ((HomologicalComplex₂.total.map f up).f n
      (∑ s : totalIndex n, insertAt K n s (y s))) =
    (f.f a).f b (componentAt K n t (∑ s : totalIndex n, insertAt K n s (y s))) at hm
  rw [hm, component_sum_insert, hy t, sub_self]

variable {J : (HomologicalComplex₂ (ModuleCat.{u} R) up up)} {e : J ⟶ K} {g : K ⟶ L}

private theorem total_map_zero (h : e ≫ g = 0) :
    HomologicalComplex₂.total.map e up ≫ HomologicalComplex₂.total.map g up = 0 := by
  rw [← HomologicalComplex₂.total.map_comp, h]
  ext n : 1
  apply HomologicalComplex₂.total.hom_ext
  intro a b hab
  rw [HomologicalComplex₂.ιTotal_map]
  simp

private def totalShortComplex (S : ShortComplex (HomologicalComplex₂ (ModuleCat.{u} R) up up)) :
    ShortComplex (CochainComplex (ModuleCat.{u} R) ℕ) :=
  ShortComplex.mk (HomologicalComplex₂.total.map S.f up)
    (HomologicalComplex₂.total.map S.g up) (total_map_zero S.zero)

private theorem component_exact (S : ShortComplex (HomologicalComplex₂ (ModuleCat.{u} R) up up)) (hS : S.ShortExact) (a b : ℕ) :
    ((S.map (HomologicalComplex.eval _ _ a)).map (HomologicalComplex.eval _ _ b)).ShortExact :=
  (HomologicalComplex.shortExact_iff_degreewise_shortExact _).mp
    ((HomologicalComplex.shortExact_iff_degreewise_shortExact S).mp hS a) b

set_option backward.isDefEq.respectTransparency false in
private theorem totalShortExact (S : ShortComplex (HomologicalComplex₂ (ModuleCat.{u} R) up up)) (hS : S.ShortExact) :
    (totalShortComplex S).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · classical
    apply (ShortComplex.moduleCat_exact_iff _).mpr
    intro x hx
    change (HomologicalComplex₂.total.map S.g up).f n x = 0 at hx
    have he (t : totalIndex n) :
        ∃ y : (S.X₁.X t.1.1).X t.1.2, (S.f.f t.1.1).f t.1.2 y = componentAt S.X₂ n t x := by
      apply (ShortComplex.moduleCat_exact_iff _).mp (component_exact S hS t.1.1 t.1.2).exact
      have hm := ConcreteCategory.congr_hom (total_map_component S.g n t) x
      change componentAt S.X₃ n t ((HomologicalComplex₂.total.map S.g up).f n x) =
        (S.g.f t.1.1).f t.1.2 (componentAt S.X₂ n t x) at hm
      rw [hx, map_zero] at hm
      exact hm.symm
    choose y hy using he
    refine ⟨∑ t : totalIndex n, insertAt S.X₁ n t (y t), ?_⟩
    change (HomologicalComplex₂.total.map S.f up).f n _ = x
    apply sub_eq_zero.mp
    apply totalComponent_ext_zero S.X₂
    intro a b hab
    let t : totalIndex n := ⟨(a, b), hab⟩
    rw [map_sub]
    have hm := ConcreteCategory.congr_hom (total_map_component S.f n t)
      (∑ s : totalIndex n, insertAt S.X₁ n s (y s))
    change componentAt S.X₂ n t ((HomologicalComplex₂.total.map S.f up).f n
        (∑ s : totalIndex n, insertAt S.X₁ n s (y s))) =
      (S.f.f a).f b (componentAt S.X₁ n t (∑ s : totalIndex n, insertAt S.X₁ n s (y s))) at hm
    rw [hm, component_sum_insert, hy t, sub_self]
  · exact (ModuleCat.mono_iff_injective _).mpr (total_map_injective S.f n
      (fun a b => (ModuleCat.mono_iff_injective _).mp (component_exact S hS a b).mono_f))
  · exact (ModuleCat.epi_iff_surjective _).mpr (total_map_surjective S.g n
      (fun a b => (ModuleCat.epi_iff_surjective _).mp (component_exact S hS a b).epi_g))

/-- 列ごとの全射擬同型は総複体でも擬同型。 -/
theorem bicomplexTotal_quasiIso_of_columns (hf : ∀ a, QuasiIso (f.f a))
    (hs : ∀ a b, Function.Surjective ((f.f a).f b)) :
    QuasiIso (HomologicalComplex₂.total.map f up) := by
  let S : ShortComplex (HomologicalComplex₂ (ModuleCat.{u} R) up up) :=
    ShortComplex.mk (kernel.ι f) f (kernel.condition f)
  let : Abelian (HomologicalComplex₂ (ModuleCat.{u} R) up up) :=
    inferInstanceAs (Abelian (CochainComplex (CochainComplex (ModuleCat.{u} R) ℕ) ℕ))
  let : S.HasHomology := ShortComplex.HasHomology.mk' (ShortComplex.HomologyData.ofAbelian S)
  let : Epi f := HomologicalComplex.epi_of_epi_f f (fun a =>
    HomologicalComplex.epi_of_epi_f _ (fun b => (ModuleCat.epi_iff_surjective _).mpr (hs a b)))
  have hS : S.ShortExact := { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel f) }
  have hc (a : ℕ) : (S.X₁.X a).Acyclic :=
    ((HomologicalComplex.shortExact_iff_degreewise_shortExact S).mp hS a).acyclic_X₁ (hf a)
  have hacyclic (i : ℕ) : IsZero ((S.X₁.total up).homology i) := by
    let I := (HomologicalComplex.homologyFunctor _ _ i).mapIso (S.X₁.totalFlipIso up)
    apply IsZero.of_iso _ I.symm
    apply HomologicalComplex.ExactAt.isZero_homology
    apply bicomplexTotal_exactAt_of_rows
    exact fun a b => hc b a
  constructor
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  let hT := totalShortExact S hS
  have hm := (hT.homology_exact₂ i).mono_g_iff.mpr ((hacyclic i).eq_zero_of_src _)
  have he := (hT.homology_exact₃ i (i + 1) rfl).epi_f_iff.mpr
    ((hacyclic (i + 1)).eq_zero_of_tgt _)
  let : Mono (HomologicalComplex.homologyMap (HomologicalComplex₂.total.map f up) i) := hm
  let : Epi (HomologicalComplex.homologyMap (HomologicalComplex₂.total.map f up) i) := he
  exact isIso_of_mono_of_epi _

end SerrePositivity.HomologicalAlgebra
