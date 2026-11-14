module

public import SerrePositivity.BhattScholze.Prismatic.Site.FlatCover
public import SerrePositivity.CommutativeAlgebra.CompletelyFlat.FiniteIdealReduction
public import SerrePositivity.HomologicalAlgebra.Cech.InverseTower
import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
import all Mathlib.AlgebraicTopology.CechNerve
import Mathlib.AlgebraicTopology.CechNerve

/-!
# 完全忠実平坦な環射の有限剰余 Čech 降下

## 概要
有限剰余の増大 Čech 複体の逆極限は、完全忠実平坦な射に対して全次数で完全。

## 方針
各有限剰余で通常の忠実平坦降下を使い、全射的な遷移写像に沿って逆極限を取る。

## 規約
BS 著者版 Corollary 3.12 (c) の古典的な逆極限の模型。通常のイデアル冪を使う。

## 使われ方
完備 Čech 複体と有限剰余の逆極限との比較。
-/

public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

namespace SerrePositivity.Cech

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

private theorem surjective_mapCechConerve {F G : Arrow CommRingCat.{u}} (a : F ⟶ G)
    (hl : Function.Surjective a.left.hom) (hr : Function.Surjective a.right.hom)
    (n : SimplexCategory) : Function.Surjective ((Arrow.mapCechConerve a).app n).hom := by
  let b := (Arrow.mapCechConerve a).app n
  let S := b.hom.range
  let e : CommRingCat.of S ⟶ G.cechConerve.obj n := CommRingCat.ofHom S.subtype
  let ι₀ : G.left ⟶ G.cechConerve.obj n := WidePushout.head _
  let ι (i : Fin (n.len + 1)) : G.right ⟶ G.cechConerve.obj n :=
    WidePushout.ι (fun _ : Fin (n.len + 1) ↦ G.hom) i
  have h₀ (x : G.left) : ι₀.hom x ∈ S := by
    obtain ⟨y, rfl⟩ := hl x
    refine ⟨(WidePushout.head (fun _ : Fin (n.len + 1) ↦ F.hom)).hom y, ?_⟩
    have hh : WidePushout.head _ ≫ b = a.left ≫ ι₀ := WidePushout.head_desc _ _ _ _
    exact RingHom.congr_fun (congrArg CommRingCat.Hom.hom hh) y
  have h (i : Fin (n.len + 1)) (x : G.right) : (ι i).hom x ∈ S := by
    obtain ⟨y, rfl⟩ := hr x
    refine ⟨(WidePushout.ι (fun _ : Fin (n.len + 1) ↦ F.hom) i).hom y, ?_⟩
    have hh : WidePushout.ι _ i ≫ b = a.right ≫ ι i := WidePushout.ι_desc _ _ _ _ _
    exact RingHom.congr_fun (congrArg CommRingCat.Hom.hom hh) y
  let j₀ := CommRingCat.ofHom (ι₀.hom.codRestrict S h₀)
  let j (i : Fin (n.len + 1)) := CommRingCat.ofHom ((ι i).hom.codRestrict S (h i))
  let k : G.cechConerve.obj n ⟶ CommRingCat.of S :=
    WidePushout.desc j₀ j (fun i ↦ by
      apply CommRingCat.hom_ext
      ext x
      have hEq : G.hom ≫ ι i = ι₀ :=
        WidePushout.arrow_ι (fun _ : Fin (n.len + 1) ↦ G.hom) i
      exact RingHom.congr_fun (congrArg CommRingCat.Hom.hom hEq) x)
  have hk : k ≫ e = 𝟙 _ := by
    apply WidePushout.hom_ext
    · intro i
      rw [← Category.assoc, WidePushout.ι_desc]
      change j i ≫ e = ι i ≫ 𝟙 _
      rw [Category.comp_id]
      rfl
    · rw [← Category.assoc, WidePushout.head_desc]
      change j₀ ≫ e = ι₀ ≫ 𝟙 _
      rw [Category.comp_id]
      rfl
  intro x
  have hx : ((k.hom x : S) : G.cechConerve.obj n) = x :=
    RingHom.congr_fun (congrArg CommRingCat.Hom.hom hk) x
  obtain ⟨y, hy⟩ := (k.hom x).property
  exact ⟨y, hy.trans hx⟩

section Complete

variable {A B : Type u} [CommRing A] [CommRing B] (I : Ideal A) (f : A →+* B)

/-- 有限剰余への通常の環射を Čech 余脈体の増大として表す。 -/
def idealPowerArrow (n : ℕ) : Arrow CommRingCat.{u} :=
  Arrow.mk (CommRingCat.ofHom
    (Ideal.quotientMap ((I ^ n).map f) f
      (Ideal.map_le_iff_le_comap.mp le_rfl)))

private def idealPowerArrowTransition (n : ℕ) : idealPowerArrow I f (n + 1) ⟶ idealPowerArrow I f n := by
  let h : I ^ (n + 1) ≤ I ^ n := Ideal.pow_le_pow_right (Nat.le_succ _)
  refine Arrow.homMk (CommRingCat.ofHom (Ideal.Quotient.factor h))
    (CommRingCat.ofHom (Ideal.Quotient.factor (Ideal.map_mono h))) ?_
  apply CommRingCat.hom_ext
  apply Ideal.Quotient.ringHom_ext
  ext x
  rfl

private def intModules : AddCommGrpCat.{u} ⥤ ModuleCat.{u} ℤ where
  obj G := ModuleCat.of ℤ G
  map f := ModuleCat.ofHom f.hom.toIntLinearMap
  map_id _ := rfl
  map_comp _ _ := rfl

private instance : intModules.{u}.Additive where
  map_add := rfl

private def ringCochainAsIntModules :
    Arrow CommRingCat.{u} ⥤ CochainComplex (ModuleCat.{u} ℤ) ℕ :=
  CosimplicialObject.augmentedCechConerve ⋙ ringCochain ⋙
    intModules.mapHomologicalComplex (.up ℕ)

private abbrev stages (n : ℕ) := ringCochainAsIntModules.obj (idealPowerArrow I f n)
private abbrev transition (n : ℕ) := ringCochainAsIntModules.map (idealPowerArrowTransition I f n)

/-- イデアル冪による有限 Čech 複体の、次数ごとの逆極限。 -/
def idealPowerCompletedCech : CochainComplex (ModuleCat.{u} ℤ) ℕ :=
  degreewiseTowerLimit (R := ℤ) (stages I f) (transition I f)

/-- 概要：完全忠実平坦な環射の有限剰余から作った完備 Čech は全次数で完全。
方針：剰余で通常の忠実平坦降下を適用し、次数ごとの全射的な逆塔を使う。
規約：BS 著者版 Corollary 3.12 (c) の逆極限側。零次に増大を置く。
使われ方：prismatic site の完備 Čech 降下。 -/
theorem idealPowerCompletedCech_acyclic
    (hf : letI := f.toAlgebra; IsCompletelyFaithfullyFlat I B) :
    (idealPowerCompletedCech I f).Acyclic := by
  let := f.toAlgebra
  apply degreewiseTowerLimit_acyclic
  · intro n j
    let h : I ^ (n + 1) ≤ I ^ n := Ideal.pow_le_pow_right (Nat.le_succ _)
    let a := idealPowerArrowTransition I f n
    have hl : Function.Surjective a.left.hom := Ideal.Quotient.factor_surjective h
    have hr : Function.Surjective a.right.hom := Ideal.Quotient.factor_surjective (Ideal.map_mono h)
    cases j with
    | zero => exact hl
    | succ j => exact surjective_mapCechConerve a hl hr ⦋j⦌
  · intro n j
    let a := idealPowerArrow I f n
    have hflat := faithfullyFlat_algebraQuotient_of_idealPower_le I (I ^ n) B hf n le_rfl
    have hfaith : letI := a.hom.hom.toAlgebra; Module.FaithfullyFlat a.left a.right := by
      change @Module.FaithfullyFlat (A ⧸ I ^ n) (B ⧸ (I ^ n).map f) _ _
        a.hom.hom.toAlgebra.toModule
      have he : a.hom.hom.toAlgebra = adicQuotientAlgebra (I ^ n) B := by
        apply Algebra.algebra_ext
        intro x
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
        rfl
      rw [he]
      exact hflat
    have hcech : IsCechExact a := isCechExact_of_faithfullyFlat (Under.mk a.hom) hfaith
    have hx := (ringCechExact_iff_acyclic a.augmentedCechConerve).mp hcech
    change ((intModules.mapHomologicalComplex (.up ℕ)).obj
      (ringCochain.obj a.augmentedCechConerve)).ExactAt j
    rw [HomologicalComplex.exactAt_iff]
    apply (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr
    exact (ShortComplex.ab_exact_iff_function_exact _).mp (hx j)

end Complete

end SerrePositivity.Cech
