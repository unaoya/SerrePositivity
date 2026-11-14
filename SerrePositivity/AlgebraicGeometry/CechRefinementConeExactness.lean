module

public import SerrePositivity.AlgebraicGeometry.CechRefinementCone
public import Mathlib.Algebra.Exact.Basic

/-!
概要：共通増大項を保つ二つの完全な Čech 列の間の射の cone は完全。
方針：元の二つの列でサイクルの前像を順に取り、cone の前像を組み立てる。
規約：第零項の単射性も含めて、自然数で添字付けした cone の完全性を示す。
使われ方：共通アフィン細分の二重図式の正次数の行を B1 へ渡す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u
variable {R : Type u} [CommRing R]
variable (A B : CochainComplex (ModuleCat.{u} R) ℕ) (f : A ⟶ B)
variable {Z : Type u} [AddCommGroup Z] [Module R Z]
variable (a : Z →ₗ[R] A.X 0) (b : Z →ₗ[R] B.X 0)
variable (hab : (f.f 0).hom.comp a = b)
variable (hbmono : Function.Injective b)
variable (ha : Function.Exact a (A.d 0 1).hom)
variable (hb : Function.Exact b (B.d 0 1).hom)
variable (hA : ∀ n, Function.Exact (A.d n (n + 1)).hom (A.d (n + 1) (n + 2)).hom)
variable (hB : ∀ n, Function.Exact (B.d n (n + 1)).hom (B.d (n + 1) (n + 2)).hom)

include hab hbmono ha in
/-- 増大項で恒等を誘導する射の cone は、第零項で核が零。 -/
theorem cechRefinementCone_zero_kernel
    (x : cechRefinementConeTerm A B 0)
    (hx : cechRefinementConeDifferential A B f 0 x = 0) : x = 0 := by
  change ((f.f 0).hom x, -(A.d 0 1).hom x) = (0, 0) at hx
  have hx0 : (f.f 0).hom x = 0 := congrArg Prod.fst hx
  have hx1 : (A.d 0 1).hom x = 0 := neg_eq_zero.mp (congrArg Prod.snd hx)
  obtain ⟨z, hz⟩ := (ha x).mp hx1
  have hz0 : b z = 0 := by
    rw [← hab, LinearMap.comp_apply, hz, hx0]
  have hz' : z = 0 := hbmono (hz0.trans (map_zero b).symm)
  rw [← hz, hz', map_zero]

include hab ha hb hA hB in
/-- cone の正次数の各サイクルは境界。増大項を保つ二つの完全な列を用いる。 -/
theorem cechRefinementCone_cycle_boundary (n : ℕ)
    (x : cechRefinementConeTerm A B (n + 1))
    (hx : cechRefinementConeDifferential A B f (n + 1) x = 0) :
    ∃ y, cechRefinementConeDifferential A B f n y = x := by
  have hf (i : ℕ) (z : A.X i) :
      (B.d i (i + 1)).hom ((f.f i).hom z) =
        (f.f (i + 1)).hom ((A.d i (i + 1)).hom z) := by
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using
      congrArg (fun c ↦ c.hom z) (f.comm i (i + 1))
  cases n with
  | zero =>
    change ((B.d 0 1).hom x.1 + (f.f 1).hom x.2, -(A.d 1 2).hom x.2) = (0, 0) at hx
    have hxA : (A.d 1 2).hom x.2 = 0 := neg_eq_zero.mp (congrArg Prod.snd hx)
    obtain ⟨y, hy⟩ := (hA 0 x.2).mp hxA
    have hcycle : (B.d 0 1).hom (x.1 + (f.f 0).hom y) = 0 := by
      rw [map_add, hf, hy]
      exact congrArg Prod.fst hx
    obtain ⟨z, hz⟩ := (hb _).mp hcycle
    have haz : (A.d 0 1).hom (a z) = 0 := (ha _).mpr ⟨z, rfl⟩
    refine ⟨a z - y, ?_⟩
    apply Prod.ext
    · change (f.f 0).hom (a z - y) = x.1
      rw [map_sub, ← LinearMap.comp_apply, hab, hz, add_sub_cancel_right]
    · change -(A.d 0 1).hom (a z - y) = x.2
      rw [map_sub, haz, zero_sub, neg_neg, hy]
  | succ n =>
    change ((B.d (n + 1) (n + 2)).hom x.1 + (f.f (n + 2)).hom x.2,
      -(A.d (n + 2) (n + 3)).hom x.2) = (0, 0) at hx
    have hxA : (A.d (n + 2) (n + 3)).hom x.2 = 0 := neg_eq_zero.mp (congrArg Prod.snd hx)
    obtain ⟨y, hy⟩ := (hA (n + 1) x.2).mp hxA
    have hcycle : (B.d (n + 1) (n + 2)).hom (x.1 + (f.f (n + 1)).hom y) = 0 := by
      rw [map_add, hf, hy]
      exact congrArg Prod.fst hx
    obtain ⟨z, hz⟩ := (hB n _).mp hcycle
    refine ⟨(z, -y), ?_⟩
    apply Prod.ext
    · change (B.d n (n + 1)).hom z + (f.f (n + 1)).hom (-y) = x.1
      rw [map_neg, hz, add_neg_cancel_right]
    · change -(A.d (n + 1) (n + 2)).hom (-y) = x.2
      rw [map_neg, neg_neg, hy]

end SerrePositivity.AlgebraicGeometry
