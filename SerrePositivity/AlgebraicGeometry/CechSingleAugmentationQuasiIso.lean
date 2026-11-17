module

public import Mathlib.Algebra.Homology.Single
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
概要：実際の single からの増大射の完全性を、同じ射の準同型性へ渡す。
方針：零次は cycles への元の写像、正次数は既存の完全性の判定を使う。
規約：基底環と加群の宇宙は独立、層の導来関手の H との比較は作らない。
使われ方：同じタプル複体への大域切断の増大の各列の比較。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u v
variable {R : Type v} [CommRing R] (A : ModuleCat.{u} R)
variable (C : CochainComplex (ModuleCat.{u} R) ℕ)
variable (f : (HomologicalComplex.single (ModuleCat.{u} R) (.up ℕ) 0).obj A ⟶ C)

set_option backward.isDefEq.respectTransparency false in
/-- 同じ増大射の単射性と零次完全性は、その射の零次の準同型性を与える。 -/
theorem cechSingleAugmentation_quasiIsoAt_zero
    (hinj : Function.Injective (f.f 0).hom)
    (hexact : Function.Exact (f.f 0).hom (C.d 0 1).hom) : QuasiIsoAt f 0 := by
  let K := (HomologicalComplex.single (ModuleCat.{u} R) (.up ℕ) 0).obj A
  let S := K.sc' 0 0 1
  let T := C.sc' 0 0 1
  let φ : S ⟶ T :=
    (HomologicalComplex.shortComplexFunctor' (ModuleCat.{u} R) (.up ℕ) 0 0 1).map f
  have hSf : S.f = 0 := K.shape 0 0 (by simp)
  have hSg : S.g = 0 :=
    (HomologicalComplex.isZero_single_obj_X (.up ℕ) 0 A 1 (by decide)).eq_of_tgt _ _
  have hTf : T.f = 0 := C.shape 0 0 (by simp)
  rw [CochainComplex.quasiIsoAt₀_iff]
  change ShortComplex.QuasiIso φ
  rw [ShortComplex.quasiIso_iff_isIso_liftCycles φ hSf hSg hTf]
  let l := T.liftCycles φ.τ₂ (by rw [φ.comm₂₃, hSg, Limits.zero_comp])
  have hv (x : S.X₂) : T.iCycles.hom (l.hom x) = (f.f 0).hom x := by
    change T.iCycles.hom ((T.liftCycles φ.τ₂ _).hom x) = φ.τ₂.hom x
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using
      congrArg (fun k ↦ k.hom x) (T.liftCycles_i φ.τ₂ (by
        rw [φ.comm₂₃, hSg, Limits.zero_comp]))
  change IsIso l
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  constructor
  · intro x y hxy
    apply hinj
    have h := congrArg T.iCycles.hom hxy
    rw [hv, hv] at h
    exact h
  · intro y
    have hy : (C.d 0 1).hom (T.iCycles.hom y) = 0 := by
      change T.g.hom (T.iCycles.hom y) = 0
      simpa only [ModuleCat.hom_comp, LinearMap.comp_apply,
        ModuleCat.hom_zero, LinearMap.zero_apply] using
        congrArg (fun k ↦ k.hom y) T.iCycles_g
    obtain ⟨x, hx⟩ := (hexact (T.iCycles.hom y)).mp hy
    refine ⟨x, ?_⟩
    apply (ModuleCat.mono_iff_injective T.iCycles).mp inferInstance
    exact (hv x).trans hx

/-- 同じ増大射の零次完全性と目標の正次数完全性は、全次数の準同型性を与える。 -/
theorem cechSingleAugmentation_quasiIsoAt
    (hinj : Function.Injective (f.f 0).hom)
    (hexact : Function.Exact (f.f 0).hom (C.d 0 1).hom)
    (hpos : ∀ n, C.ExactAt (n + 1)) (q : ℕ) : QuasiIsoAt f q := by
  cases q with
  | zero => exact cechSingleAugmentation_quasiIsoAt_zero A C f hinj hexact
  | succ n =>
    apply (quasiIsoAt_iff_exactAt f (n + 1) ?_).mpr (hpos n)
    exact HomologicalComplex.ExactAt.of_isZero
      (HomologicalComplex.isZero_single_obj_X (.up ℕ) 0 A (n + 1) (by omega))

end SerrePositivity.AlgebraicGeometry
