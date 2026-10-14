module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.AdicComparison

/-! # 導来完備加群の直積・核・余核・拡大

局所化のtelescopeから得た列作用の全単射性を使う。
古典的完備性・正則性・Noether性は仮定しない。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory
variable (R : Type u) [CommRing R]

/-- 導来完備加群の直積も導来完備。 -/
theorem isModuleComplete_pi (f : R) {ι : Type} (M : ι → ModuleCat.{u} R)
    (hM : ∀ i, IsModuleComplete R f (M i)) :
    IsModuleComplete R f (ModuleCat.of R (∀ i, M i)) := by
  have h := fun i ↦ (isModuleComplete_iff_recurrence_bijective R f (M i)).mp (hM i)
  apply (isModuleComplete_iff_recurrence_bijective R f _).mpr
  constructor
  · intro x y hxy
    funext n i
    have he : (fun n ↦ x n i) = (fun n ↦ y n i) := (h i).injective
      (by exact congrArg (fun z n ↦ z n i) hxy)
    exact congrFun he n
  · intro y
    have hy : ∀ i, ∃ x : ℕ → M i, adicRecurrenceMap f x = fun n ↦ y n i :=
      fun i ↦ (h i).surjective _
    choose x hx using hy
    refine ⟨fun n i ↦ x i n, ?_⟩
    funext n i
    exact congrFun (hx i) n

/-- 導来完備加群間の線形写像の核は導来完備。 -/
theorem isModuleComplete_ker (f : R) {M N : ModuleCat.{u} R} (g : M →ₗ[R] N)
    (hM : IsModuleComplete R f M) (hN : IsModuleComplete R f N) :
    IsModuleComplete R f (ModuleCat.of R g.ker) := by
  have hm := (isModuleComplete_iff_recurrence_bijective R f M).mp hM
  have hn := (isModuleComplete_iff_recurrence_bijective R f N).mp hN
  apply (isModuleComplete_iff_recurrence_bijective R f _).mpr
  constructor
  · intro x y hxy
    have he : (fun n ↦ (x n).val) = (fun n ↦ (y n).val) := hm.injective
      (congrArg (fun z n ↦ (z n).val) hxy)
    funext n
    exact Subtype.ext (congrFun he n)
  · intro y
    obtain ⟨x, hx⟩ := hm.surjective (fun n ↦ (y n).val)
    have hg : adicRecurrenceMap f (fun n ↦ g (x n)) = 0 := by
      funext n
      change g (x n) - f • g (x (n + 1)) = 0
      rw [← map_smul, ← map_sub]
      exact (congrArg g (congrFun hx n)).trans (y n).property
    have hxker : ∀ n, x n ∈ g.ker := by
      have he := hn.injective (hg.trans (map_zero _).symm)
      exact fun n ↦ congrFun he n
    refine ⟨fun n ↦ ⟨x n, hxker n⟩, ?_⟩
    funext n
    exact Subtype.ext (congrFun hx n)

/-- 導来完備加群間の線形写像の余核は導来完備。 -/
theorem isModuleComplete_coker (f : R) {M N : ModuleCat.{u} R} (g : M →ₗ[R] N)
    (hM : IsModuleComplete R f M) (hN : IsModuleComplete R f N) :
    IsModuleComplete R f (ModuleCat.of R (N ⧸ g.range)) := by
  have hm := (isModuleComplete_iff_recurrence_bijective R f M).mp hM
  have hn := (isModuleComplete_iff_recurrence_bijective R f N).mp hN
  let q := g.range.mkQ
  apply (isModuleComplete_iff_recurrence_bijective R f _).mpr
  constructor
  · apply (injective_iff_map_eq_zero _).mpr
    intro x hx
    choose z hz using fun n ↦ g.range.mkQ_surjective (x n)
    have hrange : ∀ n, z n - f • z (n + 1) ∈ g.range := by
      intro n
      apply (Submodule.Quotient.mk_eq_zero _).mp
      change q (z n - f • z (n + 1)) = 0
      rw [map_sub, map_smul, hz, hz]
      exact congrFun hx n
    choose w hw using hrange
    obtain ⟨v, hv⟩ := hm.surjective w
    have hrec : adicRecurrenceMap f (fun n ↦ z n - g (v n)) = 0 := by
      funext n
      change (z n - g (v n)) - f • (z (n + 1) - g (v (n + 1))) = 0
      rw [smul_sub]
      have he : g (v n) - f • g (v (n + 1)) = z n - f • z (n + 1) := by
        rw [← map_smul, ← map_sub, show v n - f • v (n + 1) = w n from congrFun hv n]
        exact hw n
      rw [show z n - g (v n) - (f • z (n + 1) - f • g (v (n + 1))) =
        (z n - f • z (n + 1)) - (g (v n) - f • g (v (n + 1))) by abel, he, sub_self]
    have hzg : ∀ n, z n = g (v n) := by
      have he := hn.injective (hrec.trans (map_zero _).symm)
      exact fun n ↦ sub_eq_zero.mp (congrFun he n)
    funext n
    rw [← hz n, hzg n]
    exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨v n, rfl⟩
  · intro y
    choose z hz using fun n ↦ g.range.mkQ_surjective (y n)
    obtain ⟨x, hx⟩ := hn.surjective z
    refine ⟨fun n ↦ q (x n), ?_⟩
    funext n
    change q (x n) - f • q (x (n + 1)) = y n
    rw [← map_smul, ← map_sub, show x n - f • x (n + 1) = z n from congrFun hx n]
    exact hz n

/-- 導来完備加群の拡大は導来完備。 -/
theorem isModuleComplete_extension (f : R) (S : ShortComplex (ModuleCat.{u} R))
    (hS : S.ShortExact) (h1 : IsModuleComplete R f S.X₁) (h3 : IsModuleComplete R f S.X₃) :
    IsModuleComplete R f S.X₂ := by
  have hfirst := (isModuleComplete_iff_recurrence_bijective R f S.X₁).mp h1
  have hlast := (isModuleComplete_iff_recurrence_bijective R f S.X₃).mp h3
  have hinj := hS.moduleCat_injective_f
  have hsurj := hS.moduleCat_surjective_g
  have hex := (ShortComplex.moduleCat_exact_iff S).mp hS.exact
  apply (isModuleComplete_iff_recurrence_bijective R f _).mpr
  constructor
  · apply (injective_iff_map_eq_zero _).mpr
    intro x hx
    have hg : adicRecurrenceMap f (fun n ↦ S.g (x n)) = 0 := by
      funext n
      change S.g (x n) - f • S.g (x (n + 1)) = 0
      rw [← map_smul, ← map_sub, show x n - f • x (n + 1) = 0 from congrFun hx n, map_zero]
    have hxg : ∀ n, S.g (x n) = 0 := by
      have he := hlast.injective (hg.trans (map_zero _).symm)
      exact fun n ↦ congrFun he n
    choose y hy using fun n ↦ hex (x n) (hxg n)
    have hyr : adicRecurrenceMap f y = 0 := by
      funext n
      apply hinj
      change S.f (y n - f • y (n + 1)) = S.f 0
      rw [map_zero]
      rw [map_sub, map_smul, hy, hy]
      exact congrFun hx n
    have hyzero := hfirst.injective (hyr.trans (map_zero _).symm)
    funext n
    simp only [← hy n, congrFun hyzero n, Pi.zero_apply, map_zero]
  · intro y
    obtain ⟨z, hz⟩ := hlast.surjective (fun n ↦ S.g (y n))
    choose x hx using fun n ↦ hsurj (z n)
    have herr : ∀ n, S.g (y n - (x n - f • x (n + 1))) = 0 := by
      intro n
      rw [map_sub, map_sub, map_smul, hx, hx]
      change S.g (y n) - (z n - f • z (n + 1)) = 0
      rw [show z n - f • z (n + 1) = S.g (y n) from congrFun hz n, sub_self]
    choose w hw using fun n ↦ hex _ (herr n)
    obtain ⟨v, hv⟩ := hfirst.surjective w
    refine ⟨fun n ↦ x n + S.f (v n), ?_⟩
    funext n
    change x n + S.f (v n) - f • (x (n + 1) + S.f (v (n + 1))) = y n
    rw [smul_add]
    have he : S.f (v n) - f • S.f (v (n + 1)) = y n - (x n - f • x (n + 1)) := by
      rw [← map_smul, ← map_sub, show v n - f • v (n + 1) = w n from congrFun hv n]
      exact hw n
    rw [show x n + S.f (v n) - (f • x (n + 1) + f • S.f (v (n + 1))) =
      (x n - f • x (n + 1)) + (S.f (v n) - f • S.f (v (n + 1))) by abel, he]
    abel

end SerrePositivity.DerivedCompletion
