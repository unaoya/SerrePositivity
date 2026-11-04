module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Localization
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModuleComplete.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import SerrePositivity.CommutativeAlgebra.Adic.Principal
public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.Algebra.Module.LinearMap.End
public import SerrePositivity.CommutativeAlgebra.PowerTorsion.Basic

/-! # 導来完備加群の閉性と古典的な完備性との比較

## 概要

局所化の telescope から得る列作用の全単射性で、古典的な主イデアル進完備性と導来完備性を比べる（`AdicComparison`）。導来完備加群が直積・核・余核・拡大・線形写像の加群で閉じること、一様なイデアル冪ねじれなら完備であること、`a` で割れる加群から完備加群への写像が零であること、完備化のパラメータが Jacobson 根基に入ること、有界な冪ねじれの下で導来完備性と古典的な完備性が一致することを与える。

## 方針

漸化式の一意な解を各元で取り、解の一意性から線形性や閉性を示す。古典的な完備性・正則性・Noether 性は仮定しない。

## 規約

旧 `AdicComparison`・`ModuleClosure`・`ModuleHomComplete`・`Torsion`・`DivisibleHomZero`・`Jacobson`・`BoundedTorsionComparison`。

## 使われ方

DerivedCompletion の全体、BhattScholze、CLMST。
-/

@[expose] public noncomputable section

universe u

section AdicComparisonPart

namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Abelian
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R]

/-- 自由telescopeのExt⁰を、基底上の値の列へ同定する。 -/
def telescopeExtZeroEquiv (M : ModuleCat.{u} R) :
    Ext (ModuleCat.of R (LocalizationTelescopeFree R)) M 0 ≃ (ℕ → M) :=
  Ext.homEquiv₀.trans (ModuleCat.homEquiv.trans
    (localizationTelescopeHomEquiv R M).toEquiv)

/-- Ext⁰の差分写像は、列の差分作用に対応する。 -/
theorem telescopeExtZeroEquiv_precomp (f : R) (M : ModuleCat.{u} R)
    (e : Ext (ModuleCat.of R (LocalizationTelescopeFree R)) M 0) :
    telescopeExtZeroEquiv R M
      ((Ext.mk₀ (ModuleCat.ofHom (localizationTelescopeMap R f))).precomp M (add_zero 0) e) =
        adicRecurrenceMap f (telescopeExtZeroEquiv R M e) := by
  obtain ⟨g, rfl⟩ := Ext.mk₀_bijective _ _ |>.surjective e
  change telescopeExtZeroEquiv R M
    ((Ext.mk₀ (ModuleCat.ofHom (localizationTelescopeMap R f))).comp (Ext.mk₀ g) (zero_add 0)) = _
  rw [Ext.mk₀_comp_mk₀]
  have he {X Y : ModuleCat.{u} R} (h : X ⟶ Y) : Ext.homEquiv₀ (Ext.mk₀ h) = h :=
    Ext.homEquiv₀.apply_symm_apply h
  change localizationTelescopeHomEquiv R M
    (Ext.homEquiv₀ (Ext.mk₀ (ModuleCat.ofHom (localizationTelescopeMap R f) ≫ g))).hom =
      adicRecurrenceMap f (localizationTelescopeHomEquiv R M (Ext.homEquiv₀ (Ext.mk₀ g)).hom)
  rw [he, he]
  exact localizationTelescopeHomEquiv_comp R f M g.hom

/-- Ext¹の消滅は、列の差分作用の全射性と同値。 -/
theorem localization_ext_one_iff_recurrence_surjective (f : R) (M : ModuleCat.{u} R) :
    Subsingleton (Ext (ModuleCat.of R (Localization.Away f)) M 1) ↔
      Function.Surjective (adicRecurrenceMap f : (ℕ → M) →ₗ[R] (ℕ → M)) := by
  rw [localization_ext_one_subsingleton_iff]
  change Function.Surjective ((Ext.mk₀ (ModuleCat.ofHom
    (localizationTelescopeMap R f))).precomp M (add_zero 0)) ↔ _
  let e := telescopeExtZeroEquiv R M
  constructor
  · intro h y
    obtain ⟨x, hx⟩ := h (e.symm y)
    refine ⟨e x, ?_⟩
    change adicRecurrenceMap f (telescopeExtZeroEquiv R M x) = y
    rw [← telescopeExtZeroEquiv_precomp R f M]
    change e (((Ext.mk₀ (ModuleCat.ofHom
      (localizationTelescopeMap R f))).precomp M (add_zero 0)) x) = y
    rw [hx]
    exact e.apply_symm_apply y
  · intro h y
    obtain ⟨x, hx⟩ := h (e y)
    refine ⟨e.symm x, e.injective ?_⟩
    dsimp only [e]
    rw [telescopeExtZeroEquiv_precomp R f M]
    change adicRecurrenceMap f (e (e.symm x)) = e y
    simpa only [Equiv.apply_symm_apply] using hx

/-- Ext⁰の消滅は、自由分解の双対の単射性と同値。 -/
theorem localization_ext_zero_iff_precomp_injective (f : R) (M : ModuleCat.{u} R) :
    Subsingleton (Ext (ModuleCat.of R (Localization.Away f)) M 0) ↔
      Function.Injective ((Ext.mk₀ (ModuleCat.ofHom (localizationTelescopeMap R f))).precomp M
        (add_zero 0)) := by
  let S := localizationPresentation R f
  have hS : S.ShortExact := localizationPresentation_shortExact R f
  change Subsingleton (Ext S.X₃ M 0) ↔
    Function.Injective ((Ext.mk₀ S.f).precomp M (add_zero 0))
  rw [injective_iff_map_eq_zero]
  constructor
  · intro h x hx
    obtain ⟨z, hz⟩ := Ext.contravariant_sequence_exact₂ hS M x hx
    rw [← hz, Subsingleton.elim z 0]
    simp
  · intro h
    apply subsingleton_of_forall_eq 0
    intro z
    let := hS.epi_g
    apply Ext.precomp_mk₀_injective_of_epi M S.g
    change (Ext.mk₀ S.g).comp z (zero_add 0) = _
    rw [map_zero]
    apply h
    change (Ext.mk₀ S.f).comp ((Ext.mk₀ S.g).comp z (zero_add 0)) (zero_add 0) = 0
    rw [Ext.mk₀_comp_mk₀_assoc, S.zero]
    simp

/-- Ext⁰の消滅は、列の差分作用の単射性と同値。 -/
theorem localization_ext_zero_iff_recurrence_injective (f : R) (M : ModuleCat.{u} R) :
    Subsingleton (Ext (ModuleCat.of R (Localization.Away f)) M 0) ↔
      Function.Injective (adicRecurrenceMap f : (ℕ → M) →ₗ[R] (ℕ → M)) := by
  rw [localization_ext_zero_iff_precomp_injective]
  let e := telescopeExtZeroEquiv R M
  constructor
  · intro h x y hxy
    apply e.symm.injective
    apply h
    apply e.injective
    dsimp only [e]
    rw [telescopeExtZeroEquiv_precomp, telescopeExtZeroEquiv_precomp]
    simpa only [Equiv.apply_symm_apply] using hxy
  · intro h x y hxy
    apply e.injective
    apply h
    rw [← telescopeExtZeroEquiv_precomp R f M, ← telescopeExtZeroEquiv_precomp R f M, hxy]

/-- 零次数に置いた二つの加群の負次数の導来射は零。 -/
theorem module_shiftedHom_eq_zero_of_neg (X Y : ModuleCat.{u} R) (n : ℤ) (hn : n < 0)
    (a : ShiftedHom ((moduleObjectFunctor R).obj X) ((moduleObjectFunctor R).obj Y) n) :
    a = 0 := by
  change ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj X ⟶
    ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj Y)⟦n⟧) at a
  apply DerivedCategory.TStructure.t.zero_of_isLE_of_isGE a 0 (-n) (by omega)
  · infer_instance
  · exact DerivedCategory.TStructure.t.isGE_shift _ 0 n (-n) (by omega)

/-- 導来主元完備性は、局所化からのExt⁰とExt¹の消滅だけで判定できる。 -/
theorem isModuleComplete_iff_ext_zero_one (f : R) (M : ModuleCat.{u} R) :
    IsModuleComplete R f M ↔
      Subsingleton (Ext (ModuleCat.of R (Localization.Away f)) M 0) ∧
        Subsingleton (Ext (ModuleCat.of R (Localization.Away f)) M 1) := by
  constructor
  · intro h
    have hz (n : ℕ) (e : Ext (ModuleCat.of R (Localization.Away f)) M n) : e = 0 := by
      apply Ext.homEquiv.injective
      have h' := h n e.hom
      dsimp only [localizationObject, moduleObjectFunctor] at h'
      change e.hom = (0 : Ext (ModuleCat.of R (Localization.Away f)) M n).hom
      rw [Ext.zero_hom]
      exact h'
    exact ⟨subsingleton_of_forall_eq 0 (hz 0), subsingleton_of_forall_eq 0 (hz 1)⟩
  · rintro ⟨h0, h1⟩ n a
    dsimp only [localizationObject, moduleObjectFunctor] at a ⊢
    by_cases hn : 0 ≤ n
    · lift n to ℕ using hn
      change ShiftedHom
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
          (ModuleCat.of R (Localization.Away f)))
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M) (n : ℤ) at a
      obtain ⟨e, rfl⟩ := Ext.homEquiv.surjective a
      have he : e = 0 := by
        cases n with
        | zero => exact h0.elim _ _
        | succ n =>
          cases n with
          | zero => exact h1.elim _ _
          | succ k => exact localization_ext_eq_zero R f M k e
      change e.hom = 0
      rw [he, Ext.zero_hom]
    · exact module_shiftedHom_eq_zero_of_neg R _ M n (by omega) a

/-- 導来主元完備性は、列の差分作用の全単射性と同値。 -/
theorem isModuleComplete_iff_recurrence_bijective (f : R) (M : ModuleCat.{u} R) :
    IsModuleComplete R f M ↔
      Function.Bijective (adicRecurrenceMap f : (ℕ → M) →ₗ[R] (ℕ → M)) := by
  rw [isModuleComplete_iff_ext_zero_one, localization_ext_zero_iff_recurrence_injective,
    localization_ext_one_iff_recurrence_surjective]
  rfl

/-- 古典的主元進完備な加群は導来完備。正則性は不要。 -/
theorem isModuleComplete_of_isAdicComplete (f : R) (M : ModuleCat.{u} R)
    [IsAdicComplete (Ideal.span {f}) M] : IsModuleComplete R f M :=
  (isModuleComplete_iff_recurrence_bijective R f M).mpr (adicRecurrenceMap_bijective f)

/-- fが単射に作用する加群では、導来完備性と古典的f進完備性が同値。 -/
theorem isModuleComplete_iff_isAdicComplete_of_regular (f : R) (M : ModuleCat.{u} R)
    (hreg : Function.Injective (fun x : M ↦ f • x)) :
    IsModuleComplete R f M ↔ IsAdicComplete (Ideal.span {f}) M := by
  rw [isModuleComplete_iff_recurrence_bijective,
    isAdicComplete_iff_adicRecurrenceMap_bijective_of_regular f hreg]

/-- pが零因子でない環での、導来p完備性と古典的p進完備性の比較。
素数性は必要ない。 -/
theorem isRingModuleComplete_iff_isAdicComplete_natCast (p : ℕ)
    (hp : Function.Injective (fun x : R ↦ (p : R) * x)) :
    IsModuleComplete R (p : R) (ModuleCat.of R R) ↔
      IsAdicComplete (Ideal.span {(p : R)}) R :=
  isModuleComplete_iff_isAdicComplete_of_regular R (p : R) (ModuleCat.of R R) hp

end SerrePositivity.DerivedCompletion

end AdicComparisonPart

section BoundedTorsionComparisonPart

namespace SerrePositivity.DerivedCompletion
open CategoryTheory
variable (R : Type u) [CommRing R]

/-- 有界f冪ねじれを持つ導来完備加群は古典的f進完備。 -/
theorem isAdicComplete_of_isModuleComplete_of_bounded_torsion (f : R)
    (M : ModuleCat.{u} R)
    (hM : IsModuleComplete R f M)
    (hbounded : ∃ N : ℕ, ∀ n : ℕ, ∀ x : M, f ^ n • x = 0 → f ^ N • x = 0) :
    IsAdicComplete (Ideal.span {f}) M := by
  have h := (isModuleComplete_iff_recurrence_bijective R f M).mp hM
  let := isHausdorff_of_adicRecurrenceMap_injective_of_bounded_torsion f hbounded h.1
  let := isPrecomplete_of_adicRecurrenceMap_surjective f h.2
  exact ⟨⟩

/-- 有界ねじれの下では、古典的完備性と実導来圏での完備性が同値。 -/
theorem isModuleComplete_iff_isAdicComplete_of_bounded_torsion (f : R)
    (M : ModuleCat.{u} R)
    (hbounded : ∃ N : ℕ, ∀ n : ℕ, ∀ x : M, f ^ n • x = 0 → f ^ N • x = 0) :
    IsModuleComplete R f M ↔ IsAdicComplete (Ideal.span {f}) M := by
  constructor
  · exact fun h ↦ isAdicComplete_of_isModuleComplete_of_bounded_torsion R f M h hbounded
  · intro h
    let := h
    exact isModuleComplete_of_isAdicComplete R f M

/-- 自然数pの像についての環版。素数性やp正則性は不要。 -/
theorem isRingModuleComplete_iff_isAdicComplete_natCast_of_bounded_torsion (p : ℕ)
    (hbounded : ∃ N : ℕ, ∀ n : ℕ, ∀ x : R,
      (p : R) ^ n * x = 0 → (p : R) ^ N * x = 0) :
    IsModuleComplete R (p : R) (ModuleCat.of R R) ↔
      IsAdicComplete (Ideal.span {(p : R)}) R :=
  isModuleComplete_iff_isAdicComplete_of_bounded_torsion R (p : R)
    (ModuleCat.of R R) hbounded

end SerrePositivity.DerivedCompletion

end BoundedTorsionComparisonPart

section DivisibleHomZeroPart

namespace SerrePositivity.DerivedCompletion
open CategoryTheory
variable {R : Type u} [CommRing R] (a : R)

/-- The recurrence injectivity criterion forbids nonzero maps from an a-divisible
module. No separation or bounded torsion hypothesis is imposed. -/
lemma linearMap_eq_zero_of_smul_surjective_of_isModuleComplete
    (M N : ModuleCat.{u} R) (hM : Function.Surjective (fun x : M => a • x))
    (hN : IsModuleComplete R a N) (f : M →ₗ[R] N) : f = 0 := by
  classical
  apply LinearMap.ext
  intro m
  let x : ℕ → M := fun n => Nat.rec m (fun _ z => Classical.choose (hM z)) n
  have hx : ∀ n, a • x (n + 1) = x n := fun n => Classical.choose_spec (hM (x n))
  have hr : adicRecurrenceMap a (fun n => f (x n)) = 0 := by
    funext n
    change f (x n) - a • f (x (n + 1)) = 0
    rw [← map_smul, hx, sub_self]
  have hn := (isModuleComplete_iff_recurrence_bijective R a N).mp hN
  have hz : (fun n => f (x n)) = 0 := hn.injective (hr.trans (map_zero _).symm)
  exact congrFun hz 0

end SerrePositivity.DerivedCompletion

end DivisibleHomZeroPart

section ModuleClosurePart

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

end ModuleClosurePart

section JacobsonPart

namespace SerrePositivity.DerivedCompletion
variable (R : Type u) [CommRing R] (a : R)

/-- A bijective recurrence makes every `1 - a * y` invertible. -/
theorem isUnit_one_sub_mul_of_recurrence_bijective
    (h : Function.Bijective (adicRecurrenceMap a : (ℕ → R) →ₗ[R] (ℕ → R)))
    (y : R) : IsUnit (1 - a * y) := by
  obtain ⟨b, hb⟩ := h.surjective (fun n ↦ y ^ n)
  have hshift : adicRecurrenceMap a (fun n ↦ b (n + 1)) =
      adicRecurrenceMap a (y • b) := by
    rw [map_smul, hb]
    funext n
    have hn := congrFun hb (n + 1)
    simpa only [adicRecurrenceMap, LinearMap.coe_mk, AddHom.coe_mk,
      Pi.smul_apply, smul_eq_mul, pow_succ, mul_comm] using hn
  have hrec := congrFun (h.injective hshift) 0
  have hzero := congrFun hb 0
  change b 1 = y * b 0 at hrec
  change b 0 - a * b 1 = y ^ 0 at hzero
  rw [hrec, pow_zero] at hzero
  apply isUnit_iff_exists_inv.mpr
  refine ⟨b 0, ?_⟩
  convert hzero using 1; ring

/-- A derived complete ring has its completion parameter in the Jacobson radical. -/
theorem mem_jacobson_bot_of_isModuleComplete
    (h : IsModuleComplete R a (ModuleCat.of R R)) :
    a ∈ Ideal.jacobson (⊥ : Ideal R) := by
  apply Ideal.mem_jacobson_bot.mpr
  intro y
  have hb := (isModuleComplete_iff_recurrence_bijective R a (ModuleCat.of R R)).mp h
  simpa [add_comm] using isUnit_one_sub_mul_of_recurrence_bijective R a hb (-y)

/-- The standard unit criterion for a parameter of a derived complete ring. -/
theorem isUnit_one_sub_mul_of_isModuleComplete
    (h : IsModuleComplete R a (ModuleCat.of R R)) (y : R) :
    IsUnit (1 - a * y) :=
  isUnit_one_sub_mul_of_recurrence_bijective R a
    ((isModuleComplete_iff_recurrence_bijective R a (ModuleCat.of R R)).mp h) y

end SerrePositivity.DerivedCompletion

end JacobsonPart

section ModuleHomCompletePart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory
variable (R : Type u) [CommRing R]

/-- 導来完備加群を値に持つ線形写像の加群も導来完備。 -/
theorem isModuleComplete_linearMap (f : R) (M N : ModuleCat.{u} R)
    (hN : IsModuleComplete R f N) :
    IsModuleComplete R f (ModuleCat.of R (M →ₗ[R] N)) := by
  have hn := (isModuleComplete_iff_recurrence_bijective R f N).mp hN
  apply (isModuleComplete_iff_recurrence_bijective R f _).mpr
  constructor
  · intro x y hxy
    have he (m : M) : (fun n ↦ x n m) = (fun n ↦ y n m) := hn.injective
      (congrArg (fun z n ↦ z n m) hxy)
    funext n
    apply LinearMap.ext
    intro m
    exact congrFun (he m) n
  · intro y
    choose x hx using fun m : M ↦ hn.surjective (fun n ↦ y n m)
    have hadd (a b : M) : x (a + b) = x a + x b := by
      apply hn.injective
      rw [map_add, hx, hx, hx]
      funext n
      exact (y n).map_add a b
    have hsmul (r : R) (a : M) : x (r • a) = r • x a := by
      apply hn.injective
      rw [map_smul, hx, hx]
      funext n
      exact (y n).map_smul r a
    let z : ℕ → M →ₗ[R] N := fun n ↦
      { toFun := fun a ↦ x a n
        map_add' := fun a b ↦ congrFun (hadd a b) n
        map_smul' := fun r a ↦ congrFun (hsmul r a) n }
    refine ⟨z, ?_⟩
    funext n
    apply LinearMap.ext
    intro m
    exact congrFun (hx m) n

end SerrePositivity.DerivedCompletion

end ModuleHomCompletePart

section TorsionPart

namespace SerrePositivity.DerivedCompletion
open CategoryTheory

variable (R : Type u) [CommRing R]

/-- J の一つの冪で加群が消えれば、J の元 f の冪も消去するため導来 f 完備。 -/
theorem isModuleComplete_of_isPowTorsion (J : Ideal R) (f : R) (hf : f ∈ J)
    (M : ModuleCat.{u} R) (hM : IsPowTorsion J M) : IsModuleComplete R f M := by
  obtain ⟨N, hN⟩ := hM
  apply isModuleComplete_of_pow_smul_zero R f M N
  intro m
  exact hN (a := ⟨f ^ N, Ideal.pow_mem_pow hf N⟩) (x := m)

end SerrePositivity.DerivedCompletion

end TorsionPart
