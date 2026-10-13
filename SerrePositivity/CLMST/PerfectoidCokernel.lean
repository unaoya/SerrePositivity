module

public import SerrePositivity.CLMST.PerfectoidIsogeny
public import SerrePositivity.CommutativeAlgebra.AlgebraMapCokernel
public import SerrePositivity.HomologicalAlgebra.KoszulScalarControl
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact

/-! # perfectoid 化の余核の代数作用と Koszul ホモロジーの制御

標準写像の余核を元の代数 S 上の加群とし、基底 R 上の isogeny の零化冪を移す。
同じ冪で、任意の列・全次数の余核を係数とする Koszul ホモロジーも零化する。
長さ零や Euler 一致を、この冪による零化だけからは結論しない。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.CLMST
open CategoryTheory
attribute [local instance] HasDerivedCategory.standard
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [Module.Finite R S] [Algebra.FinitePresentation R S]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p)

/-- perfectoid 化の標準写像の、元の代数 S 上の余核。 -/
abbrev PerfectoidizationCokernel := AlgebraMapCokernel S (Perfectoidization R S p hR)

/-- 原典の isogeny で制御した R 加群の余核との比較。 -/
def perfectoidizationCokernelRestrictEquiv :
    ((Perfectoidization R S p hR) ⧸ (perfectoidizationModuleMap R S p hR).range) ≃ₗ[R]
      PerfectoidizationCokernel R S p hR :=
  algebraMapCokernelRestrictEquiv R S (Perfectoidization R S p hR)

/-- 原典の余核の零化を、S 加群としての余核へ移す。同じ冪を保持する。 -/
theorem perfectoidizationCokernel_annihilated (g : R) (N : ℕ)
    (h : ∀ x : (Perfectoidization R S p hR) ⧸ (perfectoidizationModuleMap R S p hR).range,
      g ^ N • x = 0) :
    ∀ x : PerfectoidizationCokernel R S p hR, (algebraMap R S g) ^ N • x = 0 := by
  simpa only [map_pow] using algebraMapCokernel_annihilated_algebraMap_of_restrict
    R S (Perfectoidization R S p hR) (g ^ N) h

/-- 任意の S の列と全次数に、余核と同じ消去冪を供給する。 -/
theorem perfectoidizationCokernel_koszul_annihilated (g : R) (N : ℕ)
    (h : ∀ x : (Perfectoidization R S p hR) ⧸ (perfectoidizationModuleMap R S p hR).range,
      g ^ N • x = 0) {e : ℕ} (z : Fin e → S) (q : ℤ) :
    ∀ x : ((koszulModuleFunctor z).obj
      (ModuleCat.of S (PerfectoidizationCokernel R S p hR))).homology q,
      (algebraMap R S g) ^ N • x = 0 :=
  koszulModuleHomology_annihilated z (ModuleCat.of S (PerfectoidizationCokernel R S p hR))
    ((algebraMap R S g) ^ N) (perfectoidizationCokernel_annihilated R S p hR g N h) q

/-- S の任意の部分係数環に制限しても、同じ冪で Koszul ホモロジーを消せる。 -/
theorem perfectoidizationCokernel_restricted_koszul_annihilated
    {T : Type u} [CommRing T] (φ : T →+* S)
    (g : R) (a : T) (ha : φ a = algebraMap R S g) (N : ℕ)
    (h : ∀ x : (Perfectoidization R S p hR) ⧸ (perfectoidizationModuleMap R S p hR).range,
      g ^ N • x = 0) {e : ℕ} (z : Fin e → T) (q : ℤ) :
    ∀ x : ((koszulModuleFunctor z).obj ((ModuleCat.restrictScalars φ).obj
      (ModuleCat.of S (PerfectoidizationCokernel R S p hR)))).homology q,
      a ^ N • x = 0 := by
  apply koszulModuleHomology_annihilated_restrictScalars φ
    (ModuleCat.of S (PerfectoidizationCokernel R S p hR)) z (a ^ N) ?_ q
  simpa only [map_pow, ha] using perfectoidizationCokernel_annihilated R S p hR g N h

/-- 単射性から、標準写像とS加群の余核の実際の短完全列が得られる。 -/
theorem perfectoidizationCokernel_shortExact
    (hinj : Function.Injective (perfectoidizationModuleMap R S p hR)) :
    (algebraMapCokernelShortComplex S (Perfectoidization R S p hR)).ShortExact :=
  algebraMapCokernelShortComplex_shortExact S (Perfectoidization R S p hR) hinj

/-- 部分係数環への制限とKoszul構成の後も、同じ余核による短完全列が得られる。 -/
theorem perfectoidizationCokernel_restricted_koszul_shortExact
    {T : Type u} [CommRing T] (φ : T →+* S) {e : ℕ} (z : Fin e → T)
    (hinj : Function.Injective (perfectoidizationModuleMap R S p hR)) :
    ((algebraMapCokernelShortComplex S (Perfectoidization R S p hR)).map
      (ModuleCat.restrictScalars φ ⋙ koszulModuleFunctor z)).ShortExact := by
  rw [ShortComplex.map_comp]
  exact koszulModuleFunctor_shortExact z _
    ((perfectoidizationCokernel_shortExact R S p hR hinj).map_of_exact
      (ModuleCat.restrictScalars φ))

end SerrePositivity.CLMST
