module
public import SerrePositivity.InfinityCategories.Derived.ModulePiZeroMoore
/-!
概要：零基点の全 π による正規化 Moore 射の準同型判定。
方針：実辺・正規化の包含・標準ホモロジー射の可換式を使う。
規約：元の正規化射を保持する。使われ方：β5(g) の弱同値の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory AlgebraicTopology Opposite HomologicalComplex
open KST.Spectra
open scoped Simplicial
variable {S : Type u} [CommRing S]
variable {W V : SimplicialObject (ModuleCat.{v} S)}
lemma moduleNormalizedMap_quasiIso_iff_zeroBasepointPi
    [SSet.KanComplex (moduleUnderlyingSSet W)] [SSet.KanComplex (moduleUnderlyingSSet V)]
    (f : W ⟶ V) :
    QuasiIso ((normalizedMooreComplex (ModuleCat.{v} S)).map f) ↔
      Function.Bijective (SSet.mapπ₀ (moduleUnderlyingSSetMap f)) ∧
        ∀ n : ℕ, Function.Bijective
          (KanHomotopyGroup.map (n := n) (moduleUnderlyingSSetMap f)
            (moduleUnderlyingSSetMap_zero f)) := by
  rw [quasiIso_iff]
  simp only [quasiIsoAt_iff_isIso_homologyMap, ConcreteCategory.isIso_iff_bijective]
  constructor
  · intro h
    exact ⟨(modulePiZeroMap_bijective_iff_homologyMap f).mpr (h 0),
      fun n ↦ (modulePiMap_bijective_iff_homologyMap f n).mpr (h (n + 1))⟩
  · rintro ⟨h₀, hπ⟩ n
    cases n with
    | zero => exact (modulePiZeroMap_bijective_iff_homologyMap f).mp h₀
    | succ n => exact (modulePiMap_bijective_iff_homologyMap f n).mp (hπ n)
end SerrePositivity.InfinityCategories
