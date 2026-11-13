module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraInvariantValues

/-!
概要：実非可換 dg 代数上で、局所化不変量の k-connective 条件を具体的に定義する。
方針：源では H⁻ʲ の実作用、値では元の Perf extension の BF 整数 π の作用を用いる。
規約：underlying spectrum 関手や Perf の厳密化は入力しない。
使われ方：LT Def. 2.5 の dg 増強流での整数係数条件と準同型不変性。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories SerrePositivity.DifferentialGraded
open SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra

variable (R : Type u) [CommRing R] (Φ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u + 1} ⟶ Sp.{u + 1})

def IsKConnective (k : ℤ) : Prop :=
  IsLocalizingInvariant Φ ∧ ∀ {B C : Mon (Complex R)},
    IsConnective R B → IsConnective R C → ∀ (f : B ⟶ C) (n : ℤ), 1 ≤ n →
      Function.Bijective ((groups R 0).map f).hom → IsConnected R f n →
        (∀ j : ℤ, j < n + k → Function.Injective (invariantGroupMap R Φ f j)) ∧
          ∀ j : ℤ, j ≤ n + k → Function.Surjective (invariantGroupMap R Φ f j)

lemma IsKConnective.quasiIso_bijective {k : ℤ} (h : IsKConnective R Φ k)
    {B C : Mon (Complex R)} (hB : IsConnective R B) (hC : IsConnective R C)
    (f : B ⟶ C) (hf : QuasiIso f.hom) (j : ℤ) :
    Function.Bijective (invariantGroupMap R Φ f j) := by
  let n : ℤ := max 1 (j - k + 1)
  have hn : 1 ≤ n := le_max_left _ _
  have hj : j < n + k := by dsimp [n]; omega
  haveI := groups_map_isIso_of_quasiIso R f hf 0
  have hz := ConcreteCategory.bijective_of_isIso ((groups R 0).map f)
  have hc := h.2 hB hC f n hn hz (connected_of_quasiIso R f hf n)
  exact ⟨hc.1 j hj, hc.2 j hj.le⟩

lemma IsKConnective.quasiIso_value_isInvertible {k : ℤ} (h : IsKConnective R Φ k)
    {B C : Mon (Complex R)} (hB : IsConnective R B) (hC : IsConnective R C)
    (f : B ⟶ C) (hf : QuasiIso f.hom) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (perfectMap R f)).map Φ).toTruncated :=
  value_isInvertible_of_piIsomorphism Φ (perfectMap R f)
    (fun j ↦ h.quasiIso_bijective R Φ hB hC f hf j)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite LT "Def 2.5" (partial := component) "仮定：可換基礎環上の dg 代数または U・Perf の指定模型と整数係数（Lean が強い）。結論：π₀ 同型で n≥1 の連結射について Φ の連結度が n+k になるという定義。一般 E₁ 環スペクトル・Λ 係数は対象外（Lean が弱い）。"] _root_.SerrePositivity.KST.LocalizingInvariants.DGAlgebra.IsKConnective
