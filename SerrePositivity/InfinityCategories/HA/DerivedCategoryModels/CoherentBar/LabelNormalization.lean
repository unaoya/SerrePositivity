module
public import Mathlib.AlgebraicTopology.DoldKan.HomotopyEquivalence
public import Mathlib.AlgebraicTopology.DoldKan.Degeneracies
public import Mathlib.Algebra.Category.ModuleCat.Adjunctions
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.AlgebraicTopology.SimplicialSet.Degenerate
/-!
概要：元の単体ラベルの自由加群に Mathlib の正規化を直接適用する。
方針：I と自由加群関手を合成し、PInfty と既存の正規化 Moore ホモトピー同値を使う。
規約：ラベル複体の結果を、高次 prefix 微分を持つ実 bar の結果と同一視しない。
使われ方：bar の退化除去に用いる有限ラベル係数と、正規化ホモトピーの照合。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
open CategoryTheory Limits AlgebraicTopology AlgebraicTopology.DoldKan
open scoped _root_.Simplicial DoldKan
variable (R : Type u) [CommRing R] (I : SSet.{u})

abbrev dgCoherentBarLabelModule : SimplicialObject (ModuleCat.{u} R) :=
  I ⋙ ModuleCat.free R

abbrev dgCoherentBarLabelComplex : ChainComplex (ModuleCat.{u} R) ℕ :=
  AlternatingFaceMapComplex.obj (dgCoherentBarLabelModule R I)

def dgCoherentBarLabelProjection :
    dgCoherentBarLabelComplex R I ⟶ dgCoherentBarLabelComplex R I := PInfty

def dgCoherentBarLabelProjectionHomotopy :
    Homotopy (dgCoherentBarLabelProjection R I) (𝟙 _) :=
  homotopyPInftyToId (dgCoherentBarLabelModule R I)

def dgCoherentBarLabelNormalizedEquiv :
    HomotopyEquiv ((normalizedMooreComplex (ModuleCat.{u} R)).obj
      (dgCoherentBarLabelModule R I)) (dgCoherentBarLabelComplex R I) :=
  homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex

lemma dgCoherentBarLabelProjection_degenerate {n : ℕ} (s : I _⦋n⦌)
    (i : Fin (n + 1)) :
    (dgCoherentBarLabelProjection R I).f (n + 1)
      (ModuleCat.freeMk (R := R) (I.σ i s)) = 0 := by
  have h := σ_comp_PInfty (dgCoherentBarLabelModule R I) i
  have hh := ConcreteCategory.congr_hom h (ModuleCat.freeMk (R := R) s)
  change (PInfty (X := dgCoherentBarLabelModule R I)).f (n + 1)
    ((ModuleCat.free R).map (I.σ i) (ModuleCat.freeMk (R := R) s)) = 0 at hh
  simpa only [dgCoherentBarLabelProjection, ModuleCat.free_map_apply] using hh

lemma dgCoherentBarLabelProjection_eq_zero_of_degenerate {n : ℕ} (s : I _⦋n⦌)
    (hs : s ∈ I.degenerate n) :
    (dgCoherentBarLabelProjection R I).f n (ModuleCat.freeMk (R := R) s) = 0 := by
  cases n with
  | zero => simp only [I.degenerate_zero, Set.mem_empty_iff_false] at hs
  | succ n =>
    rw [I.degenerate_eq_iUnion_range_σ] at hs
    obtain ⟨i, t, rfl⟩ := Set.mem_iUnion.mp hs
    exact dgCoherentBarLabelProjection_degenerate R I t i

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
