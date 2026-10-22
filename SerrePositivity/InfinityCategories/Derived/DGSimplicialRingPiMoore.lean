module
public import SerrePositivity.InfinityCategories.Derived.DGSimplicialRingDGAlgebraFunctor
public import SerrePositivity.InfinityCategories.Derived.ModulePiMooreNaturality
public import SerrePositivity.KST.Comparison.SimplicialRingKan
/-!
概要：単体環の台 Kan 複体の正次数 π と同じ正規化 Moore ホモロジー。
方針：実環ホーン充填と一般の単体的加群の群同型を同じ台集合に適用する。
規約：単体環の可換性を仮定しない。使われ方：β5(g) の弱同値の比較。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory AlgebraicTopology
open KST.Comparison KST.Spectra
open scoped Simplicial
instance simplicialRingIntegerModuleUnderlyingKan (A : SimplicialObject RingCat.{u}) :
    SSet.KanComplex (moduleUnderlyingSSet (simplicialRingIntegerModule A)) := by
  change SSet.KanComplex (ringSpace A)
  infer_instance
def simplicialRingPiMooreGroupEquiv (A : SimplicialObject RingCat.{u}) (n : ℕ) :
    KanHomotopyGroup (ringSpace A) n (0 : A.obj (Opposite.op ⦋0⦌)) ≃*
      Multiplicative ((simplicialRingNormalizedChains A).homology (n + 1)) :=
  modulePiMooreGroupEquiv (simplicialRingIntegerModule A) n
end SerrePositivity.InfinityCategories
