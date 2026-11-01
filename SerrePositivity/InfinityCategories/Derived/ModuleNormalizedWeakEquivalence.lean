module
public import SerrePositivity.InfinityCategories.Derived.ModuleTranslationPi
public import SerrePositivity.InfinityCategories.Derived.ModuleNormalizedPiCriterion
public import SerrePositivity.InfinityCategories.Kan.HomotopyComponents
public import SerrePositivity.InfinityCategories.F1B.Homotopy.WeakWhitehead
public import SerrePositivity.InfinityCategories.HomotopyLimits.KanWhiteheadComparison
/-!
概要：実正規化射の準同型性と台単体集合の弱同値の同値。
方針：元の射と全基点の誘導写像を保ち、既存の実 Whitehead 逆へ接続する。
規約：可換性・平坦性を仮定しない。使われ方：β5(g) の正規化界面。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory AlgebraicTopology Opposite
open KST.Spectra
open scoped Simplicial
variable {S : Type u} [CommRing S]
variable {W V : SimplicialObject (ModuleCat.{v} S)}
lemma moduleNormalizedMap_quasiIso_iff_kanPiIsomorphism
    [SSet.KanComplex (moduleUnderlyingSSet W)] [SSet.KanComplex (moduleUnderlyingSSet V)]
    (f : W ⟶ V) :
    QuasiIso ((normalizedMooreComplex (ModuleCat.{v} S)).map f) ↔
      KanPiIsomorphism (moduleUnderlyingSSetMap f) := by
  rw [moduleNormalizedMap_quasiIso_iff_zeroBasepointPi]
  constructor
  · rintro ⟨h₀, hπ⟩ x n
    cases n with
    | zero => exact (KanHomotopyZero.map_bijective_iff_piZero
        (moduleUnderlyingSSetMap f) (x := x) rfl).mpr h₀
    | succ n => exact (modulePiMap_bijective_at_iff_zero f x n).mpr (hπ n)
  · intro h
    have hz (n : ℕ) := KanHomotopy.map_bijective_congr n (moduleUnderlyingSSetMap f)
      rfl (moduleUnderlyingSSetMap_zero f) rfl (moduleUnderlyingSSetMap_zero f) (h 0 n)
    exact ⟨(KanHomotopyZero.map_bijective_iff_piZero (moduleUnderlyingSSetMap f)
      (x := (0 : W.obj (op ⦋0⦌))) (moduleUnderlyingSSetMap_zero f)).mp (hz 0),
      fun n ↦ hz (n + 1)⟩
lemma kanPiIsomorphism_iff_isWeakHomotopyEquivalence_of_vertex
    {X Y : SSet.{v}} [SSet.KanComplex X] [SSet.KanComplex Y] (f : X ⟶ Y)
    (x : X _⦋0⦌) : KanPiIsomorphism f ↔ IsWeakHomotopyEquivalence f :=
  ⟨fun h ↦ IsSimplicialHomotopyEquivalence.isWeakHomotopyEquivalence
      (HomotopyLimits.homotopyEquivalence_of_kanPiIsomorphism_of_vertex f h x),
    fun h ↦ HomotopyLimits.kanPiIsomorphism_of_homotopyEquivalence f
      h.isSimplicialHomotopyEquivalence⟩
lemma moduleNormalizedMap_quasiIso_iff_isWeakHomotopyEquivalence
    [SSet.KanComplex (moduleUnderlyingSSet W)] [SSet.KanComplex (moduleUnderlyingSSet V)]
    (f : W ⟶ V) :
    QuasiIso ((normalizedMooreComplex (ModuleCat.{v} S)).map f) ↔
      IsWeakHomotopyEquivalence (moduleUnderlyingSSetMap f) :=
  (moduleNormalizedMap_quasiIso_iff_kanPiIsomorphism f).trans
    (kanPiIsomorphism_iff_isWeakHomotopyEquivalence_of_vertex (moduleUnderlyingSSetMap f)
      (0 : W.obj (op ⦋0⦌)))
end SerrePositivity.InfinityCategories
