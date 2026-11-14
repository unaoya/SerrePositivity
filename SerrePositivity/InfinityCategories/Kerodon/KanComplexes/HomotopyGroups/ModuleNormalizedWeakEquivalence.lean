module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.HomotopyModels.ModuleTranslationPi
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.HomotopyModels.ModuleNormalizedPiCriterion
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.HomotopyComponents
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.WeakWhitehead
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanWhiteheadComparison
/-!
概要：実正規化射の準同型性と台単体集合の弱同値の同値。
方針：元の射と全基点の誘導写像を保ち、既存の実 Whitehead 逆へ接続する。
規約：可換性・平坦性を仮定しない。使われ方：β5(g) の正規化界面。

対応節は Kerodon 3.2（Tag 00V2）。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups
open CategoryTheory AlgebraicTopology Opposite
open KST.Spectra
open scoped _root_.Simplicial
variable {S : Type u} [CommRing S]
variable {W V : SimplicialObject (ModuleCat.{v} S)}
lemma moduleNormalizedMap_quasiIso_iff_kanPiIsomorphism
    [SSet.KanComplex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet W)] [SSet.KanComplex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet V)]
    (f : W ⟶ V) :
    QuasiIso ((normalizedMooreComplex (ModuleCat.{v} S)).map f) ↔
      _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSetMap f) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleNormalizedMap_quasiIso_iff_zeroBasepointPi]
  constructor
  · rintro ⟨h₀, hπ⟩ x n
    cases n with
    | zero => exact (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanHomotopyZero.map_bijective_iff_piZero
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSetMap f) (x := x) rfl).mpr h₀
    | succ n => exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.modulePiMap_bijective_at_iff_zero f x n).mpr (hπ n)
  · intro h
    have hz (n : ℕ) := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map_bijective_congr n (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSetMap f)
      rfl (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSetMap_zero f) rfl (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSetMap_zero f) (h 0 n)
    exact ⟨(_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanHomotopyZero.map_bijective_iff_piZero (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSetMap f)
      (x := (0 : W.obj (op ⦋0⦌))) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSetMap_zero f)).mp (hz 0),
      fun n ↦ hz (n + 1)⟩
lemma kanPiIsomorphism_iff_isWeakHomotopyEquivalence_of_vertex
    {X Y : SSet.{v}} [SSet.KanComplex X] [SSet.KanComplex Y] (f : X ⟶ Y)
    (x : X _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism f ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence f :=
  ⟨fun h ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence.isWeakHomotopyEquivalence
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.homotopyEquivalence_of_kanPiIsomorphism_of_vertex f h x),
    fun h ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.kanPiIsomorphism_of_homotopyEquivalence f
      h.isSimplicialHomotopyEquivalence⟩
lemma moduleNormalizedMap_quasiIso_iff_isWeakHomotopyEquivalence
    [SSet.KanComplex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet W)] [SSet.KanComplex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet V)]
    (f : W ⟶ V) :
    QuasiIso ((normalizedMooreComplex (ModuleCat.{v} S)).map f) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSetMap f) :=
  (moduleNormalizedMap_quasiIso_iff_kanPiIsomorphism f).trans
    (kanPiIsomorphism_iff_isWeakHomotopyEquivalence_of_vertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSetMap f)
      (0 : W.obj (op ⦋0⦌)))
end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups
