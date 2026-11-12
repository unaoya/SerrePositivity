module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import Mathlib.AlgebraicTopology.SimplicialSet.Coskeletal
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FromTopologicalSpacesToSimplicialSets.HomotopyZeroRelations

/-!
概要：StrictSegal な Kan 複体の二以上の次数のホモトピー消滅。
方針：境界定数単体の全ての spine 辺が定数なので、StrictSegal の単射性を使う。
規約：次数 n は Spectra.KanHomotopy の実際の次数。
使われ方：Sp-8 (2)、群 nerve の高次ホモトピー消滅。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped _root_.Simplicial
namespace SerrePositivity.KST.LocalizingInvariants.CoreFlag
end SerrePositivity.KST.LocalizingInvariants.CoreFlag
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.CoreFlag
open _root_.SerrePositivity.KST.LocalizingInvariants
open _root_.SerrePositivity.KST.LocalizingInvariants.CoreFlag
open _root_.SerrePositivity.KST.Spectra

/-- StrictSegal な単体集合の二以上の境界定数単体は定数単体そのもの。 -/
lemma strictSegal_ptSimplex_eq_const (X : SSet.{u}) [X.IsStrictSegal]
    (n : ℕ) (hn : 1 < n) (x : X _⦋0⦌) (s : X.PtSimplex n x) :
    s = RelativeMorphism.const := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  apply RelativeMorphism.ext
  apply SSet.yonedaEquiv.injective
  apply (SSet.StrictSegal.ofIsStrictSegal X).spineInjective
  apply SSet.Path.ext'
  intro i
  have : (Δ[1] : SSet.{u}).HasDimensionLT (k + 2) :=
    SSet.hasDimensionLT_of_le (X := (Δ[1] : SSet.{u})) 2 (k + 2) (by omega)
  have h := s.comp_map_eq_const (stdSimplex.map (SimplexCategory.mkOfSucc i))
  change X.map (SimplexCategory.mkOfSucc i).op (SSet.yonedaEquiv s.map) =
    X.map (SimplexCategory.mkOfSucc i).op (SSet.yonedaEquiv (SSet.const x))
  rw [yonedaEquiv_naturality, yonedaEquiv_naturality, h, SSet.comp_const]

/-- StrictSegal な Kan 複体の二以上の実次数のホモトピー類は一意。 -/
lemma strictSegal_kanHomotopy_subsingleton (X : SSet.{u}) [KanComplex X]
    [X.IsStrictSegal] (n : ℕ) (hn : 1 < n) (x : X _⦋0⦌) :
    Subsingleton (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy X n x) := by
  constructor
  intro a b
  obtain ⟨s, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FromTopologicalSpacesToSimplicialSets.KanHomotopy.mk_surjective n a
  obtain ⟨t, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FromTopologicalSpacesToSimplicialSets.KanHomotopy.mk_surjective n b
  rw [_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.CoreFlag.strictSegal_ptSimplex_eq_const X n hn x s,
    _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.CoreFlag.strictSegal_ptSimplex_eq_const X n hn x t]

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.CoreFlag

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CoreFlag.strictSegal_kanHomotopy_subsingleton := _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.CoreFlag.strictSegal_kanHomotopy_subsingleton

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CoreFlag.strictSegal_ptSimplex_eq_const := _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.CoreFlag.strictSegal_ptSimplex_eq_const
