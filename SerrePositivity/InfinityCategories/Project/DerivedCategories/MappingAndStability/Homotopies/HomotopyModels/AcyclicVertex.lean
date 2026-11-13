module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.HomSpaces.HomotopyCategoryComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.Resolutions.SemifreeKProjective

/-! # D(S) の頂点の零性と非輪状性

概要：D(S) の頂点はその全ホモロジーが零であるとき、かつそのときに限り h D(S) で零対象である。
方針：semifree 複体の K 射影性で恒等射を零ホモトピックにし、充満忠実比較で反映する。
規約：導来圏の宇宙の選択を要しない。使われ方：局所化底変更の核の同定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded
open scoped _root_.Simplicial ZeroObject
variable (S : Type u) [CommRing S]

/-- 概要：零複体を D(S) の頂点として取る。
方針：semifree 性の証明を添えて定値頂点を作る。
規約：D(S) の既存の零複体。使われ方：零対象への同型の終域。 -/
def derivedInfinityZeroVertex : (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory S) _⦋0⦌ :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (⟨0, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexSemifree_zero S⟩ : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S)

/-- 概要：D(S) の零複体の頂点はホモトピー圏で零対象である。
方針：充満忠実な複体ホモトピー比較で零性を反映する。
規約：HasDerivedCategory の選択に依存しない。使われ方：零対象への同型。 -/
lemma derivedInfinityZeroVertex_isZero :
    IsZero (⟨derivedInfinityZeroVertex S⟩ : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomotopyCategory S) := by
  let F := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityH0Equivalence S).functor ⋙ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeHomotopyComparison S
  apply IsZero.of_full_of_faithful_of_isZero F
  exact (HomotopyCategory.quotient _ _).map_isZero (isZero_zero (_root_.SerrePositivity.DifferentialGraded.Complex S))

/-- 概要：D(S) の頂点の零性は全次数の複体ホモロジーの零性と同値である。
方針：前向きは零複体への同型、逆向きは K 射影性による恒等射の零ホモトピーを使う。
規約：一般の非有界 semifree 複体。使われ方：D_Z を底変更の核として読む。 -/
theorem derivedInfinityVertex_isZero_iff_homology
    (x : (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory S) _⦋0⦌) :
    IsZero (⟨x⟩ : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomotopyCategory S) ↔
      ∀ i : ℤ, IsZero ((x.obj 0).val.homology i) := by
  let F := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityH0Equivalence S).functor ⋙ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeHomotopyComparison S
  have hz : IsZero (F.obj ⟨derivedInfinityZeroVertex S⟩) :=
    (HomotopyCategory.quotient _ _).map_isZero (isZero_zero (_root_.SerrePositivity.DifferentialGraded.Complex S))
  constructor
  · intro hx i
    have hFX : IsZero (F.obj ⟨x⟩) :=
      hz.of_iso (F.mapIso (hx.iso (derivedInfinityZeroVertex_isZero S)))
    have hH := (HomotopyCategory.homologyFunctor (ModuleCat S) (.up ℤ) i).map_isZero hFX
    exact hH.of_iso ((HomotopyCategory.homologyFunctorFactors _ _ i).app (x.obj 0).val).symm
  · intro hx
    let P := (x.obj 0).val
    have : P.IsKProjective := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexSemifree_isKProjective S (x.obj 0).property
    have hP : P.Acyclic := fun i => (HomologicalComplex.exactAt_iff_isZero_homology P i).2 (hx i)
    have h := HomotopyCategory.eq_of_homotopy _ _
      (CochainComplex.IsKProjective.homotopyZero (𝟙 P) hP)
    have hQ : IsZero ((HomotopyCategory.quotient _ _).obj P) := by
      apply (IsZero.iff_id_eq_zero _).2
      exact ((HomotopyCategory.quotient _ _).map_id P).symm.trans
        (h.trans ((HomotopyCategory.quotient _ _).map_zero P P))
    exact IsZero.of_full_of_faithful_of_isZero F ⟨x⟩ hQ

end SerrePositivity.InfinityCategories.Project.DerivedCategories
