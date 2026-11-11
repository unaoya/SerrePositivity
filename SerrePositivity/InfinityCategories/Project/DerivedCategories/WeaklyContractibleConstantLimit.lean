module
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.CofinalLimitTransfer
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.QuillenALeft
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.SliceIdentityTerminal
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.StdSimplexTerminal
/-!
概要：弱可縮な実添字上の定値図式に、同じ指定頂点を持つ実極限錐を与える。
方針：一点への写像の left cofinality を Quillen A で確認し、恒等錐を制限する。
規約：添字の Kan 性・quasicategory 性を仮定しない。使われ方：反転された実分母図式の極限。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits SSet
open scoped _root_.Simplicial
/-- 弱可縮な添字から一点への実写像は left cofinal。 -/
lemma weaklyContractible_toPoint_isLeftCofinal (K : SSet.{u}) (hK : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeaklyContractible K) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsLeftCofinal (SSet.const (X := K) (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 1))) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isLeftCofinal_of_weaklyContractible_slices
  intro b
  have hb : b = SSet.stdSimplex.obj₀Equiv.symm (Fin.last 0) := by
    apply SSet.stdSimplex.obj₀Equiv.injective
    apply Fin.ext
    omega
  subst b
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection
      (SSet.yonedaEquiv.symm (SSet.stdSimplex.obj₀Equiv.symm (Fin.last 0)))) :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.isTerminalVertex_iff_trivialKanFibration _).mp (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.stdSimplex_last_isTerminalVertex 0)
  let u := SSet.const (X := K) (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 1))
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (pullback.fst u (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection
      (SSet.yonedaEquiv.symm (SSet.stdSimplex.obj₀Equiv.symm (Fin.last 0))))) :=
    ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibrations.pullback_fst _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p :=
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm
        (SSet.stdSimplex.obj₀Equiv.symm (Fin.last 0)))) )⟩
  have hw := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isLeftCofinal_of_trivialKanFibration
    (pullback.fst u (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm
      (SSet.stdSimplex.obj₀Equiv.symm (Fin.last 0)))))).isWeakHomotopyEquivalence
  exact hw.weaklyContractible_iff.mpr hK
/-- 定値図式の、同じ指定頂点を持つ実定値錐。 -/
def constantDiagramCone (K X : SSet.{u}) (x : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (SSet.const (X := K) x) :=
  ⟨SSet.const x, SSet.comp_const _ _⟩
/-- 実定値錐の頂点は元の指定頂点。 -/
lemma constantDiagramCone_vertex (K X : SSet.{u}) (x : X _⦋0⦌) :
    (constantDiagramCone K X x).vertex = x := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone.vertex_eq]
  change SSet.yonedaEquiv (_ ≫ SSet.const x) = x
  rw [SSet.comp_const, SSet.yonedaEquiv_const]
/-- 弱可縮な実添字上の同じ定値錐は、任意 quasicategory 標的で実極限錐。 -/
lemma constantDiagramCone_isLimit (K X : SSet.{u}) [Quasicategory X]
    (hK : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeaklyContractible K) (x : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (constantDiagramCone K X x) := by
  have h₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (constantDiagramCone (Δ[0] : SSet.{u}) X x) := by
    have h : ∀ c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (SSet.yonedaEquiv.symm x),
        c.val = SSet.const x → _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c := by
      intro c hc
      have he : c = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceIdentityCone x := Subtype.ext hc
      subst c
      exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.sliceIdentityCone_isTerminalVertex x
    rw [SSet.yonedaEquiv_symm_zero] at h
    exact h (constantDiagramCone _ X x) rfl
  have h := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isLimitCone_iff_restrict_of_leftCofinal
    (SSet.const (X := K) (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 1)))
    (weaklyContractible_toPoint_isLeftCofinal K hK) _
    (constantDiagramCone (Δ[0] : SSet.{u}) X x)).mp h₀
  exact h
end SerrePositivity.InfinityCategories.Project.DerivedCategories
