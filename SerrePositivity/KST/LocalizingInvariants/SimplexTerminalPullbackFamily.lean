module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.SimplexTerminalPullbackFamily

public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SimplexTerminalArrowFamily
public import SerrePositivity.KST.LocalizingInvariants.PullbackDiagramFamilies
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ColumnPushout
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Bicartesian
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CospanFamilies

/-!
概要：有限線型図式の終端を指定辺に沿って引き戻し、終端の四角形を厳密に固定する。
方針：同じ終端辺族を cospan 族へ貼り、最後の頂点上の列四角形を保って相対延長する。
規約：終端での同型だけではなく、列四角形そのものを保持する。
使われ方：c5 の有限図式の持ち上げで、次の辺との共有端点を保つ精密化。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

variable {X : SSet.{u}} {n : ℕ} (D : (Δ[n] : SSet.{u}) ⟶ X)
  (s : (Δ[1] : SSet.{u}) ⟶ X)
  (hs : s.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
    D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n)))

/-- 同じ指定辺を横に並べた列四角形の実 pullback 頂点。 -/
def terminalPullbackColumnVertex [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] :
    (pullbackDiagrams X) _⦋0⦌ :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareColumnDiagram s), by
    intro α
    have hα : α = 𝟙 ⦋0⦌ := Subsingleton.elim _ _
    rw [hα, op_id, CategoryTheory.Functor.map_id_apply]
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).symm
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareColumnDiagram s)))
    rw [Equiv.symm_apply_apply]
    exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable.pullback_of_pushout_square _ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareColumnDiagram_isPushout s)⟩

/-- 終端の列四角形を固定して、元の cospan 族の全普遍補完を構成する。
終端での一致は全四角形の実単体の等号であり、同型への置き換えをしない。 -/
lemma exists_simplexTerminalPullbackFamily [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] :
    ∃ F : (Δ[n] : SSet.{u}) ⟶ pullbackDiagrams X,
      F ≫ pullbackProjection X = _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.simplexTerminalCospanFamily D s hs ∧
        F.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n)) =
          terminalPullbackColumnVertex s := by
  let j : (Δ[0] : SSet.{u}) ⟶ Δ[n] :=
    SSet.const (stdSimplex.obj₀Equiv.symm (Fin.last n))
  have : Mono j := by
    rw [NatTrans.mono_iff_mono_app]
    intro m
    rw [mono_iff_injective]
    intro a b _
    apply stdSimplex.ext
    intro k
    omega
  let a : (Δ[0] : SSet.{u}) ⟶ pullbackDiagrams X :=
    SSet.const (terminalPullbackColumnVertex s)
  have ha : a ≫ pullbackProjection X = j ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.simplexTerminalCospanFamily D s hs := by
    rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.simplexTerminalCospanFamily_last]
    rw [SSet.const_comp]
    rfl
  obtain ⟨F, hFa, hFd⟩ := exists_relative_stable_pullbackFamily j
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.simplexTerminalCospanFamily D s hs) a ha
  refine ⟨F, hFd, ?_⟩
  have he := ConcreteCategory.congr_hom (NatTrans.congr_app hFa (Opposite.op ⦋0⦌))
    (stdSimplex.obj₀Equiv.symm (0 : Fin 1))
  change F.app (Opposite.op ⦋0⦌)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm (Fin.last n)) 0) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (terminalPullbackColumnVertex s) 0 at he
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero] using he

end SerrePositivity.KST.LocalizingInvariants
