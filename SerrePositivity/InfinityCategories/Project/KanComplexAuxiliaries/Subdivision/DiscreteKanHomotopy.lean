module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.HomotopyIndexing

/-!
概要：定値単体集合の正次数の Kan ホモトピー類は自明である。
方針：境界定数の正次数単体は、一つの面の式だけで定数単体と一致する。
規約：Kan 性はホモトピー類を定義するためだけに使い、モデル構造を要求しない。
使われ方：Sp-7 の離散成分への収縮から、正次数の亜群化ホモトピーを判定する。
-/

@[expose] public section
universe u
open CategoryTheory SSet
open scoped _root_.Simplicial
namespace SerrePositivity.KST.Spectra
end SerrePositivity.KST.Spectra
namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries
open _root_.SerrePositivity.KST.Spectra

/-- 概要：定値単体集合の正次数の境界定数単体は、同じ定数単体に一致する。
方針：境界定数の正次数単体は、一つの面の式だけで定数単体と一致する。
規約：Kan 性はホモトピー類を定義するためだけに使い、モデル構造を要求しない。
使われ方：Sp-7 の離散成分への収縮から、正次数の亜群化ホモトピーを判定する。 -/
lemma constant_ptSimplex_eq (T : Type u) (n : ℕ)
    (x : ((Functor.const SimplexCategoryᵒᵖ).obj T : SSet.{u}) _⦋0⦌)
    (s : SSet.PtSimplex ((Functor.const SimplexCategoryᵒᵖ).obj T) (n + 1) x) :
    s = RelativeMorphism.const := by
  apply RelativeMorphism.ext
  apply SSet.yonedaEquiv.injective
  have hh := congrArg SSet.yonedaEquiv (s.δ_map (0 : Fin (n + 2)))
  rw [stdSimplex.yonedaEquiv_δ_comp] at hh
  exact hh

/-- 概要：定値 Kan 複体の全正次数のホモトピー類は一意。
方針：境界定数の正次数単体は、一つの面の式だけで定数単体と一致する。
規約：Kan 性はホモトピー類を定義するためだけに使い、モデル構造を要求しない。
使われ方：Sp-7 の離散成分への収縮から、正次数の亜群化ホモトピーを判定する。 -/
lemma constant_kanHomotopy_subsingleton (T : Type u)
    [KanComplex ((Functor.const SimplexCategoryᵒᵖ).obj T : SSet.{u})]
    (n : ℕ) (hn : 0 < n)
    (x : ((Functor.const SimplexCategoryᵒᵖ).obj T : SSet.{u}) _⦋0⦌) :
    Subsingleton (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy ((Functor.const SimplexCategoryᵒᵖ).obj T) n x) := by
  cases n with
  | zero => omega
  | succ n =>
    change Subsingleton (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup _ n x)
    constructor
    intro a b
    induction a using Quotient.inductionOn with | h a => ?_
    induction b using Quotient.inductionOn with | h b => ?_
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk a = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk b
    rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.constant_ptSimplex_eq T n x a, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.constant_ptSimplex_eq T n x b]

end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.constant_kanHomotopy_subsingleton := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.constant_kanHomotopy_subsingleton

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.constant_ptSimplex_eq := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.constant_ptSimplex_eq
