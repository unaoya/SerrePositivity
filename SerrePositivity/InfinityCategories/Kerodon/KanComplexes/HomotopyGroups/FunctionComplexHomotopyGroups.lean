module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FunctionComplexPointedSimplex

/-!
概要：関数複体の正次数ホモトピー群と各座標のホモトピー群の関数群の同型。
方針：各評価の準同型を束ね、関係充填と代表単体を座標ごとに選んで両方向を示す。
規約：添字集合は任意。各座標で異なる基点を許す。
使われ方：Goerss–Jardine I §7、VIII §2、Kerodon §3.2.3（Tag 00W3）。群 cochain の π_* の代数的な表示。

対応節は Kerodon 3.2（Tag 00V2）。
-/

@[expose] public section

universe u

open CategoryTheory SSet
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra.SimplicialFunctionComplex
end SerrePositivity.KST.Spectra.SimplicialFunctionComplex
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups
open _root_.SerrePositivity.KST.Spectra
open _root_.SerrePositivity.KST.Spectra.SimplicialFunctionComplex

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (S : Type u) (X : SSet.{u}) [KanComplex X] (n : ℕ) (b : S → X _⦋0⦌)

/-- 概要：各評価が関数複体のホモトピー群に誘導する準同型を束ねる。
方針：座標ごとの群準同型を関数群への準同型とする。
規約：正次数 n+1 の群を扱う。
使われ方：Goerss–Jardine I §7、VIII §2。cochain の各次数の関数群への比較。 -/
def homotopyMap : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialFunctionComplex.obj S X) n b →*
    (∀ s, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup X n (b s)) where
  toFun a s := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialFunctionComplex.eval S X s) rfl a
  map_one' := by
    funext s
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialFunctionComplex.eval S X s) rfl).map_one
  map_mul' a c := by
    funext s
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialFunctionComplex.eval S X s) rfl).map_mul a c

lemma homotopyMap_injective : Function.Injective (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.homotopyMap S X n b) := by
  intro a c h
  induction a using Quotient.inductionOn with | h f => ?_
  induction c using Quotient.inductionOn with | h g => ?_
  have hs (s : S) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialFunctionComplex.eval S X s) rfl f) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialFunctionComplex.eval S X s) rfl g) := congrFun h s
  have hr (s : S) : Nonempty (PtSimplex.RelStruct
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialFunctionComplex.eval S X s) rfl f) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialFunctionComplex.eval S X s) rfl g) 0) :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.simplexRel_iff_relStruct 0).mp ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk_eq_iff _ _).mp (hs s))
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.sound (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FunctionComplexPointedSimplex.relStruct (fun s ↦ Classical.choice (hr s)))

lemma homotopyMap_surjective : Function.Surjective (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.homotopyMap S X n b) := by
  intro a
  choose f hf using fun s ↦ Quotient.exists_rep (a s)
  refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FunctionComplexPointedSimplex.simplex f), ?_⟩
  funext s
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialFunctionComplex.eval S X s) rfl (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FunctionComplexPointedSimplex.simplex f)) = a s
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FunctionComplexPointedSimplex.eval_simplex]
  exact hf s

/-- 概要：関数複体のホモトピー群は座標ごとのホモトピー群の関数群と同型。
方針：評価の準同型の単射性と全射性を群同型へ束ねる。
規約：正次数 n+1、座標ごとの任意の基点。
使われ方：Goerss–Jardine I §7、VIII §2。群 cochain の π_* を係数の関数群で表す。 -/
def homotopyEquiv : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialFunctionComplex.obj S X) n b ≃*
    (∀ s, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup X n (b s)) :=
  MulEquiv.ofBijective (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.homotopyMap S X n b)
    ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.homotopyMap_injective S X n b, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.homotopyMap_surjective S X n b⟩

end

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
