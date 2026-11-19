module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Products.SimplicialDependentProduct

/-!
概要：関数複体の境界定数単体と関係充填を座標ごとに構成する。
方針：単体と RelStruct の充填射を関数複体への lift で束ねる。
規約：座標ごとの基点と同じ面添字を使う。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.3（Tag 00W3）。cochain の関数空間のホモトピー群。

対応節は Kerodon 3.2（Tag 00V2）。
-/

@[expose] public section

universe u

open CategoryTheory SSet
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra.SimplicialDependentProduct
end SerrePositivity.KST.Spectra.SimplicialDependentProduct
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.DependentProductPointedSimplex
open _root_.SerrePositivity.KST.Spectra
open _root_.SerrePositivity.KST.Spectra.SimplicialDependentProduct

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {S : Type u} {X : S → SSet.{u}} {n : ℕ} {b : ∀ s, (X s) _⦋0⦌}

/-- 概要：各座標の境界定数単体を関数複体の境界定数単体へ束ねる。
方針：充填射を lift し、境界の式を各評価で検査する。
規約：基点は指定した基点の関数。
使われ方：Goerss–Jardine I §7。関数複体のホモトピー類の代表。 -/
def simplex (f : ∀ s, (X s).PtSimplex n (b s)) : (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialDependentProduct.obj S X).PtSimplex n b where
  map := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialDependentProduct.lift (fun s ↦ (f s).map)
  comm := by
    apply _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialDependentProduct.hom_ext
    intro s
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialDependentProduct.lift_eval]
    change (boundary n).ι ≫ (f s).map = SSet.const (b s)
    simp

lemma eval_simplex (f : ∀ s, (X s).PtSimplex n (b s)) (s : S) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialDependentProduct.eval S X s) rfl (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.DependentProductPointedSimplex.simplex f) = f s := by
  apply RelativeMorphism.ext
  exact _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialDependentProduct.lift_eval _ s

/-- 概要：各評価での関係充填を関数複体の一つの関係充填へ束ねる。
方針：全ての面の式を各評価で確認する。
規約：全ての座標で同じ面添字を使う。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.3（Tag 00W3）。関数複体のホモトピー類の識別。 -/
def relStruct {f g : (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialDependentProduct.obj S X).PtSimplex n b} {i : Fin (n + 1)}
    (r : ∀ s, PtSimplex.RelStruct (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialDependentProduct.eval S X s) rfl f)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialDependentProduct.eval S X s) rfl g) i) : PtSimplex.RelStruct f g i where
  map := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialDependentProduct.lift (fun s ↦ (r s).map)
  δ_castSucc_map := by
    apply _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialDependentProduct.hom_ext
    intro s
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialDependentProduct.lift_eval]
    exact (r s).δ_castSucc_map
  δ_succ_map := by
    apply _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialDependentProduct.hom_ext
    intro s
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialDependentProduct.lift_eval]
    exact (r s).δ_succ_map
  δ_map_of_lt j hj := by
    apply _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialDependentProduct.hom_ext
    intro s
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialDependentProduct.lift_eval, SSet.const_comp]
    exact (r s).δ_map_of_lt j hj
  δ_map_of_gt j hj := by
    apply _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialDependentProduct.hom_ext
    intro s
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialDependentProduct.lift_eval, SSet.const_comp]
    exact (r s).δ_map_of_gt j hj

end

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.DependentProductPointedSimplex

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
