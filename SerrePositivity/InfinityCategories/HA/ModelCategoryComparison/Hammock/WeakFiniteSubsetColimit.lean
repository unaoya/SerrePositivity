module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.WeakSequentialColimit
public import Mathlib.CategoryTheory.Limits.Connected
public import Mathlib.Data.Finset.Lattice.Basic

/-!
# 元の有限部分集合図式の余極限の弱同値と可縮性

概要：任意の有限部分集合図式の各項の弱比較を同じ余極限へ移す。
方針：添字だけを同じ宇宙へ持ち上げ F2 の filtered 補題と元の標準同型を使う。
規約：元の Finset 図式と同じ colim.map を保持する。
使われ方：全被覆の元の hammock の可縮性。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.SerrePositivity.InfinityCategories

lemma weakFiniteSubsetColimitMap {Q : Type u} {F G : Finset Q ⥤ SSet.{max u v}}
    (η : F ⟶ G) (hη : ∀ S, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (η.app S)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (colim.map η) := by
  classical
  let e := AsSmall.equiv.{u, u, max u v} (C := Finset Q)
  let L := e.inverse
  let τ := Functor.whiskerLeft L η
  have hτ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (colim.map τ) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.filteredColimitMap_isWeakHomotopyEquivalence_of_pointwise τ
      (fun i => hη (L.obj i))
  let iF := Functor.Final.colimitIso L F
  let iG := Functor.Final.colimitIso L G
  have hn : colim.map τ ≫ iG.hom = iF.hom ≫ colim.map η := by
    apply colimit.hom_ext
    intro i
    rw [← Category.assoc, colimit.ι_map, Category.assoc,
      Functor.Final.ι_colimitIso_hom, ← Category.assoc,
      Functor.Final.ι_colimitIso_hom, colimit.ι_map]
    rfl
  have hF := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso iF).isWeakHomotopyEquivalence
  have hG := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso iG).isWeakHomotopyEquivalence
  apply hF.cancel_left
  rw [← hn]
  exact hτ.comp hG

lemma finiteSubsetColimit_isWeaklyContractible {Q : Type u} (F : Finset Q ⥤ SSet.{max u v})
    (hF : ∀ S, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeaklyContractible (F.obj S)) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeaklyContractible (colimit F) := by
  classical
  let G := (Functor.const (Finset Q)).obj (⊤_ SSet.{max u v})
  let η : F ⟶ G :=
    { app S := terminal.from (F.obj S)
      naturality _ _ _ := terminal.hom_ext _ _ }
  have hw := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.weakFiniteSubsetColimitMap η hF
  let e : colimit G ≅ ⊤_ SSet.{max u v} :=
    (colimit.isColimit G).coconePointUniqueUpToIso
      (isColimitConstCocone (Finset Q) (⊤_ SSet.{max u v}))
  have he : terminal.from (colimit F) = colim.map η ≫ e.hom := terminal.hom_ext _ _
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (terminal.from (colimit F))
  rw [he]
  exact hw.comp (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso e).isWeakHomotopyEquivalence

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock
