module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FilteredPointwiseWeakEquivalences
public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.CategoryTheory.Category.Preorder

/-!
# 元の Nat 図式の余極限の弱同値

概要：任意の宇宙の単体集合値 Nat 図式の成分ごとの弱同値は元の余極限でも弱同値。
方針：添字の対象と射だけを同じ宇宙へ持ち上げ、F2 の filtered 補題を使う。
規約：元の比較射 colim.map への一致を余極限の標準射で証明する。
使われ方：proper 図式の長さ濾過の余極限の比較。
-/

@[expose] public section
universe w
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.InfinityCategories

lemma weakSequentialColimitMap {F G : ℕ ⥤ SSet.{w}} (η : F ⟶ G)
    (hη : ∀ n, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (η.app n)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (colim.map η) := by
  let e := ULiftHomULiftCategory.equiv.{w, w} ℕ
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

end SerrePositivity.EInfinity.Hammock
