module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentPrefixPathEnriched
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentPrefixConeTime
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.CosliceInitialCoordinates

/-!
概要：固定始点の coslice 比較を、各 tail 単体と時刻から実豊穣単体として構成する。
方針：対象写像に始点を前置し、時刻零の prefix 変形を元の cone へ前合成する。
規約：全次数で同じ元の cone と始点を保持する。
使われ方：零面の実族と最大化族の間の指定円柱。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SimplicialThickening SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の cone に prefix 変形を作用させた固定始点の実単体。 -/
def coherentPrefixConeSimplex {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {m n : ℕ} (s : (SimplicialNerve C) _⦋n + 1⦌)
    (a : Fin (m + 1) →o Fin (n + 1)) (t : Fin (m + 1) →o Fin 2) :
    (SimplicialNerve C) _⦋m + 1⦌ :=
  (coherentPrefixPathDeformationEnriched (prependOrderHom a).uliftMap
    ((coherentPrefixConeTime t).comp
      (⟨ULift.down, fun _ _ h ↦ h⟩ : ULift.{u} (Fin (m + 2)) →o _))).comp SSet s

/-- prefix 変形後も cone の始点は元の同じ対象。 -/
lemma coherentPrefixConeSimplex_apex {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {m n : ℕ} (s : (SimplicialNerve C) _⦋n + 1⦌)
    (a : Fin (m + 1) →o Fin (n + 1)) (t : Fin (m + 1) →o Fin 2) :
    (coherentPrefixConeSimplex s a t).obj ⟨ULift.up 0⟩ = s.obj ⟨ULift.up 0⟩ := rfl

/-- 固定始点の実単体は元の tail と時刻の添字変換を同時に保つ。 -/
lemma coherentPrefixConeSimplex_reindex {C : Type v}
    [Category.{u} C] [SimplicialCategory C] {l m n : ℕ}
    (s : (SimplicialNerve C) _⦋n + 1⦌)
    (a : Fin (m + 1) →o Fin (n + 1)) (t : Fin (m + 1) →o Fin 2)
    (r : Fin (l + 1) →o Fin (m + 1)) :
    (SimplicialThickening.functor (prependOrderHom r).uliftMap).comp SSet
      (coherentPrefixConeSimplex s a t) =
        coherentPrefixConeSimplex s (a.comp r) (t.comp r) := by
  change ((SimplicialThickening.functor (prependOrderHom r).uliftMap).comp SSet
    (coherentPrefixPathDeformationEnriched _ _)).comp SSet s = _
  rw [coherentPrefixPathDeformationEnriched_reindex]
  congr 2
  · ext i
    rcases i with ⟨i⟩
    induction i using Fin.cases with
    | zero => rfl
    | succ j => rfl
  · ext i
    rcases i with ⟨i⟩
    induction i using Fin.cases with
    | zero => rfl
    | succ j => rfl

end SerrePositivity.InfinityCategories.F2
