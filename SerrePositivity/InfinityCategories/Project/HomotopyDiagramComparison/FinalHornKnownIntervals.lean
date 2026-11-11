module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.IntervalChoice

/-!
概要：最終外側ホーンの未知二区間以外から、元の既知面による豊穣関手を回収する。
方針：左端が正なら面零、右端が penultimate 未満なら面 penultimate を使う。
規約：内ホーンの欠損頂点条件を仮定しない。使われ方：HTT 5.2.4.6 の外側充填。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory MonoidalCategory SSet
open CategoryTheory.SimplicialThickening

open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
variable {C : Type v} [Category.{u} C] [SimplicialCategory C] {n : ℕ}
  (σ : (Λ[n + 2, Fin.last (n + 2)] : SSet.{max u v}) ⟶ SimplicialNerve C)

/-- 最終外側ホーンの、欠ける最終頂点の一つ前の頂点。 -/
def finalHornPenultimate (n : ℕ) : Fin (n + 3) := (Fin.last (n + 1)).castSucc

/-- 同じ penultimate 頂点は最終頂点より小さい。 -/
lemma finalHornPenultimate_lt_last (n : ℕ) :
    finalHornPenultimate n < Fin.last (n + 2) := by
  change n + 1 < n + 2
  omega

/-- 二次元以上では、同じ penultimate 頂点は零より大きい。 -/
lemma finalHornPenultimate_pos (n : ℕ) : 0 < finalHornPenultimate n := by
  change 0 < n + 1
  omega

/-- 最終頂点より小さく penultimate と異なる頂点は、その前にある。 -/
lemma lt_finalHornPenultimate_of_lt_last_ne (b : Fin (n + 3))
    (hb : b < Fin.last (n + 2)) (hne : b ≠ finalHornPenultimate n) :
    b < finalHornPenultimate n := by
  have hb' : b.val < n + 2 := hb
  have hne' : b.val ≠ n + 1 := fun h ↦ hne (Fin.ext h)
  change b.val < n + 1
  omega

/-- 最終外側ホーンで、未知二区間以外の元の区間であるという条件。 -/
def FinalHornKnownInterval {n : ℕ} (a b : Fin (n + 3)) : Prop :=
  a ≠ 0 ∨ b < finalHornPenultimate n

/-- 既知の零面または penultimate 面から、同じ既知閉区間の豊穣関手を回収する。 -/
def finalHornKnownIntervalFunctor (a b : Fin (n + 3)) (hp : FinalHornKnownInterval a b) :
    EnrichedFunctor SSet
      (SimplicialThickening (Set.Icc (ULift.up.{u} a) (ULift.up.{u} b))) C := by
  let j : Fin (n + 3) := if a = 0 then finalHornPenultimate n else 0
  have hj : j ≠ Fin.last (n + 2) := by
    by_cases ha : a = 0
    · simpa only [j, ite_eq_left ha] using ne_of_lt (finalHornPenultimate_lt_last n)
    · simp only [j, ite_eq_right ha]
      exact ne_of_lt ((finalHornPenultimate_pos n).trans (finalHornPenultimate_lt_last n))
  have hout : j < a ∨ b < j := by
    by_cases ha : a = 0
    · simp only [j, ite_eq_left ha]
      exact Or.inr (hp.resolve_left (fun h ↦ h ha))
    · simp only [j, ite_eq_right ha]
      exact Or.inl (lt_of_le_of_ne (Fin.zero_le a) (Ne.symm ha))
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornIntervalViaFace σ j hj a b hout

/-- 回収した区間関手は元のホーンの同じ頂点対象を持つ。 -/
lemma finalHornKnownIntervalFunctor_obj (a b : Fin (n + 3)) (hp : FinalHornKnownInterval a b)
    (x : SimplicialThickening (Set.Icc (ULift.up.{u} a) (ULift.up.{u} b))) :
    (finalHornKnownIntervalFunctor σ a b hp).obj x = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ x.as.val.down := rfl

/-- 回収した区間関手は、区間外のどの既知面からの回収にも一致する。 -/
lemma finalHornKnownIntervalFunctor_eq_viaFace (a b : Fin (n + 3))
    (hp : FinalHornKnownInterval a b) (j : Fin (n + 3)) (hj : j ≠ Fin.last (n + 2))
    (hout : j < a ∨ b < j) :
    finalHornKnownIntervalFunctor σ a b hp = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornIntervalViaFace σ j hj a b hout := by
  unfold finalHornKnownIntervalFunctor
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornIntervalViaFace_independent σ a b _ j _ hj _ hout

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
