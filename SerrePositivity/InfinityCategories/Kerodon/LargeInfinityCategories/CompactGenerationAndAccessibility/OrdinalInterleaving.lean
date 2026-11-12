module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.SmallPieceChains
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.NerveFinalInitialComma
public import Mathlib.Order.Prod.Lex.Basic

/-!
概要：長さ κ₀ の相対交互構成の二成分を一つの順序添字へ交互に含める。
方針：正則順序と二点順序の辞書式積を取り、各成分の comma に最小対象を作る。
規約：κ₀-filtered 性と両成分の全 nerve の cofinal 性を保持する。
使われ方：両成分の像の元の余極限を一つの全交互図式から比較する。

対応節は Kerodon 9.4（Tag 06GT）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility

/-- 概要：各正則順序段の左・右を交互に並べる元の添字。
方針：二点との辞書式積を取る。
規約：同じ宇宙の小さい順序を使う。
使われ方：長さ κ の全交互図式の形状。 -/
abbrev AlternatingIndex (κ : Cardinal.{u}) := Lex (κ.ord.ToType × Fin 2)

/-- 概要：指定成分を各段の同じ位置へ含める関手。
方針：固定成分の辞書式順序への単調性を使う。
規約：二つの成分を別々の無関係な図式へ交換しない。
使われ方：全交互図式の両成分への制限。 -/
def alternatingSection (κ : Cardinal.{u}) (c : Fin 2) : κ.ord.ToType ⥤ AlternatingIndex κ :=
  (show Monotone (fun a : κ.ord.ToType ↦ toLex (a, c)) from by
    intro a b hab
    exact Prod.Lex.toLex_le_toLex.mpr
      (hab.lt_or_eq.elim Or.inl (fun h ↦ Or.inr ⟨h, le_rfl⟩))).functor

/-- 概要：正則順序の全交互添字は κ-filtered。
方針：小さい族の段を一段へ集め、次の段で両位置を上から抑える。
規約：元の両成分を含む全添字についての結論。
使われ方：accessible 圏に存在する元の交互余極限の形状。 -/
lemma alternatingIndex_isCardinalFiltered (κ : Cardinal.{u}) [Fact κ.IsRegular] :
    IsCardinalFiltered (AlternatingIndex κ) κ := by
  have : NoMaxOrder κ.ord.ToType := Cardinal.noMaxOrder (Cardinal.IsRegular.aleph0_le Fact.out)
  apply isCardinalFiltered_preorder
  intro K f hK
  have hK' := (hasCardinalLT_iff_cardinal_mk_lt K κ).mpr hK
  obtain ⟨a, ⟨ha⟩⟩ := IsCardinalFiltered.exists_max
    (κ := κ) (fun k ↦ (ofLex (f k)).1) hK'
  refine ⟨toLex (Order.succ a, 0), fun k ↦ ?_⟩
  exact Prod.Lex.le_iff.mpr (Or.inl ((leOfHom (ha k)).trans_lt (Order.lt_succ a)))

/-- 概要：交互添字の各固定成分は全 nerve 上で right cofinal。
方針：各 comma の最小段を、同じ段または次段として明示する。
規約：元の全交互図式に対する cofinal 性。
使われ方：同じ全余極限を両成分の余極限として回収する。 -/
lemma alternatingSection_isRightCofinal (κ : Cardinal.{u}) [Fact κ.IsRegular] (c : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal (nerveMap (alternatingSection κ c)) := by
  have : NoMaxOrder κ.ord.ToType := Cardinal.noMaxOrder (Cardinal.IsRegular.aleph0_le Fact.out)
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.nerveMap_isRightCofinal_of_initial_comma
  intro k
  let a := (ofLex k).1
  let b := (ofLex k).2
  let n := if b ≤ c then a else Order.succ a
  have hn : k ≤ (alternatingSection κ c).obj n := by
    change k ≤ toLex (n, c)
    apply Prod.Lex.le_iff.mpr
    change a < n ∨ a = n ∧ b ≤ c
    by_cases h : b ≤ c
    · simpa only [n, ite_eq_left h] using
        (Or.inr ⟨rfl, h⟩ : a < a ∨ a = a ∧ b ≤ c)
    · simp only [n, ite_eq_right h]
      exact Or.inl (Order.lt_succ a)
  refine ⟨StructuredArrow.mk (homOfLE hn), ⟨IsInitial.ofUniqueHom (fun y ↦ ?_) ?_⟩⟩
  · have hy : k ≤ (alternatingSection κ c).obj y.right := leOfHom y.hom
    change k ≤ toLex (y.right, c) at hy
    have hny : n ≤ y.right := by
      have hy' : a < y.right ∨ a = y.right ∧ b ≤ c := Prod.Lex.le_iff.mp hy
      rcases hy' with h | ⟨h, hbc⟩
      · dsimp only [n]
        split_ifs <;> first | exact h.le | exact Order.succ_le_of_lt h
      · have h' : b ≤ c := hbc
        simpa only [n, ite_eq_left h'] using h.le
    exact StructuredArrow.homMk (homOfLE hny) (by subsingleton)
  · intro y g
    apply StructuredArrow.hom_ext
    exact Subsingleton.elim _ _

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility
