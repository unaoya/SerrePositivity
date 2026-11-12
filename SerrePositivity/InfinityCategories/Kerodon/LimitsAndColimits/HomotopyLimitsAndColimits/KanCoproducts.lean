module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.SimplicialCoproducts

/-!
概要：小さい Kan 複体の族の次数ごとの直和は Kan 複体である。
方針：ホーンの交わる面の成分添字を同定し、一つの Kan 成分で充填して直和へ戻す。
規約：一次元のホーンを別に扱い、空の族を排除しない。
使われ方：HTT 4.2.4.1、Kerodon 7.5.4.6（Tag 03BB） の 𝒮 の実際の余積の対象。

対応節は Kerodon 7.5（Tag 039Y）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
variable {J : Type u}

/-- 概要：直和に入る一つのホーンの指定された面の成分添字は全て等しい。
方針：二次元以上では面の交わりの等式、一次元では唯一の指定された面を使う。
規約：二つの面は欠ける面以外とする。
使われ方：Kerodon 7.5.4.6（Tag 03BB）、ホーン全体を同じ Kan 成分に戻す準備。 -/
lemma simplicialCoproduct_horn_simplexLabel_eq (F : J → SSet.{u}) {n : ℕ}
    {i : Fin (n + 2)}
    (f : ∀ (j : Fin (n + 2)) (_ : j ≠ i), (Δ[n] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialCoproduct F)
    (hf : horn.IsCompatible f) (j k : Fin (n + 2)) (hj : j ≠ i) (hk : k ≠ i) :
    (SSet.yonedaEquiv (f j hj)).1 = (SSet.yonedaEquiv (f k hk)).1 := by
  cases n with
  | zero =>
    have h : j = k := by omega
    subst k
    rfl
  | succ n =>
    rcases lt_trichotomy j k with h | h | h
    · have he := congrArg (fun g : (Δ[n] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialCoproduct F ↦
        (SSet.yonedaEquiv g).1) (hf.δ_pred_comp j k hj hk h)
      simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialCoproduct_simplexLabel_face] using he
    · subst k
      rfl
    · have he := congrArg (fun g : (Δ[n] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialCoproduct F ↦
        (SSet.yonedaEquiv g).1) (hf.δ_pred_comp k j hk hj h)
      simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialCoproduct_simplexLabel_face] using he.symm

/-- 概要：任意の小さい Kan 複体の族の直和は Kan 複体。
方針：指定された面を同じ成分に因子分解し、包含の単射性で整合性を戻して Kan 充填を使う。
規約：有限性と添字の非空性は要求しない。
使われ方：HTT 4.2.4.1、Kerodon 7.5.4.6（Tag 03BB）、𝒮 の小さい余積の Kan 性。 -/
instance simplicialCoproduct_kanComplex (F : J → SSet.{u}) [∀ j, KanComplex (F j)] :
    KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialCoproduct F) := by
  classical
  rw [KanComplex.iff]
  intro n i f hf
  obtain ⟨j₀, hj₀⟩ := exists_ne i
  let a := (SSet.yonedaEquiv (f j₀ hj₀)).1
  have hfactor (j : Fin (n + 2)) (hj : j ≠ i) :
      ∃ g : (Δ[n] : SSet.{u}) ⟶ F a, g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialCoproductι F a = f j hj :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialCoproduct_simplex_factorization F (f j hj) a
      (simplicialCoproduct_horn_simplexLabel_eq F f hf j j₀ hj hj₀)
  choose g hg using hfactor
  have hcompat : horn.IsCompatible g := by
    cases n with
    | zero => trivial
    | succ n =>
      rw [horn.isCompatible_iff]
      intro j k hj hk hjk
      apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialCoproductι_cancel F a
      simp only [Category.assoc, hg]
      exact hf.δ_pred_comp j k hj hk hjk
  obtain ⟨φ, hφ⟩ := hcompat.exists_lift_of_kanComplex
  refine ⟨φ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialCoproductι F a, fun j hj ↦ ?_⟩
  rw [← Category.assoc, hφ j hj, hg]

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
