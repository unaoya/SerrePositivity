module

public import SerrePositivity.InfinityCategories.F1B.NerveComparison.Terminal
public import SerrePositivity.InfinityCategories.F1B.NerveComparison.ConeFamilyEquivalence

/-!
概要：通常の圏の極限と nerve の native な極限を双方向に比較する。
方針：錐の族の同値による終頂点性と通常の終対象性の比較を合成する。
規約：指定錐の普遍性と図式の極限の存在を区別する。
使われ方：B5 の pointwise Kan の局所極限条件の回収。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F1B

variable {I C : Type u} [Category.{u} I] [Category.{u} C] {F : I ⥤ C}

/-- 概要：通常の指定錐の極限性は nerve に移した錐の極限性と同値。
方針：通常の錐の終対象性と native な錐の族の終頂点性を合成する。
規約：極限構造の存在を Nonempty で表す。
使われ方：B5 の指定局所錐の双方向比較。 -/
lemma nerveCone_isLimit_iff (c : Cone F) :
    IsLimitCone (SerrePositivity.InfinityCategories.F1B.nerveCone c) ↔ Nonempty (IsLimit c) := by
  rw [SerrePositivity.InfinityCategories.F1B.nerveCone_isLimit_iff_terminal, ← SerrePositivity.InfinityCategories.F1B.nerveVertex_isTerminal_iff]
  exact ⟨fun ⟨h⟩ ↦ ⟨c.isLimitEquivIsTerminal.symm h⟩,
    fun ⟨h⟩ ↦ ⟨c.isLimitEquivIsTerminal h⟩⟩

/-- 概要：任意の native な錐の極限性は読み戻した通常の錐の極限性と同値。
方針：錐の復元の右逆性と前向きの判定を使う。
規約：元の図式と native な指定錐を保持する。
使われ方：B5 の native な pointwise 条件からの回収。 -/
lemma coneOfNerveCone_isLimit_iff (c : JoinCone (nerveMap F)) :
    IsLimitCone c ↔ Nonempty (IsLimit (SerrePositivity.InfinityCategories.F1B.coneOfNerveCone c)) := by
  have h := nerveCone_isLimit_iff (SerrePositivity.InfinityCategories.F1B.coneOfNerveCone c)
  rwa [SerrePositivity.InfinityCategories.F1B.nerveCone_of_read] at h

/-- 概要：通常の図式の極限の存在と nerve の極限の存在は同値。
方針：錐の全単射と指定錐の普遍性の双方向比較を使う。
規約：同じ宇宙の小さい圏上の任意の図式を扱う。
使われ方：B5 の点ごとの Kan 拡張の存在条件の回収。 -/
lemma nerve_hasLimit_iff :
    SerrePositivity.InfinityCategories.HasLimit (nerveMap F) ↔ Limits.HasLimit F := by
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨h⟩ := (coneOfNerveCone_isLimit_iff c).1 hc
    exact ⟨⟨⟨SerrePositivity.InfinityCategories.F1B.coneOfNerveCone c, h⟩⟩⟩
  · intro h
    let := h
    exact ⟨SerrePositivity.InfinityCategories.F1B.nerveCone (limit.cone F), (nerveCone_isLimit_iff _).2 ⟨limit.isLimit F⟩⟩

end SerrePositivity.InfinityCategories.F1B
