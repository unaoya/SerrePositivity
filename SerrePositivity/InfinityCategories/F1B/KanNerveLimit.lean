module

public import SerrePositivity.InfinityCategories.F1B.KanNerveTerminal
public import SerrePositivity.InfinityCategories.F1B.KanNerveConeFamilyEquivalence

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
lemma kanNerveCone_isLimit_iff (c : Cone F) :
    IsLimitCone (kanNerveCone c) ↔ Nonempty (IsLimit c) := by
  rw [kanNerveCone_isLimit_iff_terminal, ← kanNerveVertex_isTerminal_iff]
  exact ⟨fun ⟨h⟩ ↦ ⟨c.isLimitEquivIsTerminal.symm h⟩,
    fun ⟨h⟩ ↦ ⟨c.isLimitEquivIsTerminal h⟩⟩

/-- 概要：任意の native な錐の極限性は読み戻した通常の錐の極限性と同値。
方針：錐の復元の右逆性と前向きの判定を使う。
規約：元の図式と native な指定錐を保持する。
使われ方：B5 の native な pointwise 条件からの回収。 -/
lemma kanConeOfNerveCone_isLimit_iff (c : JoinCone (nerveMap F)) :
    IsLimitCone c ↔ Nonempty (IsLimit (kanConeOfNerveCone c)) := by
  have h := kanNerveCone_isLimit_iff (kanConeOfNerveCone c)
  rwa [kanNerveCone_of_read] at h

/-- 概要：通常の図式の極限の存在と nerve の極限の存在は同値。
方針：錐の全単射と指定錐の普遍性の双方向比較を使う。
規約：同じ宇宙の小さい圏上の任意の図式を扱う。
使われ方：B5 の点ごとの Kan 拡張の存在条件の回収。 -/
lemma kanNerve_hasLimit_iff :
    SerrePositivity.InfinityCategories.HasLimit (nerveMap F) ↔ Limits.HasLimit F := by
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨h⟩ := (kanConeOfNerveCone_isLimit_iff c).1 hc
    exact ⟨⟨⟨kanConeOfNerveCone c, h⟩⟩⟩
  · intro h
    let := h
    exact ⟨kanNerveCone (limit.cone F), (kanNerveCone_isLimit_iff _).2 ⟨limit.isLimit F⟩⟩

end SerrePositivity.InfinityCategories.F1B
