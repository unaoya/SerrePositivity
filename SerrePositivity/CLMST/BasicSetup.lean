module

public import SerrePositivity.CLMST.Inputs.BasicSetup

/-! # 文献の冪等性を局所的に供給した perfectoid almost 圏

mod p^N の perfectoid ideal の冪等性を名前付きの文献入力から供給し、
通常の全加群の almost 圏と局所化関手を具体的に定める。
冪等性の `Fact` は定義の内部だけで用い、全域の instance として登録しない。
明示的に `Fact` を置いた既存の `Almost.localization` と定義上同じ対象である。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.CLMST
open CategoryTheory

variable (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p) (g : R)

/-- mod p^N の全加群の perfectoid almost 圏。
文献入力の冪等性を定義の局所的な instance として供給する。 -/
abbrev perfectoidAlmostModCategory (N : ℕ) :=
  letI : Fact (perfectoidIdealMod R p hR g N * perfectoidIdealMod R p hR g N =
      perfectoidIdealMod R p hR g N) := ⟨Inputs.perfectoidIdealMod_idempotent R p hR g N⟩
  Almost.ModuleCategory (perfectoidIdealMod R p hR g N)

/-- mod p^N の加群から、その perfectoid almost 圏への局所化関手。
呼び出し側で冪等性の `Fact` を仮定する必要はない。 -/
abbrev perfectoidAlmostModLocalization (N : ℕ) :
    ModuleCat.{u} (R ⧸ Ideal.span {(p : R) ^ N}) ⥤ perfectoidAlmostModCategory R p hR g N :=
  letI : Fact (perfectoidIdealMod R p hR g N * perfectoidIdealMod R p hR g N =
      perfectoidIdealMod R p hR g N) := ⟨Inputs.perfectoidIdealMod_idempotent R p hR g N⟩
  Almost.localization (perfectoidIdealMod R p hR g N)

/-- 明示的な冪等性の証拠を置いた場合、名前付き局所化は既存の局所化と定義上同じ。 -/
theorem perfectoidAlmostModLocalization_eq (N : ℕ)
    [Fact (perfectoidIdealMod R p hR g N * perfectoidIdealMod R p hR g N =
      perfectoidIdealMod R p hR g N)] :
    perfectoidAlmostModLocalization R p hR g N =
      Almost.localization (perfectoidIdealMod R p hR g N) := rfl

end SerrePositivity.CLMST
