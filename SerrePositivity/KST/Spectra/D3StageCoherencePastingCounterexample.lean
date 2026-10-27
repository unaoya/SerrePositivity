module

public import SerrePositivity.KST.Spectra.D3StageStructureCoherenceCriterion
public import Mathlib.CategoryTheory.Types.Basic

/-!
概要：既証の二つの段貼合せ関係だけから構造可換性を推論することを、具体例で排除する。
方針：Bool の交換同型で、両貼合せを満たし構造正方形は可換でない九つの同型を与える。
規約：これは一般の同型代数の反例。実 Sp の模型補正が非恒等だとは主張しない。
使われ方：d3b② で保持した模型補正を、既証の貼合せ関係だけで消去しないための検査。
-/

@[expose] public section
noncomputable section
open CategoryTheory
namespace SerrePositivity.KST.Spectra

/-- 一般の貼合せ代数の検査に使う、二点の交換同型。 -/
def d3BoolSwap : (Bool : Type) ≅ Bool where
  hom := TypeCat.ofHom Bool.not
  inv := TypeCat.ofHom Bool.not
  hom_inv_id := by ext b; cases b <;> rfl
  inv_hom_id := by ext b; cases b <;> rfl

lemma d3BoolSwap_ne_refl : d3BoolSwap ≠ Iso.refl Bool := by
  intro h
  have hh := congrArg (fun e : (Bool : Type) ≅ Bool ↦ e.hom false) h
  change true = false at hh
  cases hh

/-- 二つの指定貼合せが成立しても、構造正方形と補正の恒等性は同時に失敗し得る。
実際の Sp の比較に対する反例ではなく、貼合せ関係のみを用いる推論の反例。 -/
theorem d3PastingRelations_structureCounterexample :
    ∃ (a s r b q u d c w : (Bool : Type) ≅ Bool),
      (((a ≪≫ s) ≪≫ d) ≪≫ c = (r ≪≫ q) ≪≫ w) ∧
      (b ≪≫ d = q ≪≫ u) ∧
      (a ≪≫ s ≠ r ≪≫ b) ∧
      ((u ≪≫ c) ≪≫ w.symm ≠ Iso.refl Bool) := by
  refine ⟨Iso.refl _, d3BoolSwap, Iso.refl _, Iso.refl _, Iso.refl _, Iso.refl _,
    Iso.refl _, d3BoolSwap, Iso.refl _, ?_, ?_, ?_, ?_⟩
  · apply Iso.ext
    ext b
    cases b <;> rfl
  · rfl
  · simpa only [Iso.refl_trans] using d3BoolSwap_ne_refl
  · simpa only [Iso.refl_trans, Iso.refl_symm, Iso.trans_refl] using d3BoolSwap_ne_refl

end SerrePositivity.KST.Spectra
