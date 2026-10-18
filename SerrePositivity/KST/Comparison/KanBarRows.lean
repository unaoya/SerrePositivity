module

public import SerrePositivity.KST.Comparison.BarTupleKan
public import SerrePositivity.KST.Comparison.ActionBarSquares

/-!
# Kan モノイドの bar の各行と射影

概要：基礎単体集合が Kan であるモノイドの bar の各行は Kan で、正則 bar の行の射影は Kan fibration。
方針：有限積座標と正則作用の積座標の同型を使う。
規約：Segal 1974 Proposition 1.6 の Kan な行の模型。
使われ方：各行の homotopy-cartesian 性を対角の比較へ接続する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits HomotopicalAlgebra MonoidalCategory CartesianMonoidalCategory Opposite
open SSet.modelCategoryQuillen
open scoped Simplicial

/--
概要：Kan な基礎単体集合を持つモノイドの bar の各行は Kan 複体である。
方針：有限積座標への同型と、同型に沿った fibrant 性の移送を使う。
規約：bar の外側の添字は nerve の次数。
使われ方：Segal の各行の比較の基底の Kan 性。
-/
instance monoidBarRow_kanComplex (M : SimplicialObject MonCat.{u}) (r : ℕ)
    [SSet.KanComplex (monoidSpace M)] : SSet.KanComplex ((actionBarBase M).obj (op ⦋r⦌)) := by
  let : (fibrations SSet.{u}).IsStableUnderComposition := by
    rw [fibrations_eq]
    infer_instance
  exact isFibrant_of_fibration (monoidBarRowIso M r).hom

/--
概要：Kan モノイドの正則 bar の各行の射影は Kan fibration である。
方針：基礎モノイドをファイバーとする積射影を同型で移す。
規約：基底の各行の Kan 性を仮定しなくても射影の Kan 条件は成立する。
使われ方：各行の厳密引き戻しをホモトピー引き戻しとして計算する。
-/
theorem actionBarProjection_row_rlp (M : SimplicialObject MonCat.{u}) (r : ℕ)
    [SSet.KanComplex (monoidSpace M)] :
    SSet.modelCategoryQuillen.J.rlp ((actionBarProjection M).app (op ⦋r⦌)) := by
  rw [← regularBarRowIso_fst]
  exact SSet.modelCategoryQuillen.J.rlp.comp_mem _ _
    (SSet.modelCategoryQuillen.J.rlp.of_isIso _) (productProjection_rlp _ _)

/--
概要：Kan モノイドの正則 bar の各行も Kan 複体である。
方針：各行の Kan な基底への Kan fibration による射影を使う。
規約：群状性はこの性質には不要。
使われ方：Segal の比較の全空間の各行の Kan 性。
-/
instance regularBarRow_kanComplex (M : SimplicialObject MonCat.{u}) (r : ℕ)
    [SSet.KanComplex (monoidSpace M)] : SSet.KanComplex ((actionBarTotal M).obj (op ⦋r⦌)) := by
  let : (fibrations SSet.{u}).IsStableUnderComposition := by
    rw [fibrations_eq]
    infer_instance
  have : Fibration ((actionBarProjection M).app (op ⦋r⦌)) :=
    (fibration_iff _).mpr (actionBarProjection_row_rlp M r)
  exact isFibrant_of_fibration ((actionBarProjection M).app (op ⦋r⦌))

end SerrePositivity.KST.Comparison
