module

public import SerrePositivity.KST.Comparison.BarZeroRows
public import SerrePositivity.KST.Comparison.FreeColumns
public import SerrePositivity.KST.Comparison.DiagonalRowEvaluation

/-!
# 正則 bar 束の第零行の評価

概要：第零行から対角への射を、標準ファイバー写像と基点の包含と同定する。
方針：長さ零の射列を定数の射列で表し、単体作用による引き戻しを計算する。
規約：Segal 1974 Propositions 1.5・1.6 のファイバーの比較の射を固定する。
使われ方：対角化の四角形を標準の bar のファイバーの四角形へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits Opposite MonoidalCategory
open scoped Simplicial

/--
概要：正則 bar の第零行の対角への評価は標準ファイバー写像である。
方針：唯一の対象で定数の射列を作る操作を計算する。
規約：二重単体集合の転置の対角の同型も明示する。
使われ方：元のモノイドから正則 bar への標準写像の比較。
-/
theorem regularBarZeroRow_evaluation (M : SimplicialObject MonCat.{u}) :
    diagonalRowEvaluation (actionBarTotal M) 0 ≫
      (diagonalFlipIso (bisimplicialRegularBar M)).hom =
    (simplexZeroTensorIso ((actionBarTotal M).obj (op ⦋0⦌))).hom ≫
      (regularBarZeroRowIso M).hom ≫ regularBarFiberMap M := by
  apply NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  rintro ⟨E, t⟩
  obtain ⟨a, rfl⟩ := ComposableArrows.mk₀_surjective E
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro i j f
  apply Subtype.ext
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

/--
概要：bar の第零行の対角への評価は標準の基点の包含である。
方針：一対象圏の定数の射列のラベルが単位であることを計算する。
規約：零単体への射は第零行の終対象との同型を使う。
使われ方：標準ファイバーの基底の比較。
-/
theorem monoidBarZeroRow_evaluation (M : SimplicialObject MonCat.{u}) :
    diagonalRowEvaluation (actionBarBase M) 0 ≫
      (diagonalFlipIso (bisimplicialBar M)).hom =
    (simplexZeroTensorIso ((actionBarBase M).obj (op ⦋0⦌))).hom ≫
      (monoidBarZeroRowIso M).hom ≫ SSet.yonedaEquiv.symm (monoidBarBasepoint M) := by
  apply NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  rintro ⟨E, t⟩
  obtain ⟨a, rfl⟩ := ComposableArrows.mk₀_surjective E
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro i j f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  change (1 : M.obj d) =
    (M.map (SimplexCategory.const d.unop ⦋0⦌ 0).op).hom 1
  exact (map_one _).symm

end SerrePositivity.KST.Comparison
