module
public import SerrePositivity.KST.SConstruction.DiagonalIterationNaturality
public import SerrePositivity.KST.SConstruction.InnerZeroDirectionCoordinates

/-! # 反復 S の全単体的な座標同型の成分
概要：全単体的に自然な座標同型を次数ごとの結合子による座標同型と照合する。
方針：安定な入力で成分を取り、単位子と結合子を計算する。
規約：既存の公開同型の定義は変更しない。使われ方：最内側の零方向との比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory
open scoped Simplicial
attribute [local instance] CategoryTheory.endofunctorMonoidalCategory

/-- 概要：反復零回の座標比較の成分は恒等射。
方針：二つの単位子の成分を計算する。
規約：任意の次数と安定な入力。使われ方：成分比較の帰納の始点。 -/
lemma diagonalSInnerComparisonNatIso_zero_app (d : SimplexCategoryᵒᵖ) (X : StableModel.{u}) :
    ((diagonalSInnerComparisonNatIso 0).hom.app d).app X =
      𝟙 ((sEndofunctor d.unop.len).obj X) := by
  simp [diagonalSInnerComparisonNatIso, Nat.recAux, diagonalSEndofunctor,
    simplicialStableEndofunctor, multiSEndofunctor, multiIndexDiagonal]

/-- 概要：反復を増やした座標比較の成分は外側の S が前の成分を写したもの。
方針：結合子と右テンソル積の成分を計算する。
規約：図式全体の自然同型をそのまま使う。使われ方：次数ごとの座標同型との照合。 -/
lemma diagonalSInnerComparisonNatIso_succ_app (r : ℕ) (d : SimplexCategoryᵒᵖ)
    (X : StableModel.{u}) :
    ((diagonalSInnerComparisonNatIso (r + 1)).hom.app d).app X =
      (sEndofunctor d.unop.len).map
        (((diagonalSInnerComparisonNatIso r).hom.app d).app X) := by
  simp [diagonalSInnerComparisonNatIso, Nat.recAux, diagonalSEndofunctor,
    simplicialStableEndofunctor, multiSEndofunctor, multiIndexDiagonal]
  exact Category.id_comp _

/-- 概要：全単体的な座標同型の各次数の成分は結合子による次数ごとの同型に一致。
方針：反復数について帰納し、成分の再帰式を照合する。
規約：自然変換そのものの厳密等号。使われ方：最内側の可変次数の比較との接続。 -/
lemma diagonalSInnerComparisonNatIso_app_eq (r n : ℕ) :
    (diagonalSInnerComparisonNatIso.{u} r).hom.app (Opposite.op ⦋n⦌) =
      (multiSEndofunctor_diagonal_inner_iso r n).hom := by
  induction r with
  | zero =>
    apply NatTrans.ext
    funext X
    exact diagonalSInnerComparisonNatIso_zero_app (Opposite.op ⦋n⦌) X
  | succ r ih =>
    apply NatTrans.ext
    funext X
    calc
      _ = (sEndofunctor n).map
          (((diagonalSInnerComparisonNatIso r).hom.app (Opposite.op ⦋n⦌)).app X) :=
        diagonalSInnerComparisonNatIso_succ_app r (Opposite.op ⦋n⦌) X
      _ = (sEndofunctor n).map
          ((multiSEndofunctor_diagonal_inner_iso r n).hom.app X) :=
        congrArg (sEndofunctor n).map (NatTrans.congr_app ih X)
      _ = _ := by
        change _ = 𝟙 _ ≫ (sEndofunctor n).map
          ((multiSEndofunctor_diagonal_inner_iso r n).hom.app X)
        exact (Category.id_comp _).symm

end SerrePositivity.KST.SConstruction
