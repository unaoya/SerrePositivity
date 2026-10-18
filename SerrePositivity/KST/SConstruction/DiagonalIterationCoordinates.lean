module
public import SerrePositivity.KST.SConstruction.IteratedPathBoundary

/-! # 最内側の S と反復対角の対象の座標
概要：全方向に同じ次数を入れると、最内側に S を置く模型と元の反復の対象が一致する。
方針：方向数について帰納し、外側の S の同じ値を付け足す。
規約：一般反復での構造写像の自然性は別に証明する。使われ方：境界の座標の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：全方向が次数 n の反復に最内側の S_n を加えると n の反復を一つ増やした対象になる。
方針：外側の S_n を方向数について帰納的に付け足す。
規約：単体集合の対象の厳密等号。使われ方：対角の各次数の対象の照合。 -/
lemma multiSConstruction_diagonal_inner (r n : ℕ) (X : StableModel.{u}) :
    (multiSConstruction r (sStableModel n X)).obj (fun _ => Opposite.op ⦋n⦌) =
      (multiSConstruction (r + 1) X).obj (fun _ => Opposite.op ⦋n⦌) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [multiSConstruction_obj_succ, multiSConstruction_obj_succ]
    exact congrArg (sConstruction n) ih

/-- 概要：固定次数で最内側に S_n を置く反復は、元の反復自己関手と自然に同型。
方針：方向数について帰納し、関手の結合子と右単位子を使う。
規約：入力の射について自然。次数変更への自然性は別に示す。使われ方：座標比較の入力への整合性。 -/
def multiSEndofunctor_diagonal_inner_iso (r n : ℕ) :
    sEndofunctor.{u} n ⋙ (multiSEndofunctor r).obj (fun _ => Opposite.op ⦋n⦌) ≅
      (multiSEndofunctor (r + 1)).obj (fun _ => Opposite.op ⦋n⦌) := by
  induction r with
  | zero => exact Functor.rightUnitor (sEndofunctor n)
  | succ r ih =>
    change sEndofunctor n ⋙
        ((multiSEndofunctor r).obj (fun _ => Opposite.op ⦋n⦌) ⋙ sEndofunctor n) ≅
      (multiSEndofunctor (r + 1)).obj (fun _ => Opposite.op ⦋n⦌) ⋙ sEndofunctor n
    exact (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight ih (sEndofunctor n)

/-- 概要：最内側 S の反復実現の零回反復は元の単体的 core S の対角。
方針：零方向の反復は core のみとなることを計算する。
規約：厳密等号。使われ方：元の実現への接続。 -/
lemma iteratedSRealization_zero (X : StableModel.{u}) :
    iteratedSRealization 0 X = diagonalCoreSConstruction X.carrier := rfl

/-- 概要：経路の零回反復の全対角は元の S の経路実現。
方針：零方向の反復は core のみとなることを計算する。
規約：厳密等号。使われ方：元の経路の座標の回収。 -/
lemma iteratedPathRealization_zero (X : StableModel.{u}) :
    iteratedPathRealization 0 X = sPathRealization X.carrier := rfl

/-- 概要：零回反復の境界射は元の S の経路実現の境界射。
方針：先頭を忘れる面と零方向の反復を計算する。
規約：射の厳密等号。使われ方：既存の境界射の回収。 -/
lemma iteratedPathRealizationBoundary_zero (X : StableModel.{u}) :
    iteratedPathRealizationBoundary 0 X = sPathRealizationBoundary X.carrier := rfl

end SerrePositivity.KST.SConstruction
