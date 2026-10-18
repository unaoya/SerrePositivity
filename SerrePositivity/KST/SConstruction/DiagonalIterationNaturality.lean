module
public import SerrePositivity.KST.SConstruction.DiagonalIterationCoordinates
public import Mathlib.CategoryTheory.Monoidal.End
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory

/-! # 反復 S の座標比較の全単体的自然性
概要：最内側の S と元の反復の比較を、単体的自己関手の自然同型として構成する。
方針：自己関手の合成のモノイダル構造と、その関手圏の結合子を使う。
規約：次数と安定な入力の両方について自然。使われ方：実現の座標の照合。
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

/-- 概要：全方向を同じ単体次数へ制限した反復 S の自己関手の図式。
方針：多重添字を対角関手で制限する。
規約：値は安定な入力の自己関手。使われ方：合成の座標比較。 -/
def diagonalSEndofunctor (r : ℕ) :
    SimplexCategoryᵒᵖ ⥤ (StableModel.{u} ⥤ StableModel.{u}) :=
  multiIndexDiagonal r ⋙ multiSEndofunctor r

/-- 概要：零方向の反復は合成のモノイダル単位。
方針：定数の恒等自己関手の定義を使う。
規約：図式の厳密等号。使われ方：座標比較の帰納の始点。 -/
lemma diagonalSEndofunctor_zero :
    diagonalSEndofunctor.{u} 0 = 𝟙_ (SimplexCategoryᵒᵖ ⥤ (StableModel.{u} ⥤ StableModel.{u})) := rfl

/-- 概要：反復を一つ増やすことは外側への S の合成。
方針：多重反復の定義を対角へ制限して計算する。
規約：自己関手のテンソルは合成。使われ方：座標比較の結合子の適用。 -/
lemma diagonalSEndofunctor_succ (r : ℕ) :
    diagonalSEndofunctor.{u} (r + 1) = diagonalSEndofunctor r ⊗ simplicialStableEndofunctor := by
  refine CategoryTheory.Functor.ext
    (F := diagonalSEndofunctor (r + 1))
    (G := diagonalSEndofunctor r ⊗ simplicialStableEndofunctor) (fun _ => ?_) ?_
  · rfl
  · intro d e f
    apply NatTrans.ext
    funext X
    change _ = ((diagonalSEndofunctor r).map f ⊗ₘ simplicialStableEndofunctor.map f).app X
    rw [endofunctorMonoidalCategory_tensorMap_app]
    rfl

/-- 概要：最内側に S を合成した対角反復は元の反復と全単体的に自然に同型。
方針：合成の結合子で S の位置を一段ずつ移す。
規約：単体次数と安定な入力の両方の射について自然。使われ方：実現前の座標の同一視。 -/
def diagonalSInnerComparisonNatIso (r : ℕ) :
    simplicialStableEndofunctor.{u} ⊗ diagonalSEndofunctor r ≅ diagonalSEndofunctor (r + 1) := by
  induction r with
  | zero =>
    exact eqToIso (congrArg (fun F => simplicialStableEndofunctor ⊗ F)
        diagonalSEndofunctor_zero) ≪≫
      (ρ_ simplicialStableEndofunctor) ≪≫ (λ_ simplicialStableEndofunctor).symm ≪≫
      (eqToIso ((diagonalSEndofunctor_succ 0).trans
        (congrArg (fun F => F ⊗ simplicialStableEndofunctor)
          diagonalSEndofunctor_zero))).symm
  | succ r ih =>
    exact eqToIso (congrArg (fun F => simplicialStableEndofunctor ⊗ F)
        (diagonalSEndofunctor_succ r)) ≪≫
      (α_ _ _ _).symm ≪≫ whiskerRightIso ih simplicialStableEndofunctor ≪≫
      (eqToIso (diagonalSEndofunctor_succ (r + 1))).symm

end SerrePositivity.KST.SConstruction
