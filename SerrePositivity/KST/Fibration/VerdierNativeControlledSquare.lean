module
public import SerrePositivity.KST.Fibration.VerdierNativeControlledUpperPrism
public import SerrePositivity.InfinityCategories.Stable.SquarePrismGluing

/-!
概要：同じ実 (9b) 欠面と元の下側二胞体を保持する一つの四角形を構成する。
方針：対角固定三角柱の終端から指定共有対角を回収し、二三角形表示で貼る。
規約：新しい充填や存在仮定を使わない。
使われ方：K-6 c4 の正規化四角柱の始端を、元の指定四角形へ戻す比較対象。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
variable (d : _root_.SerrePositivity.InfinityCategories.Stable.Infinity.VerdierDiagram.{u}) (k : (Δ[1] : SSet.{u + 1}) _⦋0⦌)

/-- 概要：同じ実制御欠面の対角は元の Verdier 四角形の指定対角。
方針：同じ対角固定三角柱の終端を評価する。
規約：元の実二胞体の対角を厳密保持。使われ方：元の下側との貼り合わせ。 -/
theorem verdierNativeControlledUpper_diagonal :
    stdSimplex.δ (1 : Fin 3) ≫ familyAtVertex
      (zeroMiddleNativeUpperFamily (verdierUpperTriangle d)
        (verdierUpperTriangle_middle_isZero d) Δ[1]) k =
      squareDiagonal ≫ (d.square ≫ coherentNerveMap (stableMultiKanEnrichedFunctor 0)) := by
  let U := verdierNativeControlledUpperPrism d k
  have ht : stdSimplex.δ (1 : Fin 3) ≫ familyAtVertex
      (zeroMiddleNativeUpperFamily (verdierUpperTriangle d)
        (verdierUpperTriangle_middle_isZero d) Δ[1]) k =
      stdSimplex.δ (1 : Fin 3) ≫
        (squareTriangle 0 ≫ (d.square ≫ coherentNerveMap (stableMultiKanEnrichedFunctor 0))) := by
    calc
      _ = SSet.ι₁ ≫ (fst (Δ[1] : SSet.{u + 1}) Δ[1] ≫ stdSimplex.δ (1 : Fin 3) ≫
          familyAtVertex (zeroMiddleNativeUpperFamily (verdierUpperTriangle d)
            (verdierUpperTriangle_middle_isZero d) Δ[1]) k) := by
        rw [← Category.assoc, SSet.ι₁_fst, Category.id_comp]
      _ = SSet.ι₁ ≫ (stdSimplex.δ (1 : Fin 3) ▷ (Δ[1] : SSet.{u + 1})) ≫ U.h :=
        congrArg (fun f => SSet.ι₁ ≫ f) (verdierNativeControlledUpperPrism_diagonal d k).symm
      _ = stdSimplex.δ (1 : Fin 3) ≫ (SSet.ι₁ ≫ U.h) := by
        rw [← Category.assoc, SSet.ι₁_comp, Category.assoc]
      _ = _ := congrArg (fun f => stdSimplex.δ (1 : Fin 3) ≫ f) U.h₁
  exact ht.trans (by rw [← Category.assoc, squareTriangle_diagonal])

/-- 概要：同じ実指定欠面と元の下側二胞体を持つ実四角形。
方針：同じ元の共有対角で二三角形表示を貼る。
規約：元の二胞体を選び直さない。使われ方：始端有限照合の共通の比較対象。 -/
def verdierNativeControlledSquare : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ SpaceInfinity.{u} :=
  square_isPushout.desc
    (familyAtVertex (zeroMiddleNativeUpperFamily (verdierUpperTriangle d)
      (verdierUpperTriangle_middle_isZero d) Δ[1]) k)
    (squareTriangle 1 ≫ (d.square ≫ coherentNerveMap (stableMultiKanEnrichedFunctor 0)))
    ((verdierNativeControlledUpper_diagonal d k).trans (by
      simpa only [Category.assoc] using! congrArg
        (fun f => f ≫ (d.square ≫ coherentNerveMap (stableMultiKanEnrichedFunctor 0)))
          (squareTriangle_diagonal (1 : Fin 2)).symm))

/-- 概要：同じ実制御四角形の上側は指定欠面そのもの。
方針：押し出しの第一制限を回収。
規約：全二胞体の厳密等式。使われ方：有限始端照合。 -/
theorem verdierNativeControlledSquare_upper :
    squareTriangle 0 ≫ verdierNativeControlledSquare d k =
      familyAtVertex (zeroMiddleNativeUpperFamily (verdierUpperTriangle d)
        (verdierUpperTriangle_middle_isZero d) Δ[1]) k :=
  square_isPushout.inl_desc _ _ _

/-- 概要：同じ実制御四角形の下側は元の Verdier 下側そのもの。
方針：押し出しの第二制限を回収。
規約：元の全二胞体を保持。使われ方：正規化下側の始端照合。 -/
theorem verdierNativeControlledSquare_lower :
    squareTriangle 1 ≫ verdierNativeControlledSquare d k =
      squareTriangle 1 ≫ (d.square ≫ coherentNerveMap (stableMultiKanEnrichedFunctor 0)) :=
  square_isPushout.inr_desc _ _ _

end SerrePositivity.KST.Fibration
