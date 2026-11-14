module
public import SerrePositivity.KST.SConstruction.GappedFrame

/-! # gapped 図式の cofiber 列
概要：全区間の押し出し条件から、各三つ組の cofiber 列を取り出す。
方針：四角形の零角は対角の頂点に一致する。
規約：BGT Definition 7.1 の三つ組条件を明示する。
使われ方：第一行の復元と Grothendieck 群の関係式。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：区間の cofiber 四角形の左上角は対角 F(j,j)。
方針：正方形の nerve 表示を零次元で計算する。
規約：零角は (0,1)。使われ方：ZeroTriangle の構成。 -/
lemma arSquare_cofiber_zero_corner {n : ℕ} {C : SSet.{u}} (F : arNerve n ⟶ C)
    (i j k : Fin (n + 1)) (hij : i ≤ j) (hjk : j ≤ k) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (arSquare i j j k hij le_rfl hjk ≫ F) 0 1 =
      F.app (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ (arObj j j le_rfl)) := by
  apply congrArg (F.app (Opposite.op ⦋0⦌))
  exact ComposableArrows.ext₀ rfl

/-- 概要：gapped 図式の三つ組から零角の四角形を取り出す。
方針：零対角条件を cofiber 四角形の左上角へ移す。
規約：i≤j≤k。使われ方：BGT Definition 7.1 の cofiber 列。 -/
def gappedCofiberTriangle {n : ℕ} {C : SSet.{u}} {F : arNerve n ⟶ C}
    (hF : IsGapped F) (i j k : Fin (n + 1)) (hij : i ≤ j) (hjk : j ≤ k) : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroTriangle C where
  square := arSquare i j j k hij le_rfl hjk ≫ F
  zero_corner := by
    rw [arSquare_cofiber_zero_corner]
    exact hF.1 j

/-- 概要：gapped 図式の F(i,j)→F(i,k)→F(j,k) は cofiber 列。
方針：gapped の四角形条件を j=k の中間端点に適用する。
規約：退化三つ組も含む。使われ方：π₀ K と三角関係の比較。 -/
lemma gappedCofiberTriangle_isCofiber {n : ℕ} {C : SSet.{u}} {F : arNerve n ⟶ C}
    (hF : IsGapped F) (i j k : Fin (n + 1)) (hij : i ≤ j) (hjk : j ≤ k) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsCofiberSequence (gappedCofiberTriangle hF i j k hij hjk) := hF.2 i j j k hij le_rfl hjk

end SerrePositivity.KST.SConstruction
