module

public import SerrePositivity.InfinityCategories.F1B.KanPinchedLeftMap
public import SerrePositivity.InfinityCategories.F1B.KanRelativeLimit
public import SerrePositivity.InfinityCategories.F1B.KanQCatEquivalenceOpposite

/-!
概要：相対終対象へ入る元の右 pinched 写像空間の作用はホモトピー同値。
方針：反転後の右模型の同値を左模型へ移し、coslice fiber と区間模型を介して元の右模型へ戻す。
規約：標的の射に inner 性を要求しない。
使われ方：右 Kan 関手の片側の相対写像空間比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

attribute [local instance] KanSection.vertexFiber_kanComplex_of_leftFibration

/-- 概要：指定左 pinched 作用が同値なら同じ両端の右 pinched 作用も同値。
方針：coslice fiber の同型の自然性で移し、区間模型を介する右模型の判定を使う。
規約：両全空間は quasicategory、射の充填性は不要。
使われ方：反転で得た片側の写像空間の比較を元の右模型へ戻す。 -/
lemma kanPinchedHomMap_equivalence_of_leftMap {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (f : X ⟶ Y) (x y : X _⦋0⦌)
    (h : IsQCatEquivalence (kanPinchedHomLeftMap f x y)) :
    IsSimplicialHomotopyEquivalence (pinchedHomMap f x y) := by
  apply (KanSection.pointCosliceFiberMap_equivalence_iff_pinchedHomMap f x y).1
  apply (qCatEquivalenceOfIso (KanSection.cosliceFiberPinchedLeftIso
    (f.app (Opposite.op ⦋0⦌) x) (f.app (Opposite.op ⦋0⦌) y))).isQCatEquivalence.cancel_right
  change IsQCatEquivalence (KanSection.pointCosliceFiberMap f x y ≫
    (KanSection.cosliceFiberPinchedLeftIso
      (f.app (Opposite.op ⦋0⦌) x) (f.app (Opposite.op ⦋0⦌) y)).hom)
  rw [kanCosliceFiberPinchedLeftIso_naturality]
  exact (qCatEquivalenceOfIso (KanSection.cosliceFiberPinchedLeftIso x y)).isQCatEquivalence.comp h

/-- 概要：相対終対象へ入る全ての右 pinched 写像空間の作用はホモトピー同値。
方針：相対終対象の定義を反転した左模型の同値へ移し、自然な模型比較で戻す。
規約：射に inner fibration 性は要求しない。
使われ方：標準相対右 Kan 関手を終点とする片側の相対比較。 -/
lemma kanRelativeTerminalVertex_pinchedHomMap_equivalence {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (f : X ⟶ Y) (x : X _⦋0⦌)
    (hx : KanRelativeTerminalVertex f x) (y : X _⦋0⦌) :
    IsSimplicialHomotopyEquivalence (pinchedHomMap f y x) := by
  apply kanPinchedHomMap_equivalence_of_leftMap f y x
  exact kanIsQCatEquivalence_op (hx (SSet.opObjEquiv.symm y)).isQCatEquivalence

end SerrePositivity.InfinityCategories.F1B
