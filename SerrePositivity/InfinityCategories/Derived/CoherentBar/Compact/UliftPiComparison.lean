module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.UliftPointedFilling
/-!
概要：指定基点での正次数 π は追加の宇宙持ち上げで変わらない。
方針：同じ球面代表と充填の上下操作を商へ降ろし、積の充填も保持する。
規約：追加宇宙は任意で、元の頂点と元の代表を使う。
使われ方：持ち上げた native 評価空間の π チャートを、元の評価空間へ戻す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet
open SerrePositivity.KST.Spectra
open scoped _root_.Simplicial
variable (X : SSet.{u}) [KanComplex X] (n : ℕ) (x : X _⦋0⦌)

def dgBarCompactPiUliftUp : KanHomotopyGroup X n x →
    KanHomotopyGroup ((SSet.uliftFunctor.{v, u}).obj X) n (ULift.up x) :=
  Quotient.map dgBarCompactPointedSimplexUp (by
    intro f g h
    obtain ⟨r⟩ := (simplexRel_iff_relStruct (X := X) 0).mp h
    exact (simplexRel_iff_relStruct (X := (SSet.uliftFunctor.{v, u}).obj X) 0).mpr
      ⟨dgBarCompactPointedRelUp r⟩)

def dgBarCompactPiUliftDown :
    KanHomotopyGroup ((SSet.uliftFunctor.{v, u}).obj X) n (ULift.up x) →
      KanHomotopyGroup X n x :=
  Quotient.map dgBarCompactPointedSimplexDown (by
    intro f g h
    obtain ⟨r⟩ := (simplexRel_iff_relStruct (X := (SSet.uliftFunctor.{v, u}).obj X) 0).mp h
    exact (simplexRel_iff_relStruct (X := X) 0).mpr ⟨dgBarCompactPointedRelDown r⟩)

/-- 元の代表を保つ、任意追加宇宙での全基点 π 群同型。 -/
def dgBarCompactUliftPiEquiv : KanHomotopyGroup X n x ≃*
    KanHomotopyGroup ((SSet.uliftFunctor.{v, u}).obj X) n (ULift.up x) where
  toFun := dgBarCompactPiUliftUp X n x
  invFun := dgBarCompactPiUliftDown X n x
  left_inv a := by
    induction a using Quotient.inductionOn with | h f => ?_
    change KanHomotopyGroup.mk (dgBarCompactPointedSimplexDown
      (dgBarCompactPointedSimplexUp.{u, v} f)) = KanHomotopyGroup.mk f
    exact congrArg KanHomotopyGroup.mk
      ((dgBarCompactUliftPointedSimplexEquiv X (n + 1) x).left_inv f)
  right_inv a := by
    induction a using Quotient.inductionOn with | h f => ?_
    change KanHomotopyGroup.mk (dgBarCompactPointedSimplexUp.{u, v}
      (dgBarCompactPointedSimplexDown f)) = KanHomotopyGroup.mk f
    exact congrArg KanHomotopyGroup.mk
      ((dgBarCompactUliftPointedSimplexEquiv X (n + 1) x).right_inv f)
  map_mul' a b := by
    induction a using Quotient.inductionOn with | h f => ?_
    induction b using Quotient.inductionOn with | h g => ?_
    obtain ⟨r⟩ := KanHomotopyGroup.productSimplex_spec f g
    exact (KanHomotopyGroup.mul_eq (dgBarCompactPointedMulUp.{u, v} r)).symm

end SerrePositivity.InfinityCategories
