module
public import SerrePositivity.KST.SConstruction.CubicalSerreDayAssociativity
public import SerrePositivity.KST.SConstruction.CubicalSerreDayUnitCoherence

/-! # 全 cubical sets の Serre 鎖の強モノイダル関手
概要：元の Day 鎖比較と単位同型を、結合・左右単位を保つ関手へ束ねる。
方針：独立な全 cell 上で証明した組み立ての自然性と coherent 法則を適用する。
規約：元の鎖関手と順逆の比較を保持。使われ方：cubical rigidification の鎖への移送。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の cubical Serre 鎖を Day モノイダル圏上の関手として読む。 -/
def cubicalDaySerreChains : CubicalDaySet.{u} ⥤ Complex A :=
  cubicalDayEquivalence.functor ⋙ cubicalSerreChains A

/-- 元の Day 比較と単位同型を持つ、Serre 鎖の強モノイダルデータ。 -/
def cubicalDaySerreCoreMonoidal : (cubicalDaySerreChains A).CoreMonoidal where
  εIso := (cubicalSerreDayUnitIso A).symm
  μIso X Y := (cubicalSerreDayIso A X.functor Y.functor).symm
  μIso_hom_natural_left := by
    intro X Y f X'
    change (cubicalSerreChains A).map f.natTrans ▷ (cubicalSerreChains A).obj X'.functor ≫
        cubicalSerreDayInverse A Y.functor X'.functor =
      cubicalSerreDayInverse A X.functor X'.functor ≫
        (cubicalSerreChains A).map (f ▷ X').natTrans
    have h := cubicalSerreDayInverse_naturality A f.natTrans (𝟙 X'.functor)
    have hm : cubicalDayTensorMap f.natTrans (𝟙 X'.functor) = (f ▷ X').natTrans := by
      change (f ⊗ₘ 𝟙 X').natTrans = (f ▷ X').natTrans
      rw [tensorHom_id]
    rw [CategoryTheory.Functor.map_id, tensorHom_id, hm] at h
    exact h
  μIso_hom_natural_right := by
    intro X Y X' f
    change (cubicalSerreChains A).obj X'.functor ◁ (cubicalSerreChains A).map f.natTrans ≫
        cubicalSerreDayInverse A X'.functor Y.functor =
      cubicalSerreDayInverse A X'.functor X.functor ≫
        (cubicalSerreChains A).map (X' ◁ f).natTrans
    have h := cubicalSerreDayInverse_naturality A (𝟙 X'.functor) f.natTrans
    have hm : cubicalDayTensorMap (𝟙 X'.functor) f.natTrans = (X' ◁ f).natTrans := by
      change (𝟙 X' ⊗ₘ f).natTrans = (X' ◁ f).natTrans
      rw [id_tensorHom]
    rw [CategoryTheory.Functor.map_id, id_tensorHom, hm] at h
    exact h
  associativity X Y Z := cubicalSerreDayInverse_associativity A X.functor Y.functor Z.functor
  left_unitality X := cubicalSerreDayInverse_leftUnit A X.functor
  right_unitality X := cubicalSerreDayInverse_rightUnit A X.functor

/-- 元の全 cubical sets 上で、Serre 鎖は Day tensor を保つ強モノイダル関手。 -/
instance cubicalDaySerreMonoidal : (cubicalDaySerreChains A).Monoidal :=
  (cubicalDaySerreCoreMonoidal A).toMonoidal

end SerrePositivity.KST.SConstruction
