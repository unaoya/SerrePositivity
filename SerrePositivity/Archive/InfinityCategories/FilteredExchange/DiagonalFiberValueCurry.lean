module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.DiagonalFiberTransport
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes

/-!
概要：二独立係数の対角 fiber 輸送の値を、全関手空間の作用へ curry する。
方針：前合成・係数制限・後合成の三つの自然性を使う。
規約：同じ普遍輸送を保持。使われ方：左 Hom 全係数比較の自然性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.F2

/-- 対角輸送の同じ二係数と終点値を curry した作用の厳密な式。 -/
lemma diagonalFiberValue_curry {E B A H Y : SSet.{u}} (p : E ⟶ B) [LeftFibration p]
    {a b : B.obj (Opposite.op (SimplexCategory.mk 0))}
    (C : A ⟶ vertexFiber p a) (k : H ⟶ intervalMappingSpace a b)
    (V : vertexFiber p b ⟶ Y) :
    curry (diagonalFiberTransport p (fst A H ≫ C) (snd A H ≫ k) ≫ V) =
      (k ≫ parametrizedFiberTransport p a b ≫ (pre C).app (vertexFiber p b)) ≫
        (ihom A).map V := by
  rw [curry_natural_right]
  congr 1
  apply uncurry_injective
  rw [uncurry_curry, ← Category.assoc k, uncurry_pre_app, uncurry_natural_left]
  change diagonalFiberTransport p (fst A H ≫ C) (snd A H ≫ k) =
    (C ▷ H) ≫ (vertexFiber p a ◁ k) ≫
      uncurry (curry (parametrizedFiberTransportFamily p a b).endpoint)
  rw [uncurry_curry]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro x
  rfl

end SerrePositivity.InfinityCategories.F2
