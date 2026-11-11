module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModuleComplete.Closure

/-!
# 導来主元完備性と環のレトラクト

## 概要
環のレトラクトは、分裂射が対応させる座標に関する導来完備性を受け継ぐ。

## 方針
差分作用の単射性は包含で、全射性はレトラクションで移す。

## 規約
正則性を仮定しない。

## 使われ方
BS 著者版 Lemma 7.8 の prism の冪等射の分裂。
-/

public section

namespace SerrePositivity.DerivedCompletion

variable {B C : Type*} [CommRing B] [CommRing C]

/-- 概要：導来主元完備性は環の分裂した部分環に降りる。
方針：列の差分作用の全単射性を両脚に沿って移す。
規約：指定座標は包含で写した元。
使われ方：冪等な prism 射の固定環。 -/
theorem isModuleComplete_of_ring_retract (i : B →+* C) (r : C →+* B)
    (h : Function.LeftInverse r i) (b : B)
    (hc : IsModuleComplete C (i b) (ModuleCat.of C C)) :
    IsModuleComplete B b (ModuleCat.of B B) := by
  have hC := (isModuleComplete_iff_recurrence_bijective C (i b) (ModuleCat.of C C)).mp hc
  apply (isModuleComplete_iff_recurrence_bijective B b (ModuleCat.of B B)).mpr
  constructor
  · intro x y hxy
    have hh : adicRecurrenceMap (M := C) (i b) (i ∘ x) =
        adicRecurrenceMap (M := C) (i b) (i ∘ y) := by
      funext n
      change i (x n) - i b * i (x (n + 1)) = i (y n) - i b * i (y (n + 1))
      have hn : x n - b * x (n + 1) = y n - b * y (n + 1) := congrFun hxy n
      simpa only [map_sub, map_mul] using congrArg i hn
    funext n
    exact h.injective (congrFun (hC.1 hh) n)
  · intro x
    obtain ⟨y, hy⟩ := hC.2 (i ∘ x)
    refine ⟨r ∘ y, ?_⟩
    funext n
    change r (y n) - b * r (y (n + 1)) = x n
    have hy' : y n - i b * y (n + 1) = i (x n) := congrFun hy n
    simpa only [map_sub, map_mul, h b, h (x n)] using congrArg r hy'

end SerrePositivity.DerivedCompletion
