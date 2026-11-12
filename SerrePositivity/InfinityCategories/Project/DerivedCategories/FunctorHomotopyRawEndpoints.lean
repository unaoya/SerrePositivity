module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FunctorHomotopyRawTransport
/-!
概要：同じ円柱射を持つ二つの全単体ホモトピーから、両端の関手等式を回収する。
方針：同じ時刻零・一の制限を評価する。
規約：頂点ごとの一致に弱めない。使われ方：augmentation 正方形の端点輸送。
-/
@[expose] public section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet
/-- 円柱射の厳密な一致は、その両端の全関手の厳密な一致を与える。 -/
lemma functorHomotopy_endpoints_of_raw_eq {X Y : SSet.{u}} {f g f' g' : X ⟶ Y}
    (H : SSet.Homotopy f g) (H' : SSet.Homotopy f' g') (h : H.h = H'.h) :
    f = f' ∧ g = g' := by
  constructor
  · rw [← H.h₀, h, H'.h₀]
  · rw [← H.h₁, h, H'.h₁]
end SerrePositivity.InfinityCategories.Project.DerivedCategories
