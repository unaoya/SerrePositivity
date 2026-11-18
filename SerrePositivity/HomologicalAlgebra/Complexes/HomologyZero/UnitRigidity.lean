module

public import SerrePositivity.HomologicalAlgebra.Complexes.HomologyZero.HomotopyClasses

/-!
# 単位複体の自己射のホモトピーは等式を与える

概要：BF §1 の E の収縮から、単位上の厳密な三角形を取り出す。
方針：単位複体には非零の境界がなく、単位からの射は一の像で決まる。
規約：任意の可換基礎環。
使われ方：E(n) の augmentation の切断と係数ホモトピーの比較。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.HomologyZero

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex
open _root_.SerrePositivity.DifferentialGraded

variable {A : Type u} [CommRing A]

/-- 概要：単位の自己射の鎖ホモトピーは射の等式を与える（BF §1）。
方針：差の像を境界で表し、単位複体の零微分を使う。
規約：実際の零次集中した単位複体。
使われ方：可縮な E(n) の単位側の三角形を厳密化する。 -/
lemma unit_homotopy_eq {f g : 𝟙_ (Complex A) ⟶ 𝟙_ (Complex A)}
    (h : Homotopy f g) : f = g := by
  apply (unitCycleEquiv (𝟙_ (Complex A))).injective
  apply Subtype.ext
  obtain ⟨x, hx⟩ := (unit_homotopy_boundary (𝟙_ (Complex A)) f g).mp ⟨h⟩
  have hd : (𝟙_ (Complex A)).d (-1) 0 = 0 := rfl
  have hz : (cycleFromUnit (𝟙_ (Complex A)) f).val -
      (cycleFromUnit (𝟙_ (Complex A)) g).val = 0 := by
    simpa only [hd, ModuleCat.hom_zero, LinearMap.zero_apply] using hx.symm
  exact sub_eq_zero.mp hz

end SerrePositivity.HomologyZero
