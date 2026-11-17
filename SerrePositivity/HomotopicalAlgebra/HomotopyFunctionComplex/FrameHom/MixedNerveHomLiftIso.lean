module
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedNerveHomRecovery
/-! 概要：元の混合宇宙の全パラメータ nerve と Hom 持ち上げの実同型。
方針：同じ up・down の両往復を全単体で検証する。
規約：元の対象・全射列を保持する。
使われ方：全要素圏の同じ相対屋根の弱同値検出。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedNerve
open _root_.CategoryTheory _root_.SSet
variable (C : Type (u + 1)) [Category.{u} C]

/-- 概要：元の Hom 宇宙を上げて戻す全 nerve の往復は恒等。
方針：元の全単体列を比較する。規約：元の全射を保持。
使われ方：全パラメータの実逆写像。 -/
lemma up_down : _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedNerve.up C ≫ _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedNerve.down C = 𝟙 _ := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro Γ
  change (Γ ⋙ ULiftHom.up.{u, u + 1, u + 1}) ⋙ ULiftHom.down.{u, u + 1, u + 1} = Γ
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro i j f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

/-- 概要：同じ全パラメータ nerve の Hom 持ち上げは実同型。
方針：元の up・down と両往復を束ねる。
規約：別のパラメータ空間を選ばない。使われ方：相対屋根の全族回収。 -/
def homLiftIso : nerve (ULiftHom.{u + 1} C) ≅ nerve C where
  hom := _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedNerve.down C
  inv := _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedNerve.up C
  hom_inv_id := _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedNerve.down_up C
  inv_hom_id := _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedNerve.up_down C

end SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedNerve
