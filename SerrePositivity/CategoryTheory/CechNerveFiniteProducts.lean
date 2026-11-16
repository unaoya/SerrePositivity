module

public import SerrePositivity.CategoryTheory.CechNerveData
public import Mathlib.AlgebraicTopology.CechNerve

/-!
概要：Mathlib の指定有限冪の Čech 図式を、同じ射影を保って CechNerveData で読む。
方針：元の productIsProduct と Pi.lift の計算則をそのまま使う。
規約：BS 著者版 Construction 4.18 の通常圏の有限冪の表示の法則。
使われ方：S8 の商の上の Čech 解消に、構成済みの comma の収縮を使う。
-/

@[expose] public noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.CechNerveData
variable {C : Type u} [Category.{v} C] [HasFiniteProducts C]

/-- 同じ有限冪、同じ射影、同じ単体作用素を持つ元の Mathlib の Čech 図式。 -/
def ofFiniteProducts (U : C) : CechNerveData U where
  obj := cechNerveTerminalFrom U
  proj n i := Pi.π (fun _ : Fin (n + 1) => U) i
  isLimit n := productIsProduct (fun _ : Fin (n + 1) => U)
  proj_map θ i := by
    exact Pi.lift_comp_π _ _

end CategoryTheory.CechNerveData
