module
public import SerrePositivity.DifferentialGraded.Category.Components

/-! # 元の通常順 dg 合成と次数移送
概要：元の左右成分と出力の次数移送を、同じ通常順 dg 合成と交換する。
方針：元の整数次数の等号を消去し、同じ合成と符号に戻す。
規約：通常順・Koszul 符号を保持。使われ方：実分割最高生成元像の native HA 次数表示。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- 元の左右成分と出力の次数移送は、元の通常順 dg 合成と可換。 -/
lemma dgCompose_degree_transport {x y z : D} {p q n p' q' n' : ℤ}
    (hp : p = p') (hq : q = q') (hn : n = n')
    (g : GradedHom A y z q) (f : GradedHom A x y p)
    (hs : p + q = n) (hs' : p' + q' = n') :
    eqToHom (congrArg (homObject A D x z).X hn) (compose A g f hs) =
      compose A (eqToHom (congrArg (homObject A D y z).X hq) g)
        (eqToHom (congrArg (homObject A D x y).X hp) f) hs' := by
  cases hp
  cases hq
  cases hn
  rfl

end SerrePositivity.KST.SConstruction
