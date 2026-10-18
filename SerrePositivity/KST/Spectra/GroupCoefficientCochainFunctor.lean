module

public import SerrePositivity.KST.Spectra.GroupCoefficientCochains

/-!
概要：群の圏の作用の非斉次 cochain の係数への関手性。
方針：係数の同変準同型を各関数座標へ適用し、前合成との可換性を使う。
規約：群の可換性と有限性を要求しない。
使われ方：Goerss–Jardine VIII §2。自明な誘導作用の係数への移送。
-/

@[expose] public section

universe u

open CategoryTheory SSet

namespace SerrePositivity.KST.Spectra.GroupCoefficientCochains

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {G : Type u} [Group G]

/-- 概要：係数の同変準同型が誘導する非斉次 cochain の自然変換。
方針：各座標の値へ準同型を適用し、係数の同変性を使う。
規約：各次数の実際の群準同型。
使われ方：Goerss–Jardine VIII §2。π_* の誘導作用の比較を cochain へ送る。 -/
def map {A B : Action GrpCat.{u} G} (τ : A ⟶ B) : obj A ⟶ obj B where
  app _ := GrpCat.ofHom
    { toFun x s := τ.hom (x s)
      map_one' := by
        funext s
        exact τ.hom.hom.map_one
      map_mul' x y := by
        funext s
        exact τ.hom.hom.map_mul _ _ }
  naturality n m f := by
    ext x
    funext t
    let θ := (GroupActionCochains.freeUniversalCover G).map f.op
    change τ.hom ((A.ρ (θ.hom ((1 : G), t)).1).asHom (x (θ.hom ((1 : G), t)).2)) =
      (B.ρ (θ.hom ((1 : G), t)).1).asHom (τ.hom (x (θ.hom ((1 : G), t)).2))
    exact congr($(τ.comm (θ.hom ((1 : G), t)).1) (x (θ.hom ((1 : G), t)).2))

/-- 概要：群の作用の非斉次 cochain は係数に関する通常の関手。
方針：各座標の恒等・合成の式を余単体自然変換に束ねる。
規約：群の圏の作用から余単体群の圏への関手。
使われ方：Goerss–Jardine VIII §2。係数の同型による cochain の自然同型。 -/
def functor (G : Type u) [Group G] : Action GrpCat.{u} G ⥤ CosimplicialObject GrpCat.{u} where
  obj := obj
  map := map
  map_id A := by
    apply NatTrans.ext
    funext n
    ext x
    rfl
  map_comp τ υ := by
    apply NatTrans.ext
    funext n
    ext x
    rfl

end

end SerrePositivity.KST.Spectra.GroupCoefficientCochains
