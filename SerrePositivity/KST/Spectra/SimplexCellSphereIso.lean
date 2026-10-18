module

public import SerrePositivity.KST.Spectra.SimplexCellCofiber
public import SerrePositivity.Spectra.Pointed.CofiberPushout
public import SerrePositivity.Spectra.PointedSimplicialSet.Spheres

/-!
概要：自由基点を加えて作ったセルの球面と境界の通常の商の球面の同型。
方針：同じ点つき span の二つの pushout の一意性を使う。
規約：既存 Spectra から借りるのは通常の cofiber の pushout の普遍性だけ。
使われ方：Goerss–Jardine I §7、VIII §1。セルの群の計算を既存の球面の界面へ移す。
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits SSet
open scoped Simplicial

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：自由基点を加えた射の点つき cofiber は元の射の商と同型。
方針：零対象への射との二つの pushout の普遍性を比較する。
規約：元の単体集合に基点や Kan 条件を要求しない。
使われ方：Goerss–Jardine I §7。球面の二つの商模型の比較。 -/
def adjoinCofiberIso {K L : SSet.{u}} (f : K ⟶ L) :
    pointedCofiber (PointedObject.adjoinFunctor.map f) ≅ PointedObject.cofiber f :=
  (pointedCofiber_isPushout (PointedObject.adjoinFunctor.map f)).isoIsPushout _ _
    (PointedObject.cofiber_isPushout f)

/-- 概要：セルの球面と境界を直接潰した球面の標準同型。
方針：境界包含へ自由基点の cofiber の比較を適用する。
規約：零次元も含む。
使われ方：Goerss–Jardine I §7、VIII §1。球面の Hom の正次数の群の計算。 -/
def SimplexCell.sphereIso (d : ℕ) : sphere.{u} d ≅ PointedSimplicialSet.sphere.{u} d :=
  adjoinCofiberIso (∂Δ[d].ι : (∂Δ[d] : SSet.{u}) ⟶ Δ[d])

end

end SerrePositivity.KST.Spectra
