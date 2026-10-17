module
public import SerrePositivity.InfinityCategories.Derived.BaseChangeDG
public import SerrePositivity.InfinityCategories.Derived.InfinityCategory

/-! # 導来 ∞ 圏の底変更

概要：任意の可換環準同型に沿う D(S) から D(T) への写像を構成する。
方針：semifree 底変更の S 線形 dg 関手に dg nerve を適用し、係数制限の同型を合成する。
規約：平坦性は不要。使われ方：D(R) 上の BS 界面の係数変更。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded
open scoped Simplicial
variable {S T : Type u} [CommRing S] [CommRing T]

/-- 概要：可換環準同型は導来 ∞ 圏の底変更写像を与える。
方針：底変更の dg 関手と、係数制限による nerve の同型を合成する。
規約：semifree モデルなので追加の平坦性仮定はない。使われ方：D(S) から D(T) への移送。 -/
def derivedInfinityBaseChange (f : S →+* T) :
    derivedInfinityCategory S ⟶ derivedInfinityCategory T :=
  dgNerve.map (semifreeBaseChangeDG f) ≫ (dgNerveRestrictScalarsIso f (Semifree T)).hom

/-- 概要：底変更写像は頂点の複体を通常の係数拡大へ送る。
方針：dg nerve の写像と係数制限同型を次数零で評価する。
規約：対象の semifree 証明を除いた複体の等式。使われ方：底変更写像の対象の計算。 -/
theorem derivedInfinityBaseChange_vertex (f : S →+* T)
    (x : (derivedInfinityCategory S) _⦋0⦌) :
    (derivedInfinityCategoryVertexEquiv T ((derivedInfinityBaseChange f).app _ x)).val =
      (complexBaseChange f).obj (derivedInfinityCategoryVertexEquiv S x).val := rfl

end SerrePositivity.InfinityCategories
