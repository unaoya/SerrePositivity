module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.BaseChangeDG
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.InfinityCategory

/-! # 導来 ∞ 圏の底変更

概要：任意の可換環準同型に沿う D(S) から D(T) への写像を構成する。
方針：semifree 底変更の S 線形 dg 関手に dg nerve を適用し、係数制限の同型を合成する。
規約：平坦性は不要。使われ方：D(R) 上の BS 界面の係数変更。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
open scoped _root_.Simplicial
variable {S T : Type u} [CommRing S] [CommRing T]

/-- 概要：可換環準同型は導来 ∞ 圏の底変更写像を与える。
方針：底変更の dg 関手と、係数制限による nerve の同型を合成する。
規約：semifree モデルなので追加の平坦性仮定はない。使われ方：D(S) から D(T) への移送。 -/
def derivedInfinityBaseChange (f : S →+* T) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory S ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory T :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeBaseChangeDG f) ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveRestrictScalarsIso f (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree T)).hom

/-- 概要：底変更写像は頂点の複体を通常の係数拡大へ送る。
方針：dg nerve の写像と係数制限同型を次数零で評価する。
規約：対象の semifree 証明を除いた複体の等式。使われ方：底変更写像の対象の計算。 -/
theorem derivedInfinityBaseChange_vertex (f : S →+* T)
    (x : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory S) _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategoryVertexEquiv T ((derivedInfinityBaseChange f).app _ x)).val =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexBaseChange f).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategoryVertexEquiv S x).val := rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories
