module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.RelativeSectionDiagram
public import Mathlib.AlgebraicTopology.SimplicialSet.Simplices
public import Mathlib.CategoryTheory.Category.ULift

/-!
概要：任意の底の単体を実際の単体集合の射として束ねる標準図式。
方針：要素の圏の射を逆向きの底上の標準単体の射へ写す。
規約：対象は単体の型のまま、射の宇宙だけを係数の宇宙へ揃える。
使われ方：全単体の切断を同時に coherent に実現する添字図式。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 概要：切断の制限の向きで取った底の全単体の圏。
方針：要素の圏の射を係数の宇宙へ持ち上げる。
規約：通常の単体圏の反対向き。退化単体も全て含む。
使われ方：全切断の coherent な図式の添字圏。 -/
abbrev TransportSimplexCategory (B : SSet.{u}) := ULiftHom.{u} B.Elements

/-- 概要：各単体を底上の実際の標準単体として束ねる。
方針：Yoneda 同値とその自然性で対象と底上の射を定める。
規約：添字圏の反対圏からの通常の関手。
使われ方：相対切断の共同図式への入力。 -/
def transportSimplexDomainFunctor (B : SSet.{u}) :
    (TransportSimplexCategory B)ᵒᵖ ⥤ Over B where
  obj s := Over.mk (show stdSimplex.obj s.unop.objDown.obj.unop ⟶ B from
    SSet.yonedaEquiv.symm s.unop.objDown.val)
  map {s t} f := Over.homMk (stdSimplex.map f.unop.down.hom.unop) (by
    change stdSimplex.map f.unop.down.hom.unop ≫
      SSet.yonedaEquiv.symm t.unop.objDown.val = SSet.yonedaEquiv.symm s.unop.objDown.val
    rw [SSet.yonedaEquiv_symm_naturality_left]
    exact congrArg SSet.yonedaEquiv.symm f.unop.down.map_val)
  map_id s := by
    apply Over.OverMorphism.ext
    exact stdSimplex.map_id _
  map_comp f g := by
    apply Over.OverMorphism.ext
    exact stdSimplex.map_comp _ _

/-- 概要：底の指定単体を切断の添字圏の対象にする。
方針：次数と単体を要素の圏の対象へ入れる。
規約：単体のデータを変更しない。
使われ方：各次数の切断空間の回収。 -/
def transportSimplexIndex {B : SSet.{u}} {n : SimplexCategory} (σ : B.obj (Opposite.op n)) :
    TransportSimplexCategory B :=
  ULiftHom.objUp (B.elementsMk (Opposite.op n) σ)

/-- 概要：面・退化を与える任意の単体作用素は切断の制限の添字の射となる。
方針：作用素とその値の定義的な等式を要素の圏へ入れる。
規約：単射な作用素だけに制限しない。
使われ方：全次数の面・退化と切断の系を結ぶ。 -/
def transportSimplexRestriction {B : SSet.{u}} {m n : SimplexCategory}
    (α : m ⟶ n) (σ : B.obj (Opposite.op n)) :
    transportSimplexIndex σ ⟶ transportSimplexIndex (B.map α.op σ) :=
  ⟨{ hom := α.op, map_val := rfl }⟩

/-- 概要：単体作用素の底上の射は元の標準単体の射そのもの。
方針：標準図式と添字の射の定義を展開する。
規約：基底の可換性の証明の選択には依存しない。
使われ方：coherent な切断の系で元の面と退化を回収する。 -/
lemma transportSimplexDomainFunctor_restriction {B : SSet.{u}} {m n : SimplexCategory}
    (α : m ⟶ n) (σ : B.obj (Opposite.op n)) :
    ((transportSimplexDomainFunctor B).map (transportSimplexRestriction α σ).op).left =
      stdSimplex.map α := rfl

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
