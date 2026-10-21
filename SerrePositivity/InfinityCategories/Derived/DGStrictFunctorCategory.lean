module
public import SerrePositivity.InfinityCategories.Derived.DGStrictNatTransAlgebra
public import Mathlib.CategoryTheory.ComposableArrows.Basic
/-!
概要：元の dg 関手と厳密 dg 自然変換から、合成二単体を指定する通常の関手圏を作る。
方針：実閉零成分と全 Hom 自然性、元の単位・合成則を使う。
規約：dg nerve の変換の等式は別途実単体で証明する。
使われ方：一般 kernel 比較の恒等・合成 coherence。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
/-- 元の dg 関手を、厳密 dg 自然変換の通常の圏の対象として読む。 -/
structure DGStrictFunctor (R : Type u) [CommRing R] (C : Type v) (E : Type w)
    [DGCategory R C] [DGCategory R E] where
  /-- 元の同じ dg 関手。 -/
  toDGFunctor : DGFunctor R C E
/-- 厳密 dg 自然変換を射とする、元の dg 関手の通常の圏。 -/
instance dgStrictFunctorCategory (R : Type u) [CommRing R] (C : Type v) (E : Type w)
    [DGCategory R C] [DGCategory R E] : Category (DGStrictFunctor R C E) where
  Hom F G := StrictNatTrans F.toDGFunctor G.toDGFunctor
  id F := dgStrictNatTransId F.toDGFunctor
  comp a b := dgStrictNatTransComp a b
  id_comp := dgStrictNatTransComp_id_left
  comp_id := dgStrictNatTransComp_id_right
  assoc := dgStrictNatTransComp_assoc
end SerrePositivity.InfinityCategories
