module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor.DGStrictNatTransAlgebra
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
/-- 元の dg 関手を、厳密 dg 自然変換の通常の圏の対象として読む。 -/
structure DGStrictFunctor (R : Type u) [CommRing R] (C : Type v) (E : Type w)
    [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] where
  /-- 元の同じ dg 関手。 -/
  toDGFunctor : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C E
/-- 厳密 dg 自然変換を射とする、元の dg 関手の通常の圏。 -/
instance dgStrictFunctorCategory (R : Type u) [CommRing R] (C : Type v) (E : Type w)
    [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] : Category (DGStrictFunctor R C E) where
  Hom F G := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F.toDGFunctor G.toDGFunctor
  id F := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransId F.toDGFunctor
  comp a b := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransComp a b
  id_comp := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransComp_id_left
  comp_id := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransComp_id_right
  assoc := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransComp_assoc
end SerrePositivity.InfinityCategories.Project.DerivedCategories
