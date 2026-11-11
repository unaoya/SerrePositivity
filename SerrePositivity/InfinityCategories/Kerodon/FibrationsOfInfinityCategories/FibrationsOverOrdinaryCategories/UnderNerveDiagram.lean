module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.LeftStrictTransport

/-!
概要：undercategory の nerve を底上の対象の反変図式としてまとめる。
方針：通常の射に Under.map の nerve を対応させ、厳密な恒等・合成則を使う。
規約：底は元の通常の圏 C の nerve。
使われ方：Kerodon Construction 5.3.1.5（Tag 035J）、Corollary 5.6.0.6（Tag 028T）、strict transport の底の図式。

対応節は Kerodon 5.3（Tag 035A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

/-- 概要：各対象の undercategory の nerve は元の nerve 上の反変図式をなす。
方針：射影を対象とし、通常の射には底を保つ nerveUnderMap を使う。
規約：自然同型ではなく厳密な関手則を満たす。
使われ方：Kerodon Construction 5.3.1.5（Tag 035J）、strict transport の相対 Hom の定義域の族。 -/
def underNerveDiagram (C : Type u) [Category.{u} C] : Cᵒᵖ ⥤ Over (nerve C) where
  obj c := Over.mk (nerveMap (Under.forget c.unop))
  map f := Over.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.nerveUnderMap f.unop) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.nerveUnderMap_projection f.unop)
  map_id c := by
    apply Over.OverMorphism.ext
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.nerveUnderMap_id c.unop
  map_comp f g := by
    apply Over.OverMorphism.ext
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.nerveUnderMap_comp g.unop f.unop

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
