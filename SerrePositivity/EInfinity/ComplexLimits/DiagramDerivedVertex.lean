module

public import SerrePositivity.EInfinity.ComplexLimits.OrdinaryDerivedSource

/-!
# 元の通常複体図式の導来頂点の同じ零単体輸送

概要：図式を nerve に送ってから導来化した頂点を、元の値の導来頂点へ照合する。
方針：元の nerveMap の零単体の式を同じ導来源で送る。
規約：元の図式と元の値の等式だけを用いる。
使われ方：自然変換の成分と導来単位の成分の厳密な照合。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open scoped Simplicial
variable (A : Type u) [CommRing A] {I : Type (u + 1)} [Category.{u} I]

lemma complexDiagramDerived_vertex (F : I ⥤ Complex A) (i : I) :
    (nerveMap F ≫ complexOrdinaryDerivedSource A).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex i) =
      (complexOrdinaryDerivedSource A).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (F.obj i)) :=
  congrArg ((complexOrdinaryDerivedSource A).app (Opposite.op ⦋0⦌)) (nerveMap_app_mk₀ F i)

def complexDiagramDerivedVertexIso (F : I ⥤ Complex A) (i : I) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso ((nerveMap F ≫ complexOrdinaryDerivedSource A).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex i)) ((complexOrdinaryDerivedSource A).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (F.obj i))) :=
  eqToIso (congrArg HomotopyCategory.mk (complexDiagramDerived_vertex A F i))

end SerrePositivity.EInfinity.ComplexLimits
