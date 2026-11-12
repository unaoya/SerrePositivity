module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.WeightedConeSectionEquivalence

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.NerveOpposite
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.OppositeKanHomotopy
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.UniverseSSetMaps

/-!
概要：通常の余錐の添字と反対の錐の反転した添字の標準同型。
方針：nerve の反対の同型を反転し、二重反転と ULift の反転の同型を合成する。
規約：元の添字 I の頂点 i は反対の添字の op i に対応する。
使われ方：HTT 4.2.4.1、極限側の錐を元の添字の native な余錐へ戻す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section

/-- 概要：元の通常の添字の nerve の ULift と反対の添字の nerve の ULift の反転は同型。
方針：二重反転の逆、nerve の反対の同型の反転、ULift の反転の同型を合成する。
規約：I とその Hom は宇宙 u、追加の持ち上げは任意の v。
使われ方：通常の余錐の native な表示の添字を元の I に戻す。 -/
def strictCoconeIndexIso (I : Type u) [SmallCategory I] :
    (SSet.uliftFunctor.{v, u}).obj (nerve I) ≅
      ((SSet.uliftFunctor.{v, u}).obj (nerve Iᵒᵖ)).op :=
  (SSet.uliftFunctor.{v, u}).mapIso (SSet.opFunctorCompOpFunctorIso.app (nerve I)).symm ≪≫
    (SSet.uliftFunctor.{v, u}).mapIso (SSet.opFunctor.mapIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.nerveOppositeIso (C := I))) ≪≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.uliftOppositeIso (nerve Iᵒᵖ)

/-- 概要：余錐の添字の同型は元の頂点 i を反対の頂点 op i の反転へ写す。
方針：零次の射列の反転を計算し、唯一の対象成分で比較する。
規約：元の添字の頂点を変更せず表示だけを移す。
使われ方：native な余錐の図式の各対象を元の F(i) と照合する。 -/
lemma strictCoconeIndexIso_hom_vertex {I : Type u} [SmallCategory I] (i : I) :
    (strictCoconeIndexIso.{u, v} I).hom.app _ (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex i)) =
      SSet.opObjEquiv.symm (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Opposite.op i))) := by
  apply SSet.opObjEquiv.injective
  apply ULift.ext
  apply ComposableArrows.ext₀
  rfl

/-- 概要：余錐の添字の同型は、通常の反対の比較を反転して二重反転を除いたものと一致する。
方針：全次数の射列の反転の成分を計算する。
規約：後続の値域の二重反転との自然性に使える分解として述べる。
使われ方：双対化した図式と元の strict な図式の厳密な同定。 -/
lemma strictCoconeIndexIso_hom_factorization (I : Type u) [SmallCategory I] :
    (strictCoconeIndexIso.{u, v} I).hom =
      (SSet.opFunctorCompOpFunctorIso.app ((SSet.uliftFunctor.{v, u}).obj (nerve I))).inv ≫
        SSet.opFunctor.map ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.uliftOppositeIso (nerve I)).inv ≫
          (SSet.uliftFunctor.{v, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.nerveOppositeIso (C := I)).hom) := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro s
  rfl

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
