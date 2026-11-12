module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.IntervalFunctorMap
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.ConstantAdjunct

/-!
概要：区間写像空間の関手による後合成は h Fun の後合成を表す。
方針：代表辺を後合成し、定値関手の合成による端点の輸送を明示する。
規約：標的・パラメータの quasicategory 性は不要。
使われ方：単位による写像空間比較の任意パラメータでの公式。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：同じ一次単体を持つ辺の Hom 類は端点の輸送と整合する。
方針：端点の等式を消去し、辺の外延性を使う。
規約：任意の単体集合。
使われ方：後合成での定値関手の端点の同一視。 -/
lemma homMk_transport {X : SSet.{u}} {x y x' y' : X _⦋0⦌}
    (hx : x = x') (hy : y = y')
    (e : SSet.Truncated.Edge (X := (truncation 2).obj X) x y)
    (e' : SSet.Truncated.Edge (X := (truncation 2).obj X) x' y') (he : e.edge = e'.edge) :
    eqToHom (congrArg HomotopyCategory.mk hx).symm ≫
      SSet.Truncated.HomotopyCategory.homMk e ≫
        eqToHom (congrArg HomotopyCategory.mk hy) = SSet.Truncated.HomotopyCategory.homMk e' := by
  subst x' y'
  have h : e = e' := SSet.Truncated.Edge.ext he
  subst e'
  simp

/-- 概要：区間模型の族の後合成は定値関手間の h Fun の後合成に対応する。
方針：curry の後合成自然性で代表辺を比較し、両端を輸送する。
規約：定値関手の合成の同一視は constantFunctorCompIso を使う。
使われ方：指定単位の比較写像の任意のパラメータでの作用。 -/
lemma intervalFunctorMap_familyHom {A X Y : SSet.{u}} {x y : X _⦋0⦌}
    (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y) (F : X ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFunctorMap F x y) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.constantFunctorCompIso A x F).inv ≫
        (hoFunctor.map ((ihom A).map F)).toFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom f) ≫
          (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.constantFunctorCompIso A y F).hom := by
  symm
  apply homMk_transport
    (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const_comp x F))
    (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const_comp y F))
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyEdge f).map ((truncation 2).map ((ihom A).map F)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyEdge (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFunctorMap F x y))
  change ((ihom A).map F).app (Opposite.op ⦋1⦌)
      (SSet.yonedaEquiv (curry (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHomotopy f).h)) =
    SSet.yonedaEquiv (curry (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHomotopy (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFunctorMap F x y)).h)
  rw [← SSet.yonedaEquiv_comp, ← curry_natural_right]
  congr 2

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
