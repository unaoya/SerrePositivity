module

public import SerrePositivity.InfinityCategories.F1.CocartesianBaseChangeSecondTriangleCurry
public import SerrePositivity.InfinityCategories.F1.CocartesianBaseChangeTriangleTranspose
public import SerrePositivity.InfinityCategories.F1.CocartesianBaseChangeAssociativityYoneda
public import SerrePositivity.InfinityCategories.F1.TransportSimplexSectionBaseChange

/-!
概要：元の第二比較の分解を、全 fibration の関手空間内の同じ大域二単体にする。
方針：同じ全高次の族を転置し、各面を元の比較の一単体へ戻す。
規約：長辺は元の大域比較三角形の第二辺そのもの。
使われ方：元の Hom 比較 span の第二辺の輸送を分解する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

variable {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
  (l : A ⥤ D) (k : D ⥤ C)

/-- 元の全 fibration 上の関手空間内にある、第二比較の同じ分解二単体。 -/
def cocartesianBaseChangeSecondGlobalTriangleSimplex :
    ((ihom (CocartesianFibrationInfinity (nerve C))).obj
      (CatInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj (nerve A)))) _⦋2⦌ :=
  SSet.yonedaEquiv (transposeFunctorFamily (cocartesianBaseChangeSecondTriangleCurryFamily l k))

/-- 同じ分解二単体の最初の辺は、既存の二回目の比較の元の底変換による前合成。 -/
lemma cocartesianBaseChangeSecondGlobalTriangleSimplex_first :
    ((ihom (CocartesianFibrationInfinity (nerve C))).obj
      (CatInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj (nerve A)))).δ (2 : Fin 3)
        (cocartesianBaseChangeSecondGlobalTriangleSimplex l k) =
      ((pre (cocartesianFibrationInfinityBaseChange (nerveMap k))).app
        (CatInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj (nerve A)))).app
          (Opposite.op ⦋1⦌) (cocartesianBaseChangeJointComparisonEdge l).edge := by
  rw [cocartesianBaseChangeSecondGlobalTriangleSimplex, ← stdSimplex.yonedaEquiv_δ_comp,
    ← transposeFunctorFamily_pre, cocartesianBaseChangeSecondTriangleCurryFamily_first,
    transposeFunctorFamily_comp, SSet.yonedaEquiv_comp,
    cocartesianBaseChangeJointComparisonEdge_yoneda]

/-- 同じ分解二単体の次の辺は、既存の元の結合比較辺そのもの。 -/
lemma cocartesianBaseChangeSecondGlobalTriangleSimplex_second :
    ((ihom (CocartesianFibrationInfinity (nerve C))).obj
      (CatInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj (nerve A)))).δ (0 : Fin 3)
        (cocartesianBaseChangeSecondGlobalTriangleSimplex l k) =
      (cocartesianBaseChangeAssociativityEdge l k).edge := by
  rw [cocartesianBaseChangeSecondGlobalTriangleSimplex, ← stdSimplex.yonedaEquiv_δ_comp,
    ← transposeFunctorFamily_pre, cocartesianBaseChangeSecondTriangleCurryFamily_second]
  exact cocartesianBaseChangeAssociativityEdge_yoneda l k

/-- 同じ分解二単体の長辺は、元の大域比較三角形の第二辺そのもの。 -/
lemma cocartesianBaseChangeSecondGlobalTriangleSimplex_long :
    ((ihom (CocartesianFibrationInfinity (nerve C))).obj
      (CatInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj (nerve A)))).δ (1 : Fin 3)
        (cocartesianBaseChangeSecondGlobalTriangleSimplex l k) =
      ((ihom (CocartesianFibrationInfinity (nerve C))).obj
        (CatInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj (nerve A)))).δ (0 : Fin 3)
          (cocartesianBaseChangeGlobalTriangleSimplex l k) := by
  rw [cocartesianBaseChangeSecondGlobalTriangleSimplex, ← stdSimplex.yonedaEquiv_δ_comp,
    ← transposeFunctorFamily_pre, cocartesianBaseChangeSecondTriangleCurryFamily_long,
    transposeFunctorFamily_pre, stdSimplex.yonedaEquiv_δ_comp]
  rfl

end SerrePositivity.InfinityCategories
