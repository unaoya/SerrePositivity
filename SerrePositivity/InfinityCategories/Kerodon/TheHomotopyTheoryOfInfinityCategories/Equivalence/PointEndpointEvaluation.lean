module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.KanEquivalencePaths

/-!
概要：区間の端点による制限と一点の関手空間の評価の可換性。
方針：頂点評価の前合成自然性と一点の評価同型を使う。
規約：端点 j は除く面 j.rev の余面写像で表す。
使われ方：Kerodon 4.5.3.24（Tag 02VM）、7.5.4.6（Tag 03BB） の可逆 path の相対充填の閉構造による表示。

対応節は Kerodon 4.5（Tag 01DE）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence

/-- 概要：一点の関手空間への評価の逆射は標的の射について自然である。
方針：第二射影の curry の前後の合成自然性を使う。
規約：元の単体集合に充填性は要求しない。
使われ方：Kerodon 4.5.3.24（Tag 02VM） の相対内部 Hom の標的の pullback の同定。 -/
lemma pointFunctorEvaluationIso_inv_naturality {E B : SSet.{u}} (p : E ⟶ B) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.pointFunctorEvaluationIso E).inv ≫ (ihom (Δ[0] : SSet.{u})).map p =
      p ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.pointFunctorEvaluationIso B).inv := by
  change curry (snd (Δ[0] : SSet.{u}) E) ≫ (ihom (Δ[0] : SSet.{u})).map p =
    p ≫ curry (snd (Δ[0] : SSet.{u}) B)
  rw [← curry_natural_right, ← curry_natural_left]
  exact congrArg curry (whiskerLeft_snd (Δ[0] : SSet.{u}) p).symm

/-- 概要：区間関手を j 番目の頂点で評価する操作は対応する一点への制限に等しい。
方針：前合成した関手の頂点評価を像の頂点での評価へ移す。
規約：j.rev を除く面が頂点 j の包含。
使われ方：Kerodon 4.5.3.24（Tag 02VM）、7.5.4.6（Tag 03BB） の相対 path の内部 Hom の表示。 -/
lemma pointFunctorEvaluationIso_interval_pre (X : SSet.{u}) (j : Fin 2) :
    (pre (stdSimplex.δ j.rev : (Δ[0] : SSet.{u}) ⟶ Δ[1])).app X ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.pointFunctorEvaluationIso X).hom =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) (stdSimplex.obj₀Equiv.symm j) := by
  change (pre (stdSimplex.δ j.rev : (Δ[0] : SSet.{u}) ⟶ Δ[1])).app X ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 0) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.evaluateFunctorAt_pre]
  congr 1
  fin_cases j <;> rfl

/-- 概要：区間の j 番目の頂点の包含は anodyne。
方針：既存の区間の余面写像の anodyne 性を使う。
規約：区間の任意の端点を同じ命題で扱う。
使われ方：Kerodon 4.5.3.24（Tag 02VM） の Kan fibration の path の相対境界充填。 -/
lemma intervalEndpoint_anodyne (j : Fin 2) :
    anodyneExtensions (stdSimplex.δ j.rev : (Δ[0] : SSet.{u}) ⟶ Δ[1]) :=
  SerrePositivity.SimplicialModel.AnodyneHomotopy.delta_anodyne j.rev j
    (by fin_cases j <;> decide)

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
