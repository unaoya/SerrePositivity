module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictBarNormalizedFunctor

/-!
概要：元の正規化射影と指定全複体同型を、全図式・全射のD(A)評価比較へ運ぶ。
方針：同じ自然変換の成分の擬同型性から全関手同型を作り、逆と合成を取る。
規約：逆は全関手同型の逆として選ぶ。対象ごとの逆を自然な族と仮定しない。
使われ方：3b-3 R6、正規化barと元の単体的置換の全族比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison

variable (A : Type u) [CommRing A] (J : Type) [SmallCategory J]

/-- 元の正規化射影による、同じ一点評価後の全関手同型。 -/
def strictBarNormalizationDerivedIso :
    FunctorIso
      (nerveMap (strictBarUnnormalizedFunctor A J ⋙ moduleEvaluation A PUnit.{1} PUnit.unit) ≫
        complexDerivedEvaluation A)
      (nerveMap (strictBarNormalizedFunctor A J ⋙ moduleEvaluation A PUnit.{1} PUnit.unit) ≫
        complexDerivedEvaluation A) :=
  complexDerivedNatTransIso A
    (Functor.whiskerRight (strictBarNormalizationNatTrans A J)
      (moduleEvaluation A PUnit.{1} PUnit.unit)) (fun F =>
        inferInstanceAs (QuasiIso ((moduleEvaluation A PUnit.{1} PUnit.unit).map
          ((strictBarNormalizationNatTrans A J).app F))))

/-- 元の指定全複体同型による、非正規化barの同じ全関手比較。 -/
def strictBarUnnormalizedTotalDerivedIso :
    FunctorIso
      (nerveMap (strictBarUnnormalizedFunctor A J ⋙ moduleEvaluation A PUnit.{1} PUnit.unit) ≫
        complexDerivedEvaluation A)
      (nerveMap (strictBarTotalComplexFunctor A J) ≫ complexDerivedEvaluation A) :=
  complexDerivedNatTransIso A (strictBarUnnormalizedTotalIso A J).hom
    (fun F => inferInstanceAs (QuasiIso (smallStrictBarTotalPointIso A F).hom))

/-- 元の正規化射影と同じ指定全複体比較の合成による、全パラメーターの比較。 -/
def strictBarNormalizedTotalDerivedIso :
    FunctorIso
      (nerveMap (strictBarNormalizedFunctor A J ⋙ moduleEvaluation A PUnit.{1} PUnit.unit) ≫
        complexDerivedEvaluation A)
      (nerveMap (strictBarTotalComplexFunctor A J) ≫ complexDerivedEvaluation A) :=
  (strictBarNormalizationDerivedIso A J).symm ≪≫ strictBarUnnormalizedTotalDerivedIso A J

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
