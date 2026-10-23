module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.HomIntervalEvaluation
public import SerrePositivity.InfinityCategories.F1.EquivalenceLiftingPullback

/-!
概要：実際の分類先の Hom を標準の成分 Hom 比較に沿って引き戻す。
方針：元の作用と成分評価の可換性で比較射を作り、同値持ち上げ性で射影の同値を証明する。
規約：比較射の第一成分は元の Hom 作用そのもの。
使われ方：一次元の元の Hom 作用の同値性を、成分固定の比較へ帰着する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories

attribute [local instance] cocartesianHomIntervalEvaluation_fibration

variable {C : Type u} [Category.{u} C] (F G : CocartesianTransportDiagramCategory C) (c : C)

/-- 元の全 Hom の core の一成分評価を、分類先と同じ宇宙へ持ち上げる。 -/
def cocartesianHomSourceComponent :
    (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom F G) ⟶
      (SSet.uliftFunctor.{u + 1, u}).obj
        (SimplicialCategory.sHom (cocartesianTransportDiagramValue F c)
          (cocartesianTransportDiagramValue G c)) :=
  (SSet.uliftFunctor.{u + 1, u}).map
    ((cocartesianTransportDiagramEvaluationEnriched c).map F G)

/-- 実際の分類先の Hom を、元の成分 Hom と同じ底を持つように引き戻す。 -/
def cocartesianHomComponentSpace : SSet.{u + 1} :=
  pullback (cocartesianHomIntervalEvaluation F G c)
    (coherentHomIntervalComparison
      (cocartesianTransportDiagramValue F c) (cocartesianTransportDiagramValue G c))

/-- 元の全 Hom 作用と元の成分評価を、同じ底を持つ比較として束ねる。 -/
def cocartesianHomComponentComparison :
    (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom F G) ⟶
      cocartesianHomComponentSpace F G c :=
  pullback.lift (cocartesianTransportDiagramHomInterval F G)
    ((SSet.uliftFunctor.{u + 1, u}).map
      ((cocartesianTransportDiagramEvaluationEnriched c).map F G))
    (cocartesianTransportDiagramHomInterval_evaluation F G c)

/-- 同じ底への比較の第一射影は、元の分類の全 Hom 作用そのもの。 -/
lemma cocartesianHomComponentComparison_fst :
    cocartesianHomComponentComparison F G c ≫ pullback.fst _ _ =
      cocartesianTransportDiagramHomInterval F G := pullback.lift_fst ..

/-- 同じ底への比較の第二射影は、元の全高次の成分評価。 -/
lemma cocartesianHomComponentComparison_snd :
    cocartesianHomComponentComparison F G c ≫ pullback.snd _ _ =
      (SSet.uliftFunctor.{u + 1, u}).map
        ((cocartesianTransportDiagramEvaluationEnriched c).map F G) := pullback.lift_snd ..

/-- 同じ底への引き戻しから元の分類先への射影は同値。 -/
lemma cocartesianHomComponentSpace_fst_isQCatEquivalence :
    IsQCatEquivalence
      (pullback.fst (cocartesianHomIntervalEvaluation F G c)
        (coherentHomIntervalComparison
          (cocartesianTransportDiagramValue F c) (cocartesianTransportDiagramValue G c))) := by
  let p := cocartesianHomIntervalEvaluation F G c
  let e := coherentHomIntervalComparison
    (cocartesianTransportDiagramValue F c) (cocartesianTransportDiagramValue G c)
  have he₀ := coherentHomIntervalComparison_isQCatEquivalence
    (cocartesianTransportDiagramValue F c) (cocartesianTransportDiagramValue G c)
  have he := he₀.pullback_snd_isPrecompositionEquivalence_of_kanEquivalenceLifting p
    (kanEquivalenceLifting_cocartesianHomIntervalEvaluation F G c)
  have h := (qCatEquivalenceOfIso (pullbackSymmetry p e)).isQCatEquivalence.comp
    he.isQCatEquivalence
  change IsQCatEquivalence ((pullbackSymmetry p e).hom ≫ pullback.snd e p) at h
  simpa only [pullbackSymmetry_hom_comp_snd] using h

end SerrePositivity.InfinityCategories
