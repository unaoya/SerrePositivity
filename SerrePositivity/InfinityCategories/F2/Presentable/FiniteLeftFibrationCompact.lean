module

public import SerrePositivity.InfinityCategories.F2.Presentable.FiniteRelativeHomAccessible
public import SerrePositivity.InfinityCategories.F2.Presentable.ContinuousLeftFibrationHomIso
public import SerrePositivity.InfinityCategories.F2.Presentable.RelativeHomModel
public import SerrePositivity.InfinityCategories.F2.Presentable.FiniteLeftFibrationFamily
public import SerrePositivity.InfinityCategories.F2.Compact.UniverseColimits

/-!
概要：有限底上模型の連続置換は、元の left fibration ∞ 圏で compact である。
方針：相対 Hom の全 filtered 保存を、元の大きい共変 Hom との全自然比較で輸送する。
規約：compact 性は既存の定義を使い、置換後の全空間の有限性は要求しない。
使われ方：一般の小さい底上の前層の小さい compact 生成族。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：相対 Hom の全 filtered 保存から、同じ left fibration 対象の compact 性を得る。
方針：元の共変 Hom への宇宙変更と全自然同型で同じ指定余錐像の保存を移す。
規約：元の小さい添字と元の指定余錐を保持する。
使われ方：有限底上模型の連続置換の compact 性の判定。 -/
lemma leftFibrationObject_isKappaCompact_of_homPreservation {B : SSet.{u}}
    {κ : Cardinal.{u}} (X : LeftFibrationObject B)
    (h : IsKappaAccessibleFunctor κ (leftFibrationCoherentEvaluation X.val)) :
    Compact.IsKappaCompact.{u, u + 1} κ (coherentNerveVertex X) := by
  intro I hI hFiltered D c hc
  have hm : IsColimitCone (mapJoinCocone
      ((SSet.uliftFunctor.{u + 2, u + 1}).map (leftFibrationCoherentEvaluation X.val) ≫
        Compact.spaceUniverseDiagram) (JoinCocone.ulift c)) := by
    rw [Compact.mapJoinCocone_universe_comp]
    exact Compact.spaceUniverseDiagram_map_isColimit (D ≫ leftFibrationCoherentEvaluation X.val)
      (mapJoinCocone (leftFibrationCoherentEvaluation X.val) c) (h I D c hc)
  exact hm.of_functorIso
    ((relativeHom_covariantModelIso X).precomp (JoinCocone.ulift c).val).symm

/-- 概要：任意の有限底上模型の元の連続置換は compact である。
方針：有限始域の相対 Hom 保存を元の単位の全関手同型で置換後へ移す。
規約：底は任意の小さい quasicategory、全空間の有限性は置換前だけに要求する。
使われ方：前層の小さい compact 生成圏の対象族。 -/
lemma finiteLeftFibrationReplacement_isCompact {B : SSet.{u}} [Quasicategory B]
    (A : Over B) [A.left.Finite] :
    Compact.IsKappaCompact.{u, u + 1} Cardinal.aleph0
      (coherentNerveVertex (continuousReplacementLeftFibrationObject A)) :=
  leftFibrationObject_isKappaCompact_of_homPreservation _
    ((finiteRelativeHom_isKappaAccessibleFunctor A).of_functorIso
      (continuousLeftFibrationHomIso A).symm)

/-- 概要：共通の小さい有限底上符号族の全頂点は compact である。
方針：各符号の実現の有限性を、同じ連続置換の compact 性へ渡す。
規約：対象族は元の宇宙 u、compact 性は元の ∞ 圏の定義で述べる。
使われ方：小さい compact 全部分生成圏の構成。 -/
lemma finiteLeftFibrationGeneratorVertex_isCompact {B : SSet.{u}} [Quasicategory B]
    (q : FiniteOverCode B) :
    Compact.IsKappaCompact.{u, u + 1} Cardinal.aleph0 (finiteLeftFibrationGeneratorVertex q) :=
  finiteLeftFibrationReplacement_isCompact q.realization

end SerrePositivity.InfinityCategories.F2.Presentable
