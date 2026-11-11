module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FiberwisePullbackComparisonApex
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.SpecifiedApexConeRestrictions

/-!
概要：一般 filtered 底上の元の引き戻し全空間の Kan 模型を native な極限錐の頂点にする。
方針：元の比較辺の可逆円柱で、既存の元の cospan 上の極限錐を頂点輸送する。
規約：元の図式・比較辺・全錐のホモトピーを保持する。
使われ方：一般 coherent filtered 余極限と引き戻しの交換の native な界面。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
variable {E D H B : SSet.{u}} [Quasicategory B] [IsFilteredInfinity B]
  (p : H ⟶ B) [LeftFibration p] (f : E ⟶ H) (g : D ⟶ H)
  [LeftFibration (f ≫ p)] [LeftFibration (g ≫ p)]

/-- 概要：元の比較辺を全頂点円柱として保持する、元の cospan 上の極限錐輸送。
方針：指定頂点輸送を実際の Kan 比較へ適用する。
規約：図式上の全円柱は定値。使われ方：元の三射影との比較のための全錐。 -/
def fiberwisePullbackNativeConeTransport :
    SpecifiedApexLimitConeTransport
      (intervalPullbackCone (continuousKanMap f) (continuousKanMap g))
      (SSet.yonedaEquiv.symm (coherentNerveVertex (fiberwisePullbackTotalKanObject p f g)))
      (fiberwisePullbackComparisonApexPrism p f g) :=
  specifiedApexLimitConeTransport _ (intervalPullbackCone_isLimit _ _) _ _
    (fiberwisePullbackComparisonApexPrism_zero p f g) (by
      rw [fiberwisePullbackComparisonApexPrism_one]
      apply SSet.yonedaEquiv.injective
      change coherentNerveVertex (fiberwisePullbackTargetKanObject f g) =
        (intervalPullbackCone (continuousKanMap f) (continuousKanMap g)).vertex
      rw [intervalPullbackCone_vertex, spaceInfinityVertex_eq_coherent]
      rfl)
    (fiberwisePullbackComparisonApexPrism_vertical_isInvertible p f g)

/-- 概要：元の引き戻し全空間の Kan 模型を頂点に持つ、三 Kan 全空間の cospan 上の錐。
方針：元の比較辺に沿って輸送した錐を取る。
規約：全図式は元のまま。使われ方：filtered 引き戻し交換の native な極限。 -/
def fiberwisePullbackNativeCone : JoinCone (kanDiagramCoherentNerve
    (kanPullbackDiagram (continuousKanMap f) (continuousKanMap g))) :=
  (fiberwisePullbackNativeConeTransport p f g).cone

/-- 概要：全空間 Kan 模型を頂点とする元の錐は native な極限錐。
方針：元の比較による可逆全錐輸送。規約：図式は元の二射。使われ方：交換の普遍性。 -/
lemma fiberwisePullbackNativeCone_isLimit : IsLimitCone (fiberwisePullbackNativeCone p f g) :=
  (fiberwisePullbackNativeConeTransport p f g).isLimit

/-- 概要：輸送後の頂点の射は元の引き戻し全空間の Kan 模型の指定点。
方針：頂点輸送の厳密な始点。規約：射の等式。使われ方：単位と三射影の照合。 -/
lemma fiberwisePullbackNativeCone_apex :
    joinInl _ _ ≫ (fiberwisePullbackNativeCone p f g).val =
      SSet.yonedaEquiv.symm (coherentNerveVertex (fiberwisePullbackTotalKanObject p f g)) :=
  (fiberwisePullbackNativeConeTransport p f g).apex_eq

/-- 概要：元の native 極限錐の頂点は元の引き戻し全空間の Kan 対象。
方針：頂点の射を Yoneda で評価。規約：厳密な頂点等式。使われ方：余極限頂点との比較。 -/
lemma fiberwisePullbackNativeCone_vertex :
    (fiberwisePullbackNativeCone p f g).vertex =
      spaceInfinityVertex (fiberwisePullbackTotalKanObject p f g) := by
  rw [spaceInfinityVertex_eq_coherent]
  change SSet.yonedaEquiv (joinInl _ _ ≫ (fiberwisePullbackNativeCone p f g).val) = _
  rw [fiberwisePullbackNativeCone_apex]
  exact SSet.yonedaEquiv.apply_symm_apply _

end SerrePositivity.InfinityCategories.F2
