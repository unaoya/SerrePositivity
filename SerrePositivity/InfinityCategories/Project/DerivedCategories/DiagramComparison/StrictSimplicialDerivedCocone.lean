module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.SpecifiedProjectiveCocone
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.StrictSimplicialNativeColimit
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.StrictSimplicialVertexLeg

/-!
# 元の直和実現を頂点とする D(A) の指定余錐

## 概要
射影的複体のstrict図式の計算済み余錐を既存D(A)へ移す。
## 方針
同じ比較の可逆性で実現の射影性を戻し、同じ全余錐を既存同値へ送る。
## 規約
D(A)の頂点は同じ実現の半自由代表。図式ごとの版である。
## 使われ方
HA 1.2.4、HTT 4.2.4.1。IS-W2 §8 の指定実現余錐。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Opposite SSet SerrePositivity.DifferentialGraded
open scoped _root_.Simplicial
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
open SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
open SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
variable (A : Type u) [CommRing A] (F : SimplicialObject (ModuleCategory A PUnit.{1}))
  (hF : ∀ j, moduleHomotopicallyProjective A PUnit.{1} (F.obj j))

include hF in
/-- 元の同じ実現は射影的。正規化barへ取り替えた主張ではない。 -/
theorem strictSimplicialRealization_projective :
    moduleHomotopicallyProjective A PUnit.{1}
      (ForgetEnrichment.of (Complex A) (strictSimplicialRealizationModule A F)) := by
  apply moduleProjective_of_isIso_onHomotopy A PUnit.{1} (strictSimplicialBarRealizationHom A F)
    (strictSimplicialBarRealizationHom_isIso_onHomotopy A F)
  apply dgCoherentBarNormalizedModule_homotopicallyProjective
  intro s
  exact hF (s.down.obj 0)

/-- 同じ元の余錐を射影的部分圏へ戻す。 -/
def strictSimplicialProjectiveCocone :=
  specifiedProjectiveCocone A PUnit.{1} (strictSimplicialBarRealizationCocone A F)
    (fun s => hF (s.down.down.obj 0)) (by
      rw [strictSimplicialBarRealizationCocone_vertex]
      exact strictSimplicialRealization_projective A F hF)

/-- 射影的複体模型での元のstrict図式を、既存D(A)へ送った同じ図式。 -/
def strictSimplicialDerivedDiagram :=
  specifiedProjectiveDiagram A PUnit.{1}
    (F := smallStrictBarDiagram A F) (fun s => hF (s.down.down.obj 0)) ≫
    (projectivePointEquivalence A).hom

/-- 元の同じ実現の半自由代表を頂点に持つ、D(A)の実際の指定余錐。 -/
def strictSimplicialDerivedCocone : JoinCocone (strictSimplicialDerivedDiagram A F hF) :=
  mapJoinCocone (projectivePointEquivalence A).hom (strictSimplicialProjectiveCocone A F hF)

/-- この同じ指定余錐はD(A)で余極限である。 -/
theorem strictSimplicialDerivedCocone_isColimit :
    IsColimitCone (strictSimplicialDerivedCocone A F hF) := by
  apply (equivalence_isColimitCone_iff (projectivePointEquivalence A).isQCatEquivalence _).mp
  apply specifiedProjectiveCocone_isColimit
  exact strictSimplicialBarRealizationCocone_isColimit A F

/-- 射影的模型へ戻した全余錐は、包含で元の同じ計算済み余錐になる。 -/
theorem strictSimplicialProjectiveCocone_image :
    (strictSimplicialProjectiveCocone A F hF).val ≫
      SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
        (dgFullSubcategoryInclusion A (RightModule A PUnit.{1})
          (dgModuleProjectiveProperty A PUnit.{1})) = (strictSimplicialBarRealizationCocone A F).val :=
  specifiedProjectiveCocone_image A PUnit.{1} _ _ _

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
