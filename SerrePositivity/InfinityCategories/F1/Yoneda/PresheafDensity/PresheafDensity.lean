module

public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.PresheafDensityEvaluationColimit
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafPointwiseColimits

/-!
概要：任意の前層を、元の小さい元の圏上の表現可能前層の余極限として実現する。
方針：元の F を頂点とする指定密度余錐の各評価の余極限性を、前層の評価で検出する。
規約：図式・余錐・指定前層を構成済みの同じものに固定する。
使われ方：HTT 5.1.5.3、Indκ の生成表示と関手の延長の密度入力。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {C : SSet.{u}} [Quasicategory C]
  (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u})

/-- 元の前層 F を指定頂点とする、同じ小さい表現可能図式の密度余錐は余極限。 -/
lemma presheafDensityCocone_isColimit : IsColimitCone (presheafDensityCocone F) :=
  presheafInfinity_isColimit_of_evaluation (presheafElementsYonedaDiagram F)
    (presheafDensityCocone F) (presheafDensityEvaluationCocone_isColimit F)

/-- 任意の前層 F は、元の小さい元の圏上の表現可能前層の同じ図式の余極限。 -/
lemma presheafDensityPresentation :
    ∃ c : JoinCocone (presheafElementsYonedaDiagram F),
      c.vertex = functorVertex F ∧ IsColimitCone c :=
  ⟨presheafDensityCocone F, presheafDensityCocone_vertex F, presheafDensityCocone_isColimit F⟩

end SerrePositivity.InfinityCategories.F2.Ind
