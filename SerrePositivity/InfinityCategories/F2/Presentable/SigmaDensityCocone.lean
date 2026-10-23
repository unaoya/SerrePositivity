module

public import SerrePositivity.InfinityCategories.F2.Presentable.SigmaYonedaInfinity
public import SerrePositivity.InfinityCategories.HomotopyLimits.FullSubcomplexCoconeLift
public import SerrePositivity.InfinityCategories.HomotopyLimits.FullSubcomplexColimitReflection
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.PresheafDensity
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FunctorCoconeReindex

/-!
概要：元の前層密度余錐を、元の指定 P_Σ 対象を頂点とする内部余極限へ制限する。
方針：元の小さい元の圏・同じ射影・Yoneda 因子化を使い、全余錐を持ち上げる。
規約：添字の sifted 性は別工程。元の図式・頂点・全余錐を保持する。
使われ方：P-1 g の sifted 生成と、元の Yoneda への左 Kan 延長の入力。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
variable {C : SSet.{u}} [Quasicategory C]
  (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u})

/-- 元の小さい元の圏上の、元の P_Σ Yoneda に値を取る全図式。 -/
def sigmaElementsYonedaDiagram :
    (SSet.uliftFunctor.{u + 1, u}).obj (smallRightUnstraightening F) ⟶
      SigmaPresheafInfinity C :=
  (SSet.uliftFunctor.{u + 1, u}).map (smallRightUnstraighteningProjection F) ≫
    sigmaYonedaInfinityMap C

/-- 同じ生成図式の包含は元の前層の密度図式そのもの。 -/
lemma sigmaElementsYonedaDiagram_inclusion :
    sigmaElementsYonedaDiagram F ≫ sigmaPresheafInfinityInclusion C =
      F2.Ind.presheafElementsYonedaDiagram F := by
  rw [sigmaElementsYonedaDiagram, Category.assoc, sigmaYonedaInfinityMap_inclusion]
  rfl

/-- 同じ密度全余錐を、元の内部図式の包含像上の余錐として読む。 -/
def sigmaDensityAmbientCocone :
    JoinCocone (sigmaElementsYonedaDiagram F ≫ sigmaPresheafInfinityInclusion C) :=
  ⟨(F2.Ind.presheafDensityCocone F).val, by
    rw [sigmaElementsYonedaDiagram_inclusion]
    exact (F2.Ind.presheafDensityCocone F).property⟩

/-- 元の周囲の密度余錐は、元の F 自身を指定頂点とする。 -/
lemma sigmaDensityAmbientCocone_vertex :
    (sigmaDensityAmbientCocone F).vertex = functorVertex F :=
  F2.Ind.presheafDensityCocone_vertex F

/-- 同じ周囲の密度余錐は元の全図式の余極限。 -/
lemma sigmaDensityAmbientCocone_isColimit : IsColimitCone (sigmaDensityAmbientCocone F) := by
  apply (F2.isColimitCone_iff_of_coconeMap_eq (sigmaDensityAmbientCocone F)
    (F2.Ind.presheafDensityCocone F) rfl).mpr
  exact F2.Ind.presheafDensityCocone_isColimit F

/-- 元の指定 P_Σ 対象への、元の小さい元の圏による内部の全密度余錐。 -/
def sigmaDensityCocone (hF : IsSigmaPresheaf (functorVertex F)) :
    JoinCocone (sigmaElementsYonedaDiagram F) :=
  fullSubcomplexCoconeLift IsSigmaPresheaf (sigmaElementsYonedaDiagram F)
    (sigmaDensityAmbientCocone F) ((sigmaDensityAmbientCocone_vertex F).symm ▸ hF)

/-- 内部の全余錐の包含は元の前層密度全余錐を厳密に回収する。 -/
lemma sigmaDensityCocone_inclusion (hF : IsSigmaPresheaf (functorVertex F)) :
    F1B.kanPostcomposeCocone (sigmaPresheafInfinityInclusion C) (sigmaDensityCocone F hF) =
      sigmaDensityAmbientCocone F :=
  fullSubcomplexCoconeLift_inclusion _ _ _ _

/-- 元の P_Σ 密度全余錐は同じ内部図式の余極限。 -/
lemma sigmaDensityCocone_isColimit (hF : IsSigmaPresheaf (functorVertex F)) :
    IsColimitCone (sigmaDensityCocone F hF) := by
  apply isColimitCone_of_fullSubcomplex (IsSigmaPresheaf (C := C))
  change IsColimitCone (F1B.kanPostcomposeCocone
    (sigmaPresheafInfinityInclusion C) (sigmaDensityCocone F hF))
  rw [sigmaDensityCocone_inclusion]
  exact sigmaDensityAmbientCocone_isColimit F

end SerrePositivity.InfinityCategories.HomotopyLimits
