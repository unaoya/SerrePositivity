module

public import SerrePositivity.InfinityCategories.F2.Ind.SingleFilteredPresentation
public import SerrePositivity.InfinityCategories.F2.Ind.KappaColimits
public import SerrePositivity.InfinityCategories.HomotopyLimits.CoherentCoconeTransport

/-!
概要：元の前層の小さい元の圏上の密度余錐を、同じ Indκ の全余錐として持ち上げる。
方針：元の Yoneda の因子化と全部分余錐の持ち上げを使う。
規約：図式・元の全余錐・前層頂点を包含後に厳密に回収する。
使われ方：κ-filtered 保存関手の値を元の C 上の制限から回収する密度入力。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
open HomotopyLimits
variable (κ : Cardinal.{u}) {C : SSet.{u}} [Quasicategory C]
  (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u})

/-- 同じ元の圏から Indκ 内の Yoneda 像への、元の射影による図式。 -/
def indDensityDiagram :
    (SSet.uliftFunctor.{u + 1, u}).obj (smallRightUnstraightening F) ⟶ IndInfinity κ C :=
  (SSet.uliftFunctor.{u + 1, u}).map (smallRightUnstraighteningProjection F) ≫ indYoneda κ C

lemma indDensityDiagram_inclusion :
    indDensityDiagram κ F ≫ indInclusionPresheaf κ C = presheafElementsYonedaDiagram F := by
  rw [indDensityDiagram, Category.assoc, indYoneda_inclusion]
  rfl

/-- 元の全密度余錐を、同じ持ち上げ図式の包含上で型を揃えて読む。 -/
def indDensityAmbientCocone :
    JoinCocone (indDensityDiagram κ F ≫ indInclusionPresheaf κ C) :=
  coherentCoconeOfDiagramEq (indDensityDiagram_inclusion κ F).symm (presheafDensityCocone F)

lemma indDensityAmbientCocone_vertex :
    (indDensityAmbientCocone κ F).vertex = functorVertex F :=
  (coherentCoconeOfDiagramEq_vertex _ _).trans (presheafDensityCocone_vertex F)

/-- 元の Indκ 頂点を持つ密度余錐そのものを、Indκ 内へ持ち上げる。 -/
def indDensityCocone (hF : IsIndVertex κ C (functorVertex F)) :
    JoinCocone (indDensityDiagram κ F) :=
  fullCoconeLift (IsIndVertex κ C) (indDensityDiagram κ F) (indDensityAmbientCocone κ F)
    ((indDensityAmbientCocone_vertex κ F).symm ▸ hF)

/-- 同じ包含後の全余錐は、元の密度余錐そのもの。 -/
lemma indDensityCocone_inclusion (hF : IsIndVertex κ C (functorVertex F)) :
    mapJoinCocone (indInclusionPresheaf κ C) (indDensityCocone κ F hF) =
      indDensityAmbientCocone κ F := fullCoconeLift_inclusion _ _ _ _

lemma indDensityCocone_isColimit (hF : IsIndVertex κ C (functorVertex F)) :
    IsColimitCone (indDensityCocone κ F hF) := by
  apply fullCoconeLift_isColimit
  exact (coherentCoconeOfDiagramEq_isColimit_iff _ _).mp (presheafDensityCocone_isColimit F)

/-- 同じ密度余錐の Indκ 頂点を前層へ戻すと、元の F 自体を厳密に回収する。 -/
lemma indDensityCocone_vertex (hF : IsIndVertex κ C (functorVertex F)) :
    (indInclusionPresheaf κ C).app (Opposite.op ⦋0⦌) (indDensityCocone κ F hF).vertex =
      functorVertex F := by
  have h := congrArg JoinCocone.vertex (indDensityCocone_inclusion κ F hF)
  exact h.trans (indDensityAmbientCocone_vertex κ F)

end SerrePositivity.InfinityCategories.F2.Ind
