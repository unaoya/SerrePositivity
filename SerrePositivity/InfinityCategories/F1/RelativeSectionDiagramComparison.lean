module

public import SerrePositivity.InfinityCategories.F1.RelativeSectionDiagram
public import SerrePositivity.InfinityCategories.F1.StrictDiagramPostcomposition
public import SerrePositivity.InfinityCategories.F1.StrictDiagramPrecomposition

/-!
概要：底上の定義域図式の自然変換を、全相対切断図式の豊穣自然な比較へ送る。
方針：相対前合成の合成則と全高次 Hom に対する自然性を使う。
規約：単体集合の底にも添字圏にも追加仮定を課さない。
使われ方：単体の切断と under の切断を図式全体で比較する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories

/-- 概要：定義域図式の自然変換は各 left fibration の切断図式を反変に比較する。
方針：各成分を相対前合成とし、自然性は合成則へ戻す。
規約：全ての添字の射に関して厳密に自然。
使われ方：共同切断の図式全体の比較の通常の成分。 -/
def relativeSectionDiagramComparison {B : SSet.{u}} {J : Type u} [Category.{u} J]
    {A D : Jᵒᵖ ⥤ Over B} (η : A ⟶ D) (p : LeftFibrationObject B) :
    (relativeSectionEnrichedDiagram D).evaluate p ⋙ kanObjectForget ⟶
      (relativeSectionEnrichedDiagram A).evaluate p ⋙ kanObjectForget where
  app j := relativeFunctorOverPre p.val.hom (η.app (Opposite.op j))
  naturality i j f := by
    change relativeFunctorOverPre p.val.hom (D.map f.op) ≫
      relativeFunctorOverPre p.val.hom (η.app (Opposite.op j)) =
      relativeFunctorOverPre p.val.hom (η.app (Opposite.op i)) ≫
        relativeFunctorOverPre p.val.hom (A.map f.op)
    rw [← relativeFunctorOverPre_comp, ← relativeFunctorOverPre_comp, η.naturality]

/-- 概要：定義域の比較は全 left fibrations の全高次 Hom について豊穣自然。
方針：変換空間の各成分で相対前合成の豊穣自然性を評価する。
規約：頂点に制限せず写像空間そのものの射の等式。
使われ方：全対象を同時に動かす図式の比較の実現。 -/
lemma relativeSectionDiagramComparison_enrichedNaturality
    {B : SSet.{u}} {J : Type u} [Category.{u} J]
    {A D : Jᵒᵖ ⥤ Over B} (η : A ⟶ D) (p q : LeftFibrationObject B) :
    (relativeSectionEnrichedDiagram D).mappingSpaceMap p q ≫
      strictDiagramMappingPost (relativeSectionDiagramComparison η q)
        ((relativeSectionEnrichedDiagram D).evaluate p ⋙ kanObjectForget) =
    (relativeSectionEnrichedDiagram A).mappingSpaceMap p q ≫
      strictDiagramMappingPre (relativeSectionDiagramComparison η p)
        ((relativeSectionEnrichedDiagram A).evaluate q ⋙ kanObjectForget) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro θ
  apply Subtype.ext
  funext j
  apply CategoryTheory.Functor.functorHom_ext
  intro k α
  apply ConcreteCategory.hom_ext
  intro x
  exact (kanEnrichedComparison_app (relativeFunctorOverPreComparison
    (η.app (Opposite.op j))) p q θ α x).symm

/-- 概要：定義域の比較の豊穣成分は添字の射と厳密に可換。
方針：相対切断図式の通常の自然性を全対象で同時に使う。
規約：Kan 値豊穣比較としての等式。
使われ方：二つの比較図式を一つの添字図式へ束ねる。 -/
lemma relativeSectionDiagramComparison_indexNaturality
    {B : SSet.{u}} {J : Type u} [Category.{u} J]
    {A D : Jᵒᵖ ⥤ Over B} (η : A ⟶ D) {i j : J} (f : i ⟶ j) :
    ((relativeSectionEnrichedDiagram D).map f).trans
      (relativeFunctorOverPreComparison (η.app (Opposite.op j))) =
    (relativeFunctorOverPreComparison (η.app (Opposite.op i))).trans
      ((relativeSectionEnrichedDiagram A).map f) := by
  apply Subtype.ext
  funext p
  exact (relativeSectionDiagramComparison η p).naturality f

end SerrePositivity.InfinityCategories
