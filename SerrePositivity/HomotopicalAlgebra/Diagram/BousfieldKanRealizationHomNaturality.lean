module

public import SerrePositivity.HomotopicalAlgebra.Diagram.BousfieldKanParameterNaturality

/-!
概要：指定BK実現のHom同型はsource frameの射についても自然。
方針：合成随伴の転置の自然性を全次数のYoneda評価へ移す。
使われ方：HTT 4.2.4.4、RR02(a)のHom同型の全族の照合。
規約：標的の自然性は既存の自然同型に含まれ、source側をここで照合する。
-/

@[expose] public noncomputable section
universe w u
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
namespace SerrePositivity.DiagramModel.FrameWeightRealization
variable (K : Type w) [SmallCategory K]
  {C : Type u} [Category.{w} C] [HasColimitsOfSize.{w, w} C]

/-- Hom同型はsource frameの射の全族に対して可換。 -/
lemma bousfieldKanRealizationHomIso_source_naturality
    {A B : K ⥤ SimplexCategory ⥤ C} (a : A ⟶ B) :
    cosimplicialHomMap (Functor.whiskerLeft SSet.stdSimplex (bousfieldKanParameterMap K a)) ≫
        (bousfieldKanRealizationHomIso K A).hom =
      (bousfieldKanRealizationHomIso K B).hom ≫
        Functor.whiskerRight ((homFamily K).map a.op)
          (weightedSectionsFunctor (bousfieldKanWeight Kᵒᵖ)) := by
  apply NatTrans.ext
  funext Y
  apply NatTrans.ext
  funext n
  ext t
  change SSet.yonedaEquiv ((bousfieldKanParameterAdjunction K A).homEquiv _ Y
      ((bousfieldKanParameterMap K a).app _ ≫ t)) = _
  rw [bousfieldKanParameterHomEquiv_frame_naturality]
  exact SSet.yonedaEquiv_comp _ _

end SerrePositivity.DiagramModel.FrameWeightRealization
