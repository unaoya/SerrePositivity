module

public import SerrePositivity.HomotopicalAlgebra.Diagram.BousfieldKanFrameAugmentation
public import SerrePositivity.HomotopicalAlgebra.Diagram.BousfieldKanRealizationHom

/-!
概要：指定増大射による前合成の、実現Hom同型の下での全単体の式。
方針：同じ随伴の自然性と合成随伴の転置を使う。
使われ方：HTT 4.2.4.4、RR02(a)の実比較射の照合。
規約：元の増大射を固定し、弱同値性は仮定しない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe w u
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
namespace SerrePositivity.DiagramModel.FrameWeightRealization
variable (K : Type w) [SmallCategory K]
  {C : Type u} [Category.{w} C] [HasColimitsOfSize.{w, w} C]
  (A : K ⥤ SimplexCategory ⥤ C) (Q : SimplexCategory ⥤ C)
  (e : A ⟶ (Functor.const K).obj Q)

/-- 増大射との合成の指定転置は、元の余錐の転置の後合成。 -/
lemma bousfieldKanFrameAugmentation_homEquiv (n : SimplexCategory) (Y : C)
    (f : Q.obj n ⟶ Y) :
    (adjunction K A).homEquiv _ Y ((bousfieldKanFrameAugmentation K A Q e).app n ≫ f) =
      bousfieldKanCoconeParameter K A Q e n ≫ (hom K A).map f := by
  rw [Adjunction.homEquiv_naturality_right]
  exact congrArg (fun a => a ≫ (hom K A).map f)
    (((adjunction K A).homEquiv _ _).apply_symm_apply _)

/-- Hom同型の下で、増大射による前合成を全単体で評価する。 -/
lemma bousfieldKanAugmentationHom_app (Y : C) (n : SimplexCategoryᵒᵖ)
    (f : Q.obj n.unop ⟶ Y) :
    (((bousfieldKanRealizationHomIso K A).hom.app Y).app n)
        ((bousfieldKanFrameAugmentation K A Q e).app n.unop ≫ f) =
      SSet.yonedaEquiv ((weightedSectionsAdjunction (bousfieldKanWeight Kᵒᵖ)).homEquiv _ _
        (bousfieldKanCoconeParameter K A Q e n.unop ≫ (hom K A).map f)) := by
  rw [bousfieldKanRealizationHomIso_hom_app]
  have h := congrArg (fun h => h (SSet.stdSimplex.obj n.unop) Y
      ((bousfieldKanFrameAugmentation K A Q e).app n.unop ≫ f))
    (Adjunction.comp_homEquiv (weightedSectionsAdjunction (bousfieldKanWeight Kᵒᵖ))
      (adjunction K A))
  exact (congrArg SSet.yonedaEquiv h).trans
    (congrArg (fun a => SSet.yonedaEquiv
      ((weightedSectionsAdjunction (bousfieldKanWeight Kᵒᵖ)).homEquiv _ _ a))
        (bousfieldKanFrameAugmentation_homEquiv K A Q e n.unop Y f))

end SerrePositivity.DiagramModel.FrameWeightRealization
