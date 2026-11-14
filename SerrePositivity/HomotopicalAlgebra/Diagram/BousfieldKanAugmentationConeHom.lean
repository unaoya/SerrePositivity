module

public import SerrePositivity.HomotopicalAlgebra.Diagram.BousfieldKanAugmentationHom

/-!
概要：BK実現の指定増大射のHomは、元のframe余錐からの重み付き錐比較と一致。
方針：全単体で指定随伴の転置を計算し、第二射影とYonedaの自然性を使う。
使われ方：HTT 4.2.4.4、RR02(a)の実比較射の照合。
規約：錐の脚は元の余錐のHomであることを明示する。極限性は仮定しない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe w u
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
namespace SerrePositivity.DiagramModel.FrameWeightRealization
variable (K : Type w) [SmallCategory K]
  {C : Type u} [Category.{w} C] [HasColimitsOfSize.{w, w} C]
  (A : K ⥤ SimplexCategory ⥤ C) (Q : SimplexCategory ⥤ C)
  (e : A ⟶ (Functor.const K).obj Q) (Y : C)
  (π : (Functor.const Kᵒᵖ).obj ((cosimplicialHom Q).obj Y) ⟶ (hom K A).obj Y)
  (hπ : ∀ k, π.app k = (cosimplicialHomMap (e.app k.unop)).app Y)

include hπ in
/-- 指定Hom同型の下で、元の増大射の前合成は同じ脚の錐比較そのもの。 -/
lemma bousfieldKanAugmentationHom_cone :
    (cosimplicialHomMap (bousfieldKanFrameAugmentation K A Q e)).app Y ≫
        (bousfieldKanRealizationHomIso K A).hom.app Y =
      weightedConeComparison (bousfieldKanWeight Kᵒᵖ)
        (⟨(cosimplicialHom Q).obj Y, π⟩ : Cone ((hom K A).obj Y)) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro f
  change (((bousfieldKanRealizationHomIso K A).hom.app Y).app n)
      ((bousfieldKanFrameAugmentation K A Q e).app n.unop ≫ f) = _
  rw [bousfieldKanAugmentationHom_app]
  have hy := SSet.yonedaEquiv_comp (SSet.yonedaEquiv.symm f)
    (weightedConeComparison (bousfieldKanWeight Kᵒᵖ)
      (⟨(cosimplicialHom Q).obj Y, π⟩ : Cone ((hom K A).obj Y)))
  rw [Equiv.apply_symm_apply] at hy
  refine Eq.trans ?_ hy
  apply congrArg SSet.yonedaEquiv
  simp only [weightedSectionsAdjunction, Adjunction.mkOfHomEquiv_homEquiv]
  change weightedSectionsLift (I := Kᵒᵖ) _ = SSet.yonedaEquiv.symm f ≫ weightedSectionsLift (I := Kᵒᵖ) _
  apply (weightedSectionsHomEquiv (bousfieldKanWeight Kᵒᵖ) ((hom K A).obj Y) (SSet.stdSimplex.obj n.unop)).injective
  change weightedSectionsUncurry (weightedSectionsLift (I := Kᵒᵖ) _) =
    weightedSectionsUncurry (SSet.yonedaEquiv.symm f ≫ weightedSectionsLift (I := Kᵒᵖ) _)
  rw [weightedSectionsUncurry_lift, weightedSectionsUncurry_precomp,
    weightedSectionsUncurry_lift]
  apply NatTrans.ext
  funext k
  change (snd _ _ ≫ SSet.yonedaEquiv.symm ((e.app k.unop).app n.unop)) ≫
      (cosimplicialHom (A.obj k.unop)).map f =
    (bousfieldKanWeight Kᵒᵖ).obj k ◁ SSet.yonedaEquiv.symm f ≫ snd _ _ ≫ π.app k
  rw [whiskerLeft_snd_assoc, Category.assoc, hπ]
  apply congrArg (fun a => snd ((bousfieldKanWeight Kᵒᵖ).obj k)
    (SSet.stdSimplex.obj n.unop) ≫ a)
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp, SSet.yonedaEquiv_comp,
    Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  rfl

end SerrePositivity.DiagramModel.FrameWeightRealization
