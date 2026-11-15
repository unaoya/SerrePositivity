module

public import SerrePositivity.HomotopicalAlgebra.Diagram.FrameBousfieldKanAugmentation
public import SerrePositivity.HomotopicalAlgebra.Diagram.ConstantWeightNaturality

/-!
概要：指定BK増大射はframeの係数移送と両立する。
方針：指定随伴で転置し、零重みと元の次数零余錐の移送を照合する。
使われ方：HTT 4.2.4.4、RR02(a)の元の自由増大射への接続。
規約：元の余錐を次数零の射で前合成するだけで、脚を選び直さない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe w u
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
namespace SerrePositivity.DiagramModel.FrameWeightRealization
variable {K : Type w} [SmallCategory K]
  {C : Type u} [Category.{w} C] [HasColimitsOfSize.{w, w} C]
  {A B : K ⥤ SimplexCategory ⥤ C} (a : A ⟶ B)
  (c : Cocone (ConstantWeightHom.degree K B (SimplexCategory.mk 0)))

lemma bousfieldKanAugmentation_frame_naturality :
    (map K a).app (bousfieldKanWeight Kᵒᵖ) ≫ bousfieldKanAugmentation B c =
      bousfieldKanAugmentation A
        ((Cocone.precompose (ConstantWeightRealization.degreeMap K a (SimplexCategory.mk 0))).obj c) := by
  have h : (ConstantWeightHom.homEquiv K B (SimplexCategory.mk 0) c.pt).symm c.ι ≫
      ((homFamily K).map a.op).app c.pt =
      (ConstantWeightHom.homEquiv K A (SimplexCategory.mk 0) c.pt).symm
        (ConstantWeightRealization.degreeMap K a (SimplexCategory.mk 0) ≫ c.ι) := by
    apply (ConstantWeightHom.homEquiv K A (SimplexCategory.mk 0) c.pt).injective
    rw [ConstantWeightRealization.weightHomEquiv_frame_naturality,
      Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  apply ((adjunction K A).homEquiv _ _).injective
  rw [homEquiv_frame_naturality, bousfieldKanAugmentation_homEquiv, Category.assoc, h]
  exact ((adjunction K A).homEquiv _ _).apply_symm_apply _ |>.symm

end SerrePositivity.DiagramModel.FrameWeightRealization
