module

public import SerrePositivity.HomotopicalAlgebra.Diagram.ElementsCopowerIsoEvaluation
public import SerrePositivity.HomotopicalAlgebra.Diagram.FrameBousfieldKanAugmentation

/-!
概要：余積frameの指定余錐を要素圏へ移し、元のBK増大射を照合する。
方針：余積の挿入と単体的Yonedaの自然性を使い、指定Hom同値で転置する。
使われ方：HTT 4.2.4.4、RR02(a)の評価同型と元の増大射の一致。
規約：要素圏の余錐の脚は元の脚への余積挿入である。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe w u
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.InfinityCategories.Project.FilteredExchange
open SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
namespace SerrePositivity.DiagramModel.ElementsCopower
variable {K : Type w} [SmallCategory K]
  {C : Type u} [Category.{w} C] [HasColimitsOfSize.{w, w} C]
  (F : K ⥤ Type w) (B : K ⥤ SimplexCategory ⥤ C)
  (c : Cocone (ConstantWeightHom.degree K (frames F B) (SimplexCategory.mk 0)))

/-- 元の次数零余錐の各脚に余積の挿入を前合成する。 -/
def elementsZeroCocone :
    Cocone (ConstantWeightHom.degree F.Elements (Functor.Elements.π F ⋙ B)
      (SimplexCategory.mk 0)) where
  pt := c.pt
  ι := {
    app e := (summand F B e.obj e.val).app (SimplexCategory.mk 0) ≫ c.ι.app e.obj
    naturality e e' f := by
      have hs := congr_app (summand_naturality F B f.hom e.val) (SimplexCategory.mk 0)
      rw [f.map_val] at hs
      change (B.map f.hom).app (SimplexCategory.mk 0) ≫
        ((summand F B e'.obj e'.val).app (SimplexCategory.mk 0) ≫ c.ι.app e'.obj) =
        ((summand F B e.obj e.val).app (SimplexCategory.mk 0) ≫ c.ι.app e.obj) ≫ 𝟙 _
      rw [← Category.assoc, ← NatTrans.comp_app, hs, NatTrans.comp_app, Category.assoc]
      have hc := c.ι.naturality f.hom
      change ((frames F B).map f.hom).app (SimplexCategory.mk 0) ≫ c.ι.app e'.obj =
        c.ι.app e.obj ≫ 𝟙 _ at hc
      rw [hc, Category.assoc] }

lemma weightedHomEquiv_zeroWeight :
    weightedHomEquiv F B (bousfieldKanWeight Kᵒᵖ) c.pt
      (FrameWeightRealization.bousfieldKanZeroWeight K ≫
        (ConstantWeightHom.homEquiv K (frames F B) (SimplexCategory.mk 0) c.pt).symm c.ι) =
      Functor.whiskerLeft (Functor.Elements.π F).op
          (FrameWeightRealization.bousfieldKanZeroWeight K) ≫
        (ConstantWeightHom.homEquiv F.Elements (Functor.Elements.π F ⋙ B)
          (SimplexCategory.mk 0) c.pt).symm (elementsZeroCocone F B c).ι := by
  apply NatTrans.ext
  funext e
  change (_ ≫ SSet.yonedaEquiv.symm (c.ι.app e.unop.obj)) ≫
      (cosimplicialHomMap (summand F B e.unop.obj e.unop.val)).app c.pt =
    _ ≫ SSet.yonedaEquiv.symm ((elementsZeroCocone F B c).ι.app e.unop)
  rw [Category.assoc, SSet.yonedaEquiv_symm_comp]
  rfl

/-- 指定要素射影の重み比較の後、元の表示同型の逆を通しても同じ増大射。 -/
lemma realizationIso_inv_augmentation :
    (FrameWeightRealization.functor F.Elements (Functor.Elements.π F ⋙ B)).map
        (bousfieldKanWeightPost (Functor.Elements.π F).op) ≫
      (realizationIso F B (bousfieldKanWeight Kᵒᵖ)).inv ≫
        FrameWeightRealization.bousfieldKanAugmentation (frames F B) c =
      FrameWeightRealization.bousfieldKanAugmentation (Functor.Elements.π F ⋙ B)
        (elementsZeroCocone F B c) := by
  apply ((FrameWeightRealization.adjunction F.Elements (Functor.Elements.π F ⋙ B)).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, realizationIso_inv_comp]
  dsimp only [realizationHomEquiv, Equiv.trans_apply]
  rw [Equiv.apply_symm_apply, FrameWeightRealization.bousfieldKanAugmentation_homEquiv,
    weightedHomEquiv_zeroWeight, ← Category.assoc,
    FrameWeightRealization.bousfieldKanZeroWeight_post]
  exact (FrameWeightRealization.bousfieldKanAugmentation_homEquiv _ _).symm

end SerrePositivity.DiagramModel.ElementsCopower
