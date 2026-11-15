module

public import SerrePositivity.HomotopicalAlgebra.Diagram.FrameBousfieldKanReindexing
public import SerrePositivity.HomotopicalAlgebra.Diagram.ConstantWeightHom

/-!
概要：指定された次数零の余錐へのBK frame実現の増大射と添字変更の可換性。
方針：定値零単体への重み射、simplicial Yoneda、元の実現随伴で転置する。
規約：余錐の脚を選び直さず、全添字変更で元の増大射を保つ。
使われ方：HTT 4.2.4.4のRR02(a)、評価点の指定増大射への接続。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe w u
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.InfinityCategories.Project.FilteredExchange
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
namespace SerrePositivity.DiagramModel.FrameWeightRealization
variable {K L : Type w} [SmallCategory K] [SmallCategory L]
  {C : Type u} [Category.{w} C] [HasColimitsOfSize.{w, w} C]

/-- BK重みから定値零単体への一意な射。 -/
def bousfieldKanZeroWeight (K : Type w) [SmallCategory K] :
    bousfieldKanWeight Kᵒᵖ ⟶ ConstantWeightHom.weight K (SimplexCategory.mk 0) where
  app _ := SSet.stdSimplex.isTerminalObj₀.from _
  naturality _ _ _ := SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

variable (A : K ⥤ SimplexCategory ⥤ C)
  (c : Cocone (ConstantWeightHom.degree K A (SimplexCategory.mk 0)))

/-- 与えられた次数零の余錐そのものへ向かうBK実現の増大射。 -/
def bousfieldKanAugmentation :
    (functor K A).obj (bousfieldKanWeight Kᵒᵖ) ⟶ c.pt :=
  ((adjunction K A).homEquiv _ _).symm
    (bousfieldKanZeroWeight K ≫
      (ConstantWeightHom.homEquiv K A (SimplexCategory.mk 0) c.pt).symm c.ι)

/-- 増大射の転置は指定余錐のsimplicial Yoneda像。 -/
lemma bousfieldKanAugmentation_homEquiv :
    (adjunction K A).homEquiv _ _ (bousfieldKanAugmentation A c) =
      bousfieldKanZeroWeight K ≫
        (ConstantWeightHom.homEquiv K A (SimplexCategory.mk 0) c.pt).symm c.ι :=
  ((adjunction K A).homEquiv _ _).apply_symm_apply _

/-- 定値零単体への重み射は、既存のBK重み比較と可換。 -/
lemma bousfieldKanZeroWeight_post (P : L ⥤ K) :
    bousfieldKanWeightPost P.op ≫ Functor.whiskerLeft P.op (bousfieldKanZeroWeight K) =
      bousfieldKanZeroWeight L := by
  apply NatTrans.ext
  funext l
  exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

/-- 指定余錐のYoneda像は、frame Homの添字制限と可換。 -/
lemma zeroWeightCocone_reindex (P : L ⥤ K) :
    Functor.whiskerLeft P.op
        ((ConstantWeightHom.homEquiv K A (SimplexCategory.mk 0) c.pt).symm c.ι) ≫
      (homReindexIso P A).hom.app c.pt =
    (ConstantWeightHom.homEquiv L (P ⋙ A) (SimplexCategory.mk 0) c.pt).symm
      (c.whisker P).ι := by
  apply NatTrans.ext
  funext l
  exact Category.comp_id _

/-- 添字変更後の増大射は、元の余錐をそのまま制限した増大射に一致する。 -/
lemma bousfieldKanReindexMap_augmentation (P : L ⥤ K) :
    bousfieldKanReindexMap P A ≫ bousfieldKanAugmentation A c =
      bousfieldKanAugmentation (P ⋙ A) (c.whisker P) := by
  apply ((adjunction L (P ⋙ A)).homEquiv _ _).injective
  have hrestricted := bousfieldKanAugmentation_homEquiv (P ⋙ A) (c.whisker P)
  simp only [Cocone.whisker_pt] at hrestricted
  rw [bousfieldKanReindexMap_homEquiv, bousfieldKanAugmentation_homEquiv, hrestricted]
  rw [Functor.whiskerLeft_comp, Category.assoc, zeroWeightCocone_reindex]
  rw [← Category.assoc, bousfieldKanZeroWeight_post]

end SerrePositivity.DiagramModel.FrameWeightRealization
