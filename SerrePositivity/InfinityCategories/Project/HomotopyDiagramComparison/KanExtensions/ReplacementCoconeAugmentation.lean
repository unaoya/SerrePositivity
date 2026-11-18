module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.KanExtensions.UnderWeightedColimitComparison
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.CoconeComparison.WeightedColimitAugmentation

/-!
概要：元の通常の余錐で simplicial replacement を評価した増大を、同じ Under coend と照合する。
方針：指定された脚で係数単体を評価し、余錐の可換条件で最初の頂点の移動を消す。
規約：Kerodon Construction 5.3.2.1（Tag 035V）の既存模型の評価の法則。
使われ方：S8 で反転 BK と元の圏の比較に、元の Čech 増大を通す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory SSet
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open SerrePositivity.InfinityCategories.Project.FilteredExchange
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
variable {I : Type u} [SmallCategory I] {F : I ⥤ SSet.{u}}

/-- 元の通常の余錐の脚による、replacement の全単体での評価。 -/
def replacementCoconeAugmentation (c : Cocone F) : simplicialReplacement F ⟶ c.pt where
  app _ := ↾fun s => SSet.yonedaEquiv (s.2 ≫ c.ι.app (s.1.obj 0))
  naturality {n m} θ := by
    apply ConcreteCategory.hom_ext
    rintro ⟨σ, x⟩
    change SSet.yonedaEquiv ((stdSimplex.map θ.unop ≫ x ≫
      F.map (σ.map (homOfLE (Fin.zero_le _)))) ≫ c.ι.app _) =
        c.pt.map θ (SSet.yonedaEquiv (x ≫ c.ι.app (σ.obj 0)))
    rw [Category.assoc, Category.assoc, c.w, ← Category.assoc]
    exact (SSet.yonedaEquiv_naturality θ.unop (x ≫ c.ι.app (σ.obj 0))).symm

/-- Under の各普遍脚の後で増大を取ると、元の余錐の同じ脚になる。 -/
lemma underWeightedColimitLeg_augmentation (c : Cocone F) (i : I) :
    underWeightedColimitLeg F i ≫ replacementCoconeAugmentation c =
      fst (F.obj i) (nerve (Under i)) ≫ c.ι.app i := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨x, τ⟩
  change SSet.yonedaEquiv ((SSet.yonedaEquiv.symm x ≫ F.map (τ.obj 0).hom) ≫
    c.ι.app (τ.obj 0).right) = (c.ι.app i).app _ x
  rw [Category.assoc, c.w, SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
  rfl

/-- 同じ大域 coend 比較は、元の通常の余錐への指定増大と可換。 -/
lemma underWeightedColimitToReplacement_augmentation (c : Cocone F) :
    underWeightedColimitToReplacement F ≫ replacementCoconeAugmentation c =
      weightedColimitAugmentation (underNerveWeight I) c := by
  apply weightedColimit_hom_ext
  intro i
  rw [← Category.assoc, underWeightedColimitToReplacement_ι,
    underWeightedColimitLeg_augmentation, weightedColimitι_augmentation]
  rfl

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
