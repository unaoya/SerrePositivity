module

public import SerrePositivity.EInfinity.SimplicialLocalization.FreeResolutionGeneratorHom

/-!
# 元の標準 Hom の全生成作用素の回収

概要：標準 Hom の面・退化・augmentation を元の余モナドの同じ射作用へ戻す。
方針：元の固定対象の端点移送だけを異種等式で消去する。
規約：元の作用素と元の各射を保持する。
使われ方：元の一文字の列による追加退化の恒等式。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.SimplicialLocalization
open CategoryTheory Opposite SerrePositivity.HomotopyFunctionComplex.ComonadResolutionOperators
open scoped Simplicial

variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) {X Y : C.category}

lemma generatorHom_face_heq (n : ℕ) (i : Fin (n + 2))
    (f : (freeResolutionGeneratorHom C X Y) _⦋n + 1⦌) :
    HEq ((freeResolutionGeneratorHom C X Y).δ i f)
      ((face _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.freeRelativeComonad C (n + 1) i).functor.map f) := by
  change HEq (eqToHom _ ≫ ((freeResolution C).δ i).functor.map f ≫ eqToHom _) _
  simp only [eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
  rw [freeResolution_face]

lemma generatorHom_degeneracy_heq (n : ℕ) (i : Fin (n + 1))
    (f : (freeResolutionGeneratorHom C X Y) _⦋n⦌) :
    HEq ((freeResolutionGeneratorHom C X Y).σ i f)
      ((degeneracy _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.freeRelativeComonad C n i).functor.map f) := by
  change HEq (eqToHom _ ≫ ((freeResolution C).σ i).functor.map f ≫ eqToHom _) _
  simp only [eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
  rw [freeResolution_degeneracy]

lemma generatorHom_augmentation_heq (n : ℕ)
    (f : (freeResolutionGeneratorHom C X Y) _⦋n⦌) :
    HEq ((freeResolutionGeneratorHomAugmentation C X Y).app (op ⦋n⦌) f)
      ((augmentation _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.freeRelativeComonad C (n + 1)).functor.map f) := by
  change HEq (eqToHom _ ≫ ((freeResolutionAugmentationNatTrans C).app (op ⦋n⦌)).functor.map f ≫
    eqToHom _) _
  simp only [eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
  rfl

end SerrePositivity.EInfinity.SimplicialLocalization
