module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchangeTarget
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.TensorExchangeCoherence

/-!
概要：内部 Hom の合成と、二つの源の交換同型の両立。
方針：二重評価し、因子交換の自然性と六角形から得た整合性へ還元する。
規約：閉対称モノイダル圏での全パラメータの等式。
使われ方：BF 源の Hom パラメータに関する cotensor 比較の豊穣自然性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory MonoidalClosed
namespace SerrePositivity.KST.Spectra.InternalHomExchange
end SerrePositivity.KST.Spectra.InternalHomExchange
namespace SerrePositivity.InfinityCategories.Project.PointedSpaces
open _root_.SerrePositivity.KST.Spectra.InternalHomExchange
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C]

/-- 内部 Hom の合成は、源の交換と strength を通して厳密に可換。 -/
lemma composition (X Y A Z : C) :
    MonoidalClosed.comp X Y ((ihom A).obj Z) ≫ (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso X A Z).hom =
      (𝟙 ((ihom X).obj Y) ⊗ₘ (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso Y A Z).hom) ≫
        _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.map ((ihom X).obj Y) A ((ihom Y).obj Z) ≫
          (ihom A).map (MonoidalClosed.comp X Y Z) := by
  apply uncurry_injective
  apply uncurry_injective
  simp only [uncurry_natural_left, uncurry_ihom_map, _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.uncurry_uncurry_hom]
  rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.exchange_natural_right_assoc]
  rw [← whiskerLeft_comp_assoc A
    (X ◁ MonoidalClosed.comp X Y ((ihom A).obj Z))
    ((ihom.ev X).app ((ihom A).obj Z)) ((ihom.ev A).app Z)]
  rw [← uncurry_eq (MonoidalClosed.comp X Y ((ihom A).obj Z)),
    comp_eq, uncurry_curry, compTranspose_eq]
  simp only [whiskerLeft_comp, Category.assoc]
  rw [← whiskerLeft_comp_assoc X
    (A ◁ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.map ((ihom X).obj Y) A ((ihom Y).obj Z))
    ((ihom.ev A).app (((ihom X).obj Y) ⊗ ((ihom Y).obj Z)))
    (uncurry (comp X Y Z)), _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.evaluation]
  simp only [whiskerLeft_comp, Category.assoc]
  conv_rhs =>
    rw [← whiskerLeft_comp_assoc, id_tensorHom, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.exchange_natural_right]
  simp only [whiskerLeft_comp, Category.assoc]
  rw [comp_eq, uncurry_curry, compTranspose_eq]
  conv_rhs =>
    arg 2
    rw [← whiskerLeft_comp_assoc X, ← whiskerLeft_comp]
  erw [associator_inv_naturality_right_assoc]
  erw [whisker_exchange_assoc]
  simp only [whiskerLeft_comp, Category.assoc]
  have hr := _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.uncurry_uncurry_hom Y A Z
  change Y ◁ (A ◁ (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso Y A Z).hom ≫
    (ihom.ev A).app ((ihom Y).obj Z)) ≫ (ihom.ev Y).app Z = _ at hr
  simp only [whiskerLeft_comp, Category.assoc] at hr
  erw [hr]
  erw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.exchange_natural_left_assoc]
  have hc := congrArg (fun k ↦ k ≫
      A ◁ ((ihom.ev X).app Y ▷ (ihom Y).obj ((ihom A).obj Z)) ≫
      A ◁ (ihom.ev Y).app ((ihom A).obj Z) ≫ (ihom.ev A).app Z)
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.exchange_tensor_left_reordered X ((ihom X).obj Y) A
      ((ihom Y).obj ((ihom A).obj Z)))
  simp only [Category.assoc] at hc
  exact hc.symm

end SerrePositivity.InfinityCategories.Project.PointedSpaces

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
