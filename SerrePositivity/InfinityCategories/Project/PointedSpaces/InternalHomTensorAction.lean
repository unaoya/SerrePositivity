module


public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.TensorExchangeCoherence
public import SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchangeTarget

/-!
概要：閉対称モノイダル圏で、テンソル作用の Hom 写像と内部 Hom の源交換は整合する。
方針：評価の自然性と六角形から得た因子交換の等式へ還元する。
規約：単体集合の性質は使わない。使われ方：スペクトルの cotensor の構造可換性。
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

abbrev tensorSuspend (S X : C) := S ⊗ X

def tensorHom (S X Y : C) : (ihom X).obj Y ⟶ (ihom (S ⊗ X)).obj (S ⊗ Y) :=
  curry ((α_ S X ((ihom X).obj Y)).hom ≫ S ◁ (ihom.ev X).app Y)

omit [SymmetricCategory C] in
@[reassoc]
lemma tensorHom_evaluation (S X Y : C) :
    (S ⊗ X) ◁ _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.tensorHom S X Y ≫ (ihom.ev (S ⊗ X)).app (S ⊗ Y) =
      (α_ S X ((ihom X).obj Y)).hom ≫ S ◁ (ihom.ev X).app Y := uncurry_curry _

lemma tensorHom_strength (S X A Y : C) :
    _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.tensorHom S X ((ihom A).obj Y) ≫
        (ihom (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.tensorSuspend S X)).map (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.map S A Y) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.tensorSuspend S X) A (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.tensorSuspend S Y)).hom =
      (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso X A Y).hom ≫ (ihom A).map (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.tensorHom S X Y) := by
  apply MonoidalClosed.uncurry_injective
  apply MonoidalClosed.uncurry_injective
  simp only [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_ihom_map,
    _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.uncurry_uncurry_hom]
  rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.exchange_natural_right_assoc,
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.exchange_natural_right_assoc]
  have hev := congrArg (fun f ↦ A ◁ f)
    ((ihom.ev (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.tensorSuspend S X)).naturality (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.map S A Y))
  change A ◁ (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.tensorSuspend S X ◁ (ihom (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.tensorSuspend S X)).map
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.map S A Y) ≫
      (ihom.ev (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.tensorSuspend S X)).app ((ihom A).obj (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.tensorSuspend S Y))) =
    A ◁ ((ihom.ev (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.tensorSuspend S X)).app (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.tensorSuspend S ((ihom A).obj Y)) ≫
      _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.map S A Y) at hev
  simp only [whiskerLeft_comp] at hev
  rw [← Category.assoc (A ◁ _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.tensorSuspend S X ◁
    (ihom (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.tensorSuspend S X)).map (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.map S A Y)),
    hev, Category.assoc]
  rw [← whiskerLeft_comp_assoc A (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.tensorSuspend S X ◁ _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.tensorHom S X ((ihom A).obj Y)),
    _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.tensorHom_evaluation S]
  rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.evaluation]
  simp only [whiskerLeft_comp, Category.assoc]
  erw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.exchange_natural_right_assoc A S
    ((ihom.ev X).app ((ihom A).obj Y))]
  conv_rhs =>
    unfold _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.tensorHom
    rw [MonoidalClosed.uncurry_curry]
  erw [associator_naturality_right_assoc S X
    ((ihom.ev A).app ((ihom X).obj Y)),
    associator_naturality_right_assoc S X (A ◁ (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso X A Y).hom)]
  have hr := congrArg (fun f ↦ S ◁ f)
    (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.uncurry_uncurry_hom X A Y)
  change S ◁
      (X ◁ (A ◁ (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso X A Y).hom ≫ (ihom.ev A).app ((ihom X).obj Y)) ≫
        (ihom.ev X).app Y) = _ at hr
  simp only [whiskerLeft_comp, Category.assoc] at hr
  rw [hr]
  have hc := congrArg (fun f : _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.tensorSuspend S X ⊗ (A ⊗ ((ihom X).obj ((ihom A).obj Y))) ⟶
      S ⊗ (A ⊗ (X ⊗ ((ihom X).obj ((ihom A).obj Y)))) ↦ f ≫
      S ◁ A ◁ (ihom.ev X).app ((ihom A).obj Y) ≫
        S ◁ (ihom.ev A).app Y)
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.exchange_tensor_left S X A
      ((ihom X).obj ((ihom A).obj Y)))
  simp only [Category.assoc] at hc
  exact hc

end SerrePositivity.InfinityCategories.Project.PointedSpaces

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
