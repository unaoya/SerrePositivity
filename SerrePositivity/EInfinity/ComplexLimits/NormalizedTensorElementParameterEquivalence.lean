module
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorElementParameter

/-!
概要：実全単体図式の大域パラメータ射は同じ元の Hom への弱比較である。
方針：対象/Hom の宇宙比較の厳密な逆を作り、元の終端 augmentation の反転性を使う。
規約：大域パラメータ射そのものを保つ。使われ方：同じ Hom の大域三角形の検出。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory SSet
attribute [local instance] uliftCategory
open SerrePositivity.DifferentialGraded
open SerrePositivity.SimplicialModel
variable (A : Type u) [CommRing A] (X Y : Complex A)

def normalizedTensorElementLiftNerveInverse :
    nerve (ULiftHom.{u + 1}
      ((((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (normalizedSimplexTensor A X)).obj Y).Elements)ᵒᵖ)) ⟶
    nerve (normalizedTensorElementIndex A X Y) where
  app _ := ↾fun Γ => Γ ⋙ (ULiftHom.down ⋙ ULift.upFunctor ⋙ ULiftHom.up)
  naturality _ _ _ := rfl

def normalizedTensorElementLiftNerveIso : nerve (normalizedTensorElementIndex A X Y) ≅
    nerve (ULiftHom.{u + 1}
      ((((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (normalizedSimplexTensor A X)).obj Y).Elements)ᵒᵖ)) where
  hom := normalizedTensorElementLiftNerveMap A X Y
  inv := normalizedTensorElementLiftNerveInverse A X Y
  hom_inv_id := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro Γ
    refine CategoryTheory.Functor.ext (fun _ => rfl) (fun i j f => ?_)
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl
  inv_hom_id := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro Γ
    refine CategoryTheory.Functor.ext (fun _ => rfl) (fun i j f => ?_)
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl

lemma normalizedTensorElementParameterMap_localized_isIso :
    IsIso (AnodyneHomotopy.anodyneQ.map (normalizedTensorElementParameterMap A X Y)) := by
  have : IsIso (normalizedTensorElementLiftNerveMap A X Y) :=
    (normalizedTensorElementLiftNerveIso A X Y).isIso_hom
  have := _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.SimplexTerminalNerve.liftedAugmentation_localized_isIso.{u, u + 1}
    ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (normalizedSimplexTensor A X)).obj Y)
  dsimp only [normalizedTensorElementParameterMap]
  rw [CategoryTheory.Functor.map_comp]
  infer_instance

lemma normalizedTensorElementPinchedMap_localized_isIso :
    IsIso (AnodyneHomotopy.anodyneQ.map (normalizedTensorElementPinchedMap A X Y)) := by
  have := normalizedTensorElementParameterMap_localized_isIso A X Y
  dsimp only [normalizedTensorElementPinchedMap]
  rw [CategoryTheory.Functor.map_comp]
  infer_instance

end SerrePositivity.EInfinity.ComplexLimits
