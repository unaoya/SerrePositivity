module

-- functorFrom の公開型に含まれる内部の端点移送の証明も読み込む。
import all Mathlib.CategoryTheory.Grothendieck
public import Mathlib.CategoryTheory.Category.Cat.Op
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagFirstBoundaryRelativeForward
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagFirstBoundaryRelativeBackward
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeFixedCoefficientCoherence
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Transfunctor
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeMarkedCategory
/-!
# 固定した終点を持つ元の非空語の transfunctor

概要：相対圏の元の図式から、始点が動く元の zigzag 圏の係数 transfunctor を得る。
方針：先頭向きに従う境界作用と相対作用の厳密な自然性を全作用素へ束ねる。
規約：指定部分圏の元の全射と元の固定終点を保持し、恒等・合成を検証する。
使われ方：DK9.3・10.3・5.7の全語の graph の元の Grothendieck 分解。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory Opposite
variable {I : Type v} [Category I] (D : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word)
  (Y : (i : I) → (D.obj i).category)
  (hY : ∀ {i j : I} (θ : i ⟶ j), (D.map θ).functor.obj (Y i) = Y j)

def markedBase : I ⥤ Cat.{u, u} := D ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.markedCategoryFunctor

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.FirstBoundary.markedBase export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (markedBase)


def forwardFibre (i : I) : ((markedBase D).obj i)ᵒᵖ ⥤ Cat.{u, u} :=
  (wideSubcategoryInclusion (D.obj i).weakEquivalences).op ⋙
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardContravariant (W := (D.obj i).weakEquivalences) w (Y i)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.FirstBoundary.forwardFibre export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (forwardFibre)


def backwardFibre (i : I) : (markedBase D).obj i ⥤ Cat.{u, u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardCovariant (W := (D.obj i).weakEquivalences) w (Y i)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.FirstBoundary.backwardFibre export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (backwardFibre)


def forwardTransition {i j : I} (θ : i ⟶ j) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardFibre D w Y i ⟶
    ((markedBase D ⋙ Cat.opFunctor).map θ).toFunctor ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardFibre D w Y j where
  app X := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeFixedZigzagFunctor.fixedFunctor (w := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .forward w) (D.map θ)
    (rfl : (D.map θ).functor.obj X.unop.obj = (D.map θ).functor.obj X.unop.obj) (hY θ)).toCatHom
  naturality X X' f := by
    apply Cat.Hom.ext
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forward_relative_functor (D.map θ) (hY θ) f.unop.hom

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.FirstBoundary.forwardTransition export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (forwardTransition)


def backwardTransition {i j : I} (θ : i ⟶ j) : backwardFibre D w Y i ⟶
    ((markedBase D).map θ).toFunctor ⋙ backwardFibre D w Y j where
  app X := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeFixedZigzagFunctor.fixedFunctor (w := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .backward w) (D.map θ)
    (rfl : (D.map θ).functor.obj X.obj = (D.map θ).functor.obj X.obj) (hY θ)).toCatHom
  naturality X X' f := by
    apply Cat.Hom.ext
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backward_relative_functor (D.map θ) (hY θ) f.hom f.property

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.FirstBoundary.backwardTransition export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (backwardTransition)


private lemma natTrans_hext {C E : Type*} [Category* C] [Category* E]
    {F F' G G' : C ⥤ E} (hF : F = F') (hG : G = G')
    (α : F ⟶ G) (β : F' ⟶ G') (ha : ∀ X, HEq (α.app X) (β.app X)) : HEq α β := by
  cases hF
  cases hG
  apply heq_of_eq
  ext X
  exact eq_of_heq (ha X)

private lemma forwardTransition_id (i : I) :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardTransition D w Y hY (𝟙 i)) (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardFibre D w Y i)) := by
  refine natTrans_hext rfl ?_ _ _ ?_
  · rw [(markedBase D ⋙ Cat.opFunctor).map_id]
    rfl
  · intro X
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.fixedFunctor_id_toCatHom_heq (D.map (𝟙 i)) (D.map_id i)
      X.unop.obj (Y i) (hY (𝟙 i))

private lemma backwardTransition_id (i : I) :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardTransition D w Y hY (𝟙 i)) (𝟙 (backwardFibre D w Y i)) := by
  refine natTrans_hext rfl ?_ _ _ ?_
  · rw [(markedBase D).map_id]
    rfl
  · intro X
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.fixedFunctor_id_toCatHom_heq (D.map (𝟙 i)) (D.map_id i)
      X.obj (Y i) (hY (𝟙 i))

private lemma forwardTransition_comp {i j k : I} (θ : i ⟶ j) (φ : j ⟶ k) :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardTransition D w Y hY (θ ≫ φ))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardTransition D w Y hY θ ≫
        Functor.whiskerLeft ((markedBase D ⋙ Cat.opFunctor).map θ).toFunctor
          (forwardTransition D w Y hY φ)) := by
  refine natTrans_hext rfl ?_ _ _ ?_
  · rw [(markedBase D ⋙ Cat.opFunctor).map_comp]
    rfl
  · intro X
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.fixedFunctor_comp_toCatHom_heq (D.map θ) (D.map φ) (D.map (θ ≫ φ))
      (D.map_comp θ φ) X.unop.obj (Y i) (Y j) (Y k) (hY θ) (hY φ) (hY (θ ≫ φ))

private lemma backwardTransition_comp {i j k : I} (θ : i ⟶ j) (φ : j ⟶ k) :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardTransition D w Y hY (θ ≫ φ))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardTransition D w Y hY θ ≫
        Functor.whiskerLeft ((markedBase D).map θ).toFunctor
          (backwardTransition D w Y hY φ)) := by
  refine natTrans_hext rfl ?_ _ _ ?_
  · rw [(markedBase D).map_comp]
    rfl
  · intro X
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.fixedFunctor_comp_toCatHom_heq (D.map θ) (D.map φ) (D.map (θ ≫ φ))
      (D.map_comp θ φ) X.obj (Y i) (Y j) (Y k) (hY θ) (hY φ) (hY (θ ≫ φ))

def forwardTransfunctor : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Transfunctor.Covariant (markedBase D ⋙ Cat.opFunctor) :=
  Grothendieck.functorFrom (forwardFibre D w Y) (fun θ => forwardTransition D w Y hY θ)
    (fun i => by
      apply eq_of_heq
      exact (forwardTransition_id D w Y hY i).trans (eqToHom_heq_id_dom _ _ _).symm)
    (fun _ _ _ θ φ => by
      apply eq_of_heq
      exact (forwardTransition_comp D w Y hY θ φ).trans (comp_eqToHom_heq _ _).symm)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.FirstBoundary.forwardTransfunctor export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (forwardTransfunctor)


def backwardTransfunctor : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Transfunctor.Covariant (markedBase D) :=
  Grothendieck.functorFrom (backwardFibre D w Y) (fun θ => backwardTransition D w Y hY θ)
    (fun i => by
      apply eq_of_heq
      exact (backwardTransition_id D w Y hY i).trans (eqToHom_heq_id_dom _ _ _).symm)
    (fun _ _ _ θ φ => by
      apply eq_of_heq
      exact (backwardTransition_comp D w Y hY θ φ).trans (comp_eqToHom_heq _ _).symm)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.FirstBoundary.backwardTransfunctor export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (backwardTransfunctor)

lemma forwardTransfunctor_obj (i : I) (X : WideSubcategory (D.obj i).weakEquivalences) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardTransfunctor D w Y hY).obj ⟨i, op X⟩ =
      Cat.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag (D.obj i).weakEquivalences (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .forward w) X.obj (Y i)) := rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.FirstBoundary.forwardTransfunctor_obj export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (forwardTransfunctor_obj)


lemma backwardTransfunctor_obj (i : I) (X : WideSubcategory (D.obj i).weakEquivalences) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardTransfunctor D w Y hY).obj ⟨i, X⟩ =
      Cat.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag (D.obj i).weakEquivalences (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .backward w) X.obj (Y i)) := rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.FirstBoundary.backwardTransfunctor_obj export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (backwardTransfunctor_obj)


lemma forwardTransfunctor_map {Z Z' : Grothendieck (markedBase D ⋙ Cat.opFunctor)} (f : Z ⟶ Z') :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardTransfunctor D w Y hY).map f =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeFixedZigzagFunctor.fixedFunctor (w := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .forward w) (D.map f.base)
        (rfl : (D.map f.base).functor.obj Z.fiber.unop.obj =
          (D.map f.base).functor.obj Z.fiber.unop.obj) (hY f.base)).toCatHom ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagFirstBoundaryMaps.forwardFunctor (W := (D.obj Z'.base).weakEquivalences) (w := w)
          (Y := Y Z'.base) f.fiber.unop.hom).toCatHom := rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.FirstBoundary.forwardTransfunctor_map export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (forwardTransfunctor_map)


lemma backwardTransfunctor_map {Z Z' : Grothendieck (markedBase D)} (f : Z ⟶ Z') :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardTransfunctor D w Y hY).map f =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeFixedZigzagFunctor.fixedFunctor (w := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .backward w) (D.map f.base)
        (rfl : (D.map f.base).functor.obj Z.fiber.obj =
          (D.map f.base).functor.obj Z.fiber.obj) (hY f.base)).toCatHom ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagFirstBoundaryBackwardMaps.backwardFunctor (W := (D.obj Z'.base).weakEquivalences) (w := w)
          (Y := Y Z'.base) f.fiber.hom f.fiber.property).toCatHom := rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.FirstBoundary.backwardTransfunctor_map export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (backwardTransfunctor_map)


end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
