module

public import SerrePositivity.InfinityCategories.ModelBridge.MiddleBackwardFamilyPullback

/-!
# 中央の自明 cofibration を恒等列にする図式全体の置換

概要：右ブロックの同時 pushout により、中央が恒等列の全体の zigzag 関手を作る。
方針：同じ初点置換の comma 図式と正規化後の包含・端点自然性を使う。
規約：元の X,Y と左ブロックを保持する。長さ零と動く端点も含む。
使われ方：中央の恒等列の包含への関手的置換と unit の基礎データ。
-/

@[expose] public section
universe u v u' v'
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.MiddleBackward.Family
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra ForwardPath

variable {D : Type u'} [Category.{v'} D] {C : Type u} [Category.{v} C] [ModelCategory C]
  {n m : ℕ} {X Y : C} (F : Family D C n m X Y)

def pushoutInputs : D ⥤ InitialReplacement C m where
  obj d := pushoutInput (F.left.obj d) (F.right.obj d) (F.middle.app d)
  map f :=
    { left := F.right.map f
      right := (F.left.map f).app (Fin.last n)
      w := F.middle.naturality f }
  map_id d := by
    apply Comma.hom_ext
    · exact F.right.map_id d
    · change (F.left.map (𝟙 d)).app (Fin.last n) = 𝟙 _
      rw [F.left.map_id]
      rfl
  map_comp f g := by
    apply Comma.hom_ext
    · exact F.right.map_comp f g
    · change (F.left.map (f ≫ g)).app (Fin.last n) =
        (F.left.map f).app (Fin.last n) ≫ (F.left.map g).app (Fin.last n)
      rw [F.left.map_comp]
      rfl

def pushoutRight : D ⥤ ComposableArrows C m := F.pushoutInputs ⋙ normalizedPushoutFunctor

def pushoutRightInclusion : F.right ⟶ F.pushoutRight where
  app d := normalizedPushoutInclusion (F.pushoutInputs.obj d)
  naturality _ _ f := normalizedPushoutInclusion_naturality (F.pushoutInputs.map f)

def pushoutMiddle :
    F.pushoutRight ⋙ pathEvaluation C m 0 ⟶ F.left ⋙ pathEvaluation C n (Fin.last n) where
  app d := 𝟙 ((F.left.obj d).obj (Fin.last n))
  naturality d d' f := by
    change (normalizedPushoutComparison (F.pushoutInputs.map f)).app 0 ≫ 𝟙 _ =
      𝟙 _ ≫ (F.left.map f).app (Fin.last n)
    rw [Category.comp_id, Category.id_comp, normalizedPushoutComparison_zero]
    rfl

def pushoutOuterRight :
    (Functor.const D).obj Y ⟶ F.pushoutRight ⋙ pathEvaluation C m (Fin.last m) :=
  F.b ≫ Functor.whiskerRight F.pushoutRightInclusion (pathEvaluation C m (Fin.last m))

variable (hc : ∀ d, trivialCofibrations C (F.middle.app d))

include hc in
lemma pushoutRightInclusion_trivialCofibration (d : D) (i : Fin (m + 1)) :
    trivialCofibrations C ((F.pushoutRightInclusion.app d).app i) :=
  normalizedPushoutInclusion_trivialCofibration _ (hc d) i

include hc in
lemma pushoutRight_map_weak {d d' : D} (f : d ⟶ d') (i : Fin (m + 1)) :
    weakEquivalences C ((F.pushoutRight.map f).app i) :=
  normalizedPushoutComparison_weakEquivalence _ (hc d) (hc d') (F.right_mem f) i

def pushoutFamily : Family D C n m X Y where
  left := F.left
  right := F.pushoutRight
  a := F.a
  middle := F.pushoutMiddle
  b := F.pushoutOuterRight
  a_mem := F.a_mem
  middle_mem _ := (weakEquivalences C).id_mem _
  b_mem d := (weakEquivalences C).comp_mem _ _ (F.b_mem d)
    (F.pushoutRightInclusion_trivialCofibration hc d (Fin.last m)).2
  left_mem := F.left_mem
  right_mem := F.pushoutRight_map_weak hc

def pushoutFunctor : D ⥤ Zigzag (weakEquivalences C) (word n m) X Y :=
  (F.pushoutFamily hc).zigzagFunctor

end SerrePositivity.EInfinity.Hammock.MiddleBackward.Family
