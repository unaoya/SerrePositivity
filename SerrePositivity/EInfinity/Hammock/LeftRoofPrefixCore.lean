module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardRoof
public import SerrePositivity.EInfinity.Hammock.LeftRoofPrefixCylinder

/-!
# 元の Under 円柱から先頭の恒等列を除く

概要：元の上行・下行・全成分を共通の三列で表す。
方針：同じ augmentation と包含を使い、恒等列の挿入で元の四列を回収する。
規約：元の対象・射・弱同値の条件を保持する。
使われ方：始点変更への全円柱の厳密な自然性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.Hammock.LeftRoof.Prefix
open CategoryTheory MonoidalCategory SSet
variable {C I : Type u} [Category.{u} C] [Category.{u} I]
  (W : MorphismProperty C) [W.IsMultiplicative]
  (U : I ⥤ C) {X Y : C} (p : U ⟶ (Functor.const I).obj X)
  (hp : ∀ i, W (p.app i)) (σ : U ⟶ (Functor.const I).obj Y)
  (hU : ∀ {i j} (a : i ⟶ j), W (U.map a)) (i : I)

def coreUpper : Under i ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardRoof.word (U.obj i) Y :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardRoof.diagram W (restrictedFrame U i) (restrictedFrame U i) (inclusion U i)
    (𝟙 _) (fun s => W.id_mem (U.obj s.right)) (restrictedRightLeg U σ i)
    (fun f => restrictedFrame_map_weak W U hU i f)
    (fun f => restrictedFrame_map_weak W U hU i f)

def coreLower : Under i ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardRoof.word (U.obj i) Y :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardRoof.diagram W ((Functor.const (Under i)).obj X) (restrictedFrame U i)
    ((Functor.const (Under i)).map (p.app i)) (restrictedAugmentation U p i)
    (restrictedAugmentation_weak W U p hp i) (restrictedRightLeg U σ i)
    (fun _ => W.id_mem X) (fun f => restrictedFrame_map_weak W U hU i f)

def coreComponent : coreUpper W U σ hU i ⟶ coreLower W U p hp σ hU i where
  app s := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardRoof.map W
    (a := U.map s.hom) (p := 𝟙 (U.obj s.right)) (hp := W.id_mem _)
    (σ := σ.app s.right) (a' := p.app i) (p' := p.app s.right) (hp' := hp s.right)
    (σ' := σ.app s.right) (p.app s.right) (hp s.right) (𝟙 _) (W.id_mem _)
    ((p.naturality s.hom).trans (Category.comp_id _)) rfl (Category.id_comp _).symm
  naturality s t f := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.hom_ext
    intro j
    fin_cases j
    · rfl
    · exact p.naturality f.right
    · exact (Category.comp_id _).trans (Category.id_comp _).symm
    · rfl

lemma coreUpper_insert : coreUpper W U σ hU i ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoofPrecomposeWords.lowerInsert =
    upperDiagram W U σ hU i := by
  have ho (s : Under i) :
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoofPrecomposeWords.lowerInsert ((coreUpper W U σ hU i).obj s) =
        (upperDiagram W U σ hU i).obj s :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardRoof.insert_obj W (U.map s.hom) (𝟙 _) (W.id_mem _) (σ.app s.right)
  apply CategoryTheory.Functor.hext ho
  intro s t f
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagExt.hom_hext (ho s) (ho t)
  intro j
  change HEq (((coreUpper W U σ hU i).map f).app (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoofPrecomposeWords.lowerInsert.cut j)) _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoofPrecomposeWords.lowerInsert_cut]
  fin_cases j <;> rfl

lemma coreLower_insert : coreLower W U p hp σ hU i ⋙
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoofPrecomposeWords.lowerInsert = lowerDiagram W U p hp σ hU i := by
  have ho (s : Under i) :
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoofPrecomposeWords.lowerInsert ((coreLower W U p hp σ hU i).obj s) =
        (lowerDiagram W U p hp σ hU i).obj s :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardRoof.insert_obj W (p.app i) (p.app s.right) (hp s.right) (σ.app s.right)
  apply CategoryTheory.Functor.hext ho
  intro s t f
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagExt.hom_hext (ho s) (ho t)
  intro j
  change HEq (((coreLower W U p hp σ hU i).map f).app (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoofPrecomposeWords.lowerInsert.cut j)) _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoofPrecomposeWords.lowerInsert_cut]
  fin_cases j <;> rfl

def coreCylinder : Fin 2 × Under i ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardRoof.word (U.obj i) Y :=
  Functor.uncurry.obj (ComposableArrows.mk₁ (coreComponent W U p hp σ hU i))

lemma coreCylinder_insert : coreCylinder W U p hp σ hU i ⋙
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoofPrecomposeWords.lowerInsert =
      Functor.uncurry.obj (ComposableArrows.mk₁ (component W U p hp σ hU i)) := by
  have ho (s : Fin 2 × Under i) :
      (coreCylinder W U p hp σ hU i ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoofPrecomposeWords.lowerInsert).obj s =
        (Functor.uncurry.obj (ComposableArrows.mk₁ (component W U p hp σ hU i))).obj s := by
    rcases s with ⟨t, s⟩
    fin_cases t
    · exact CategoryTheory.Functor.congr_obj (coreUpper_insert W U σ hU i) s
    · exact CategoryTheory.Functor.congr_obj (coreLower_insert W U p hp σ hU i) s
  apply CategoryTheory.Functor.hext ho
  intro s t f
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagExt.hom_hext (ho s) (ho t)
  intro j
  rcases s with ⟨s, a⟩
  rcases t with ⟨t, b⟩
  change HEq (((coreCylinder W U p hp σ hU i).map f).app
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoofPrecomposeWords.lowerInsert.cut j)) _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoofPrecomposeWords.lowerInsert_cut]
  fin_cases s <;> fin_cases t
  · fin_cases j <;> rfl
  · fin_cases j <;> rfl
  · exact False.elim (by have h := leOfHom f.1; change (1 : Fin 2) ≤ 0 at h; omega)
  · fin_cases j <;> rfl

end SerrePositivity.EInfinity.Hammock.LeftRoof.Prefix
