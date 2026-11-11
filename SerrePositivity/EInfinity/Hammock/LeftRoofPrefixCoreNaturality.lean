module

public import SerrePositivity.EInfinity.Hammock.LeftRoofPrefixCore
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardRoofPrecompose

/-!
# 始点変更と元の三列円柱の全関手の一致

概要：始点変更で制限した全円柱は先頭への前合成と隣接列の縮約に一致する。
方針：元の四頂点・全列・全縦射を直接照合する。
規約：単体の次数・時間・Under の全対象と射を保持する。
使われ方：元の余極限内の全円柱の始点自然性。
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
  (hU : ∀ {i j} (a : i ⟶ j), W (U.map a)) (i : I) {j : I} (a : i ⟶ j)

def coreChangeStart : Fin 2 × Under j ⥤ Fin 2 × Under i :=
  (Functor.id (Fin 2)).prod (Under.map a)

def corePrecomposeCylinder : Fin 2 × Under j ⥤
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardRoofPrecompose.preWord (U.obj i) Y :=
  ((Functor.const (Fin 2 × Under j)).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag.obj (W := W) (U.map a))).prod'
    (coreCylinder W U p hp σ hU j) ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendFunctor.functor

lemma coreCylinder_underMap : corePrecomposeCylinder W U p hp σ hU i a ⋙
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardRoofPrecompose.collapse =
      coreChangeStart i a ⋙ coreCylinder W U p hp σ hU i := by
  have ho (s : Fin 2 × Under j) :
      (corePrecomposeCylinder W U p hp σ hU i a ⋙
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardRoofPrecompose.collapse).obj s =
      (coreChangeStart i a ⋙ coreCylinder W U p hp σ hU i).obj s := by
    rcases s with ⟨t, s⟩
    fin_cases t
    · change _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardRoofPrecompose.collapse
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag.obj (W := W) (U.map a))
          (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardRoof.obj W (U.map s.hom) (𝟙 _) (W.id_mem _) (σ.app s.right))) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardRoof.obj W (U.map (a ≫ s.hom)) (𝟙 _) (W.id_mem _) (σ.app s.right)
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardRoofPrecompose.collapse_obj, U.map_comp]
    · change _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardRoofPrecompose.collapse
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag.obj (W := W) (U.map a))
          (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardRoof.obj W (p.app j) (p.app s.right) (hp s.right) (σ.app s.right))) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardRoof.obj W (p.app i) (p.app s.right) (hp s.right) (σ.app s.right)
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardRoofPrecompose.collapse_obj]
      exact congrArg (fun f => _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardRoof.obj W f (p.app s.right) (hp s.right)
        (σ.app s.right)) ((p.naturality a).trans (Category.comp_id _))
  apply CategoryTheory.Functor.hext ho
  intro s t f
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagExt.hom_hext (ho s) (ho t)
  intro k
  change HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendVertical.app (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag.obj (W := W) (U.map a)))
    ((coreCylinder W U p hp σ hU j).map f) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardRoofPrecompose.collapse.cut k)) _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardRoofPrecompose.collapse_cut]
  have hleft := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendVertical.app_left_heq (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag.obj (W := W) (U.map a)))
    ((coreCylinder W U p hp σ hU j).map f) (0 : Fin 2)
  have hright (k : Fin 4) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendVertical.app_right_heq (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag.obj (W := W) (U.map a)))
      ((coreCylinder W U p hp σ hU j).map f) k
  rcases s with ⟨s, s'⟩
  rcases t with ⟨t, t'⟩
  fin_cases s <;> fin_cases t
  · fin_cases k
    · exact hleft.trans (heq_of_eq (Category.id_comp (𝟙 (U.obj i))).symm)
    · exact hright 1
    · exact hright 2
    · exact hright 3
  · fin_cases k
    · exact hleft.trans (heq_of_eq (Category.id_comp (𝟙 (U.obj i))).symm)
    · exact hright 1
    · exact hright 2
    · exact hright 3
  · exact False.elim (by have h := leOfHom f.1; change (1 : Fin 2) ≤ 0 at h; omega)
  · fin_cases k
    · exact hleft.trans (heq_of_eq (Category.id_comp (𝟙 (U.obj i))).symm)
    · exact hright 1
    · exact hright 2
    · exact hright 3

end SerrePositivity.EInfinity.Hammock.LeftRoof.Prefix
