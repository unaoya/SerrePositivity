module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BackwardZigzag
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagExt
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory
public import Mathlib.CategoryTheory.Discrete.Basic
/-!
# 元の backward 一列の指定 Hom の離散圏への回収

概要：元の一列の圏を同じ始終点の指定射の離散圏へ元の評価で回収する。
方針：元の全射列の値と同じ端点の移送を使い、元の全縦射を保持する。
規約：モデル構造は要求せず、元の比較射を使う。
使われ方：DK5.7の元の単一列の Hom の弱比較への接続。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BackwardZigzagDiscrete
open CategoryTheory
variable {C : Type u} [Category.{u} C] {W : MorphismProperty C} [W.IsMultiplicative] {X Y : C}
def value (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .backward) X Y) : {f : Y ⟶ X // W f} :=
  ⟨eqToHom S.last.symm ≫ S.arrow (0 : Fin 1) ≫ eqToHom S.first,
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.transport_mem S.last.symm S.first (S.arrow (0 : Fin 1))).mpr
      (S.backward_mem (0 : Fin 1) rfl)⟩
lemma value_map {S T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .backward) X Y} (h : S ⟶ T) : value S = value T := by
  apply Subtype.ext
  have hc : S.arrow (0 : Fin 1) ≫ h.app (0 : Fin 2) =
      h.app (1 : Fin 2) ≫ T.arrow (0 : Fin 1) := h.comm (0 : Fin 1)
  have hfirst : h.app (0 : Fin 2) = eqToHom (S.first.trans T.first.symm) := h.first
  have hlast : h.app (1 : Fin 2) = eqToHom (S.last.trans T.last.symm) := h.last
  rw [hfirst, hlast] at hc
  simpa only [value, Category.assoc, eqToHom_trans_assoc, eqToHom_trans] using
    congrArg (fun z => eqToHom S.last.symm ≫ z ≫ eqToHom T.first) hc

instance homSubsingleton (S T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .backward) X Y) : Subsingleton (S ⟶ T) :=
  ⟨fun f g => by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.hom_ext
    intro j
    change Fin 2 at j
    cases j using Fin.cases with
    | zero => exact f.first.trans g.first.symm
    | succ j =>
      have hj : j = (0 : Fin 1) := Subsingleton.elim _ _
      subst j
      exact f.last.trans g.last.symm⟩

def toDiscrete : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .backward) X Y ⥤ Discrete {f : Y ⟶ X // W f} where
  obj S := Discrete.mk (value S)
  map h := eqToHom (congrArg Discrete.mk (value_map h))
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

def fromDiscrete : Discrete {f : Y ⟶ X // W f} ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .backward) X Y :=
  Discrete.functor (fun f => _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BackwardZigzag.obj f.val f.property)

omit [W.IsMultiplicative] in
lemma value_obj (f : {f : Y ⟶ X // W f}) : value (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BackwardZigzag.obj f.val f.property) = f := by
  apply Subtype.ext
  change (𝟙 Y) ≫ f.val ≫ 𝟙 X = f.val
  simp only [Category.id_comp, Category.comp_id]

omit [W.IsMultiplicative] in
lemma obj_value (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .backward) X Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BackwardZigzag.obj (value S).val (value S).property = S := by
  refine _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagExt.object_ext _ _ ?_ ?_
  · intro j
    change Fin 2 at j
    cases j using Fin.cases with
    | zero => exact S.first.symm
    | succ j =>
      have hj : j = (0 : Fin 1) := Subsingleton.elim _ _
      subst j
      exact S.last.symm
  · intro i
    change Fin 1 at i
    have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
    subst i
    change HEq (value S).val (S.arrow (0 : Fin 1))
    unfold value
    simp only [eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
    rfl

def discreteEquivalence : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .backward) X Y ≌ Discrete {f : Y ⟶ X // W f} where
  functor := toDiscrete
  inverse := fromDiscrete
  unitIso := NatIso.ofComponents (fun S => eqToIso (obj_value S).symm)
    (by intros; exact Subsingleton.elim _ _)
  counitIso := NatIso.ofComponents
    (fun S => eqToIso (congrArg Discrete.mk (value_obj S.as)))
    (by intros; exact Subsingleton.elim _ _)
end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BackwardZigzagDiscrete
