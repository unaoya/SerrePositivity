module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValueMaps

/-!
# 反転関手の元の自然変換と zigzag 評価

概要：全語の評価は元の自然変換の両端成分と可換。
方針：前向きの自然性と後ろ向きの逆射の可換式を全射列へ束ねる。
規約：自然変換の成分の可逆性は要求しない。
使われ方：元の局所化の因子化同型を π₀ の評価へ移す。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v u' v'
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {W : MorphismProperty C} {L M : C ⥤ D} (hL : W.IsInvertedBy L) (hM : W.IsInvertedBy M)
  (η : L ⟶ M) {w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y : C} (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w X Y)

lemma edge_naturality (i : Fin w.length) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.edge L hL S i ≫ η.app (S.vertex i.succ) =
      η.app (S.vertex i.castSucc) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.edge M hM S i := by
  cases hi : w.direction i with
  | forward =>
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.edge_forward L hL S i hi, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.edge_forward M hM S i hi]
    exact η.naturality (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.arrow .forward S i hi)
  | backward =>
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.edge_backward L hL S i hi, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.edge_backward M hM S i hi]
    have h := η.naturality (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.arrow .backward S i hi).unop
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.backwardIso L hL S i hi).hom ≫ η.app (S.vertex i.castSucc) =
      η.app (S.vertex i.succ) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.backwardIso M hM S i hi).hom at h
    apply (cancel_epi (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.backwardIso L hL S i hi).hom).1
    rw [Iso.hom_inv_id_assoc, ← Category.assoc, h, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.Value.edge_naturality export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (edge_naturality)


def pathNatTrans : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.path L hL S ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.path M hM S :=
  ComposableArrows.homMk (fun i => η.app (S.vertex i)) (by
    intro i hi
    simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.path, ComposableArrows.mkOfObjOfMapSucc_map_succ]
    exact edge_naturality hL hM η S ⟨i, hi⟩)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.Value.pathNatTrans export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (pathNatTrans)


lemma value_naturality : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.value L hL S ≫ η.app Y = η.app X ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.value M hM S := by
  have h := (pathNatTrans hL hM η S).naturality
    (homOfLE (show (0 : Fin (w.length + 1)) ≤ Fin.last _ from Fin.zero_le _))
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.path L hL S).hom ≫ η.app (S.vertex (Fin.last _)) =
    η.app (S.vertex 0) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.path M hM S).hom at h
  have hX := η.naturality (eqToHom S.first.symm)
  have hY := η.naturality (eqToHom S.last)
  simp only [eqToHom_map] at hX hY
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.value]
  simp only [Category.assoc]
  rw [hY, ← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.path L hL S).hom, h, Category.assoc,
    ← Category.assoc _ (η.app (S.vertex 0)), hX, Category.assoc]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.Value.value_naturality export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (value_naturality)


end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
