module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeSegmentFunctor

/-!
# 元の相対関手による zigzag の像の評価

概要：相対関手で全列を送ってから評価する操作は、同じ関手を先に合成した評価に一致。
方針：向き付きの各列の関手像と、後ろ向きの像の同型の一意性を使う。
規約：相対関手自身に指定矢を反転する条件は加えない。
使われ方：自由相対解像の全単体作用素に沿う局所化 Hom の評価の自然性。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v u' v' u'' v''
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {E : Type u''} [Category.{v''} E] {W : MorphismProperty C} {V : MorphismProperty D}
  (F : LocalizerMorphism W V) (M : D ⥤ E) (hM : V.IsInvertedBy M)
  {w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y : C}

include hM in
lemma relativeInverts : W.IsInvertedBy (F.functor ⋙ M) := by
  intro A B f hf
  exact hM (F.functor.map f) (F.map f hf)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.Value.relativeInverts export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (relativeInverts)


lemma arrow_relative_heq (d : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction) (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w X Y)
    (i : Fin w.length) (hi : w.direction i = d) :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.arrow d (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeZigzagFunctor.obj F S) i hi)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction.mapFunctor d F.functor).map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.arrow d S i hi)) := by
  cases d <;> simp [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.arrow, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeZigzagFunctor.obj, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction.mapFunctor,
    CategoryTheory.Functor.map_comp, eqToHom_map]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.Value.arrow_relative_heq export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (arrow_relative_heq)


lemma edge_relative (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w X Y) (i : Fin w.length) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.edge M hM (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeZigzagFunctor.obj F S) i = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.edge (F.functor ⋙ M) (relativeInverts F M hM) S i := by
  cases hi : w.direction i with
  | forward =>
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.edge_forward M hM (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeZigzagFunctor.obj F S) i hi,
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.edge_forward (F.functor ⋙ M) (relativeInverts F M hM) S i hi]
    exact congrArg M.map (eq_of_heq (arrow_relative_heq F .forward S i hi))
  | backward =>
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.edge_backward M hM (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeZigzagFunctor.obj F S) i hi,
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.edge_backward (F.functor ⋙ M) (relativeInverts F M hM) S i hi]
    have hh : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.backwardIso M hM (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeZigzagFunctor.obj F S) i hi =
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.backwardIso (F.functor ⋙ M) (relativeInverts F M hM) S i hi := by
      apply Iso.ext
      change M.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.arrow .backward (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeZigzagFunctor.obj F S) i hi).unop =
        M.map (F.functor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.arrow .backward S i hi).unop)
      exact congrArg M.map
        (congrArg Quiver.Hom.unop (eq_of_heq (arrow_relative_heq F .backward S i hi)))
    exact congrArg Iso.inv hh

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.Value.edge_relative export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (edge_relative)


lemma path_relative (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w X Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.path M hM (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeZigzagFunctor.obj F S) = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.path (F.functor ⋙ M) (relativeInverts F M hM) S := by
  apply ComposableArrows.ext (F := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.path M hM (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeZigzagFunctor.obj F S))
    (G := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.path (F.functor ⋙ M) (relativeInverts F M hM) S) (fun _ => rfl)
  intro i hi
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.path M hM (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeZigzagFunctor.obj F S)).map' i (i + 1) =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.path (F.functor ⋙ M) (relativeInverts F M hM) S).map' i (i + 1)
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.path]
  rw [ComposableArrows.mkOfObjOfMapSucc_map_succ _ _ i hi,
    ComposableArrows.mkOfObjOfMapSucc_map_succ _ _ i hi]
  exact edge_relative F M hM S ⟨i, hi⟩

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.Value.path_relative export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (path_relative)


lemma value_relative (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w X Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.value M hM (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeZigzagFunctor.obj F S) = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.value (F.functor ⋙ M) (relativeInverts F M hM) S := by
  have h := CategoryTheory.Functor.hcongr_hom (path_relative F M hM S)
    (homOfLE (show (0 : Fin (w.length + 1)) ≤ Fin.last _ from Fin.zero_le _))
  apply eq_of_heq
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.value]
  simp only [eqToHom_comp_heq_iff, comp_eqToHom_heq_iff,
    heq_eqToHom_comp_iff, heq_comp_eqToHom_iff]
  exact h

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.Value.value_relative export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (value_relative)


end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
