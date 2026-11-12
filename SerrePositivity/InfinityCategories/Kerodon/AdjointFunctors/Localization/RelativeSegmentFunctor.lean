module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeZigzagFunctor
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment

/-!
# 相対関手と元の同方向の射列の両立

概要：関手を全列へ適用する操作は、元の同方向の区間の射列と両立する。
方針：前向きには元の関手、後ろ向きには反対関手を使い、全隣接射を照合する。
規約：区間の長さ零と元の両端の等式移送を保持する。
使われ方：元の WordAction の全列との自然性。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v u' v'
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

def Direction.mapFunctor {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    (d : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction) (F : C ⥤ D) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.category d C ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.category d D :=
  match d with | .forward => F | .backward => F.op

namespace Zigzag.Relative
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {W : MorphismProperty C} [W.IsMultiplicative] {V : MorphismProperty D} [V.IsMultiplicative]
  (F : LocalizerMorphism W V) {w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y : C}

omit [W.IsMultiplicative] [V.IsMultiplicative] in
lemma chain_eq (d : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction) (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w X Y)
    (p q : Fin (w.length + 1)) (hpq : p ≤ q)
    (hd : ∀ i : Fin w.length, p.val ≤ i.val → i.val < q.val → w.direction i = d) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.chain d (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeZigzagFunctor.obj F S) p q hpq hd =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.chain d S p q hpq hd ⋙ Direction.mapFunctor d F.functor := by
  have ho : ∀ k, (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.chain d (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeZigzagFunctor.obj F S) p q hpq hd).obj k =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.chain d S p q hpq hd ⋙ Direction.mapFunctor d F.functor).obj k := by
    intro k
    cases d <;> rfl
  apply ComposableArrows.ext ho
  intro k hk
  apply (conj_eqToHom_iff_heq _ _ (ho ⟨k, by omega⟩) (ho ⟨k + 1, by omega⟩)).2
  change HEq ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.chain d (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeZigzagFunctor.obj F S) p q hpq hd).map' k (k + 1))
    ((Direction.mapFunctor d F.functor).map ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.chain d S p q hpq hd).map' k (k + 1)))
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.chain]
  rw [ComposableArrows.mkOfObjOfMapSucc_map_succ _ _ k hk,
    ComposableArrows.mkOfObjOfMapSucc_map_succ _ _ k hk]
  cases d <;> simp [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.arrow, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeZigzagFunctor.obj, Direction.mapFunctor, eqToHom_map, Functor.map_comp]

omit [W.IsMultiplicative] [V.IsMultiplicative] in
lemma segment_map_heq (d : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction) (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w X Y)
    (p q : Fin (w.length + 1)) (hpq : p ≤ q)
    (hd : ∀ i : Fin w.length, p.val ≤ i.val → i.val < q.val → w.direction i = d) :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.map d (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeZigzagFunctor.obj F S) p q hpq hd)
      ((Direction.mapFunctor d F.functor).map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.map d S p q hpq hd)) := by
  cases d <;> dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.map, Direction.mapFunctor]
  all_goals
    simp only [Functor.map_comp, eqToHom_map, eqToHom_comp_heq_iff, comp_eqToHom_heq_iff,
      heq_eqToHom_comp_iff, heq_comp_eqToHom_iff]
    exact Functor.hcongr_hom (chain_eq F _ S p q hpq hd)
      (homOfLE (show (0 : Fin (q.val - p.val + 1)) ≤ Fin.last _ from Fin.zero_le _))

end Zigzag.Relative
end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
