module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardRoof
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardPairComposition

/-!
# 三列の先頭への forward の前合成

概要：X′→X→V←U→Y を元の三列 X′→V←U→Y へ縮約する。
方針：先頭の二列の区間合成と後続の隣接列をそのまま使う。
規約：元の語の射と全頂点・射を保持する。
使われ方：始点変更に対する roof 全円柱の比較。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardRoofPrecompose
open CategoryTheory
abbrev preWord : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward) _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardRoof.word

def collapse : preWord ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardRoof.word where
  orderHom := ⟨(![0, 0, 1, 2] : Fin 4 → Fin 3), by decide⟩
  direction_eq i := by fin_cases i <;> rfl

lemma collapse_cut (j : Fin 4) : collapse.cut j = (![0, 2, 3, 4] : Fin 4 → Fin 5) j := by
  fin_cases j <;> decide

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) [W.IsMultiplicative]
  {X' X Y V U : C}

lemma collapse_obj (f : X' ⟶ X) (a : X ⟶ V) (p : U ⟶ V) (hp : W p) (σ : U ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj collapse
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag.obj (W := W) f) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardRoof.obj W a p hp σ)) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardRoof.obj W (f ≫ a) p hp σ := by
  let S := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag.obj (W := W) f) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardRoof.obj W a p hp σ)
  have h0 : S.arrow (0 : Fin 4) = f :=
    eq_of_heq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.arrow_left_heq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag.obj f) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardRoof.obj W a p hp σ) (0 : Fin 1))
  have h1 : S.arrow (1 : Fin 4) = a :=
    eq_of_heq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.arrow_right_heq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag.obj f) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardRoof.obj W a p hp σ) (0 : Fin 3))
  have h2 : S.arrow (2 : Fin 4) = p :=
    eq_of_heq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.arrow_right_heq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag.obj f) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardRoof.obj W a p hp σ) (1 : Fin 3))
  have h3 : S.arrow (3 : Fin 4) = σ :=
    eq_of_heq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.arrow_right_heq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag.obj f) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardRoof.obj W a p hp σ) (2 : Fin 3))
  have he0 : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.map .forward S 0 1 (by decide)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.adjacent_direction (w := preWord) .forward (0 : Fin 4) rfl) = f :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.map_adjacent .forward S (0 : Fin 4) rfl).trans
      ((eq_of_heq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forward_arrow_heq S (0 : Fin 4) rfl)).trans h0)
  have he1 : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.map .forward S 1 2 (by decide)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.adjacent_direction (w := preWord) .forward (1 : Fin 4) rfl) = a :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.map_adjacent .forward S (1 : Fin 4) rfl).trans
      ((eq_of_heq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forward_arrow_heq S (1 : Fin 4) rfl)).trans h1)
  have hd : ∀ i : Fin 4, 0 ≤ i.val → i.val < 2 → preWord.direction i = .forward := by
    intro i _ hi
    fin_cases i
    · rfl
    · rfl
    · exact False.elim (by change 2 < 2 at hi; omega)
    · exact False.elim (by change 3 < 2 at hi; omega)
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.map .forward S 0 2 (by decide) hd = f ≫ a :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SegmentSubdivision.map_comp .forward S 0 1 2 (by decide) (by decide) hd).trans
      (congrArg₂ (fun f g => f ≫ g) he0 he1)
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagExt.object_ext
  · intro j
    change S.vertex (collapse.cut j) = _
    rw [collapse_cut]
    fin_cases j <;> rfl
  · intro j
    fin_cases j
    · exact heq_of_eq he
    · apply heq_of_eq
      change (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.map .backward S 2 3 _ _).unop = p
      exact congrArg (fun f : Opposite.op V ⟶ Opposite.op U => f.unop)
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.map_adjacent .backward S (2 : Fin 4) rfl).trans
          ((eq_of_heq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backward_arrow_heq S (2 : Fin 4) rfl)).trans
            (congrArg (fun f : U ⟶ V => f.op) h2)))
    · apply heq_of_eq
      change _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.map .forward S 3 4 _ _ = σ
      exact (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.map_adjacent .forward S (3 : Fin 4) rfl).trans
        ((eq_of_heq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forward_arrow_heq S (3 : Fin 4) rfl)).trans h3)

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardRoofPrecompose
