module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ZigzagValuePath
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.RelativeSegmentFunctor

/-!
# 元の相対関手による zigzag の像の評価

概要：相対関手で全列を送ってから評価する操作は、同じ関手を先に合成した評価に一致。
方針：向き付きの各列の関手像と、後ろ向きの像の同型の一意性を使う。
規約：相対関手自身に指定矢を反転する条件は加えない。
使われ方：自由相対解像の全単体作用素に沿う局所化 Hom の評価の自然性。
-/

@[expose] public section
universe u v u' v' u'' v''
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.Zigzag.Value
open CategoryTheory

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {E : Type u''} [Category.{v''} E] {W : MorphismProperty C} {V : MorphismProperty D}
  (F : LocalizerMorphism W V) (M : D ⥤ E) (hM : V.IsInvertedBy M)
  {w : Word} {X Y : C}

include hM in
lemma relativeInverts : W.IsInvertedBy (F.functor ⋙ M) := by
  intro A B f hf
  exact hM (F.functor.map f) (F.map f hf)

lemma arrow_relative_heq (d : Direction) (S : Zigzag W w X Y)
    (i : Fin w.length) (hi : w.direction i = d) :
    HEq (Direction.arrow d (Relative.obj F S) i hi)
      ((Direction.mapFunctor d F.functor).map (Direction.arrow d S i hi)) := by
  cases d <;> simp [Direction.arrow, Relative.obj, Direction.mapFunctor,
    CategoryTheory.Functor.map_comp, eqToHom_map]

lemma edge_relative (S : Zigzag W w X Y) (i : Fin w.length) :
    edge M hM (Relative.obj F S) i = edge (F.functor ⋙ M) (relativeInverts F M hM) S i := by
  cases hi : w.direction i with
  | forward =>
    rw [edge_forward M hM (Relative.obj F S) i hi,
      edge_forward (F.functor ⋙ M) (relativeInverts F M hM) S i hi]
    exact congrArg M.map (eq_of_heq (arrow_relative_heq F .forward S i hi))
  | backward =>
    rw [edge_backward M hM (Relative.obj F S) i hi,
      edge_backward (F.functor ⋙ M) (relativeInverts F M hM) S i hi]
    have hh : backwardIso M hM (Relative.obj F S) i hi =
        backwardIso (F.functor ⋙ M) (relativeInverts F M hM) S i hi := by
      apply Iso.ext
      change M.map (Direction.arrow .backward (Relative.obj F S) i hi).unop =
        M.map (F.functor.map (Direction.arrow .backward S i hi).unop)
      exact congrArg M.map
        (congrArg Quiver.Hom.unop (eq_of_heq (arrow_relative_heq F .backward S i hi)))
    exact congrArg Iso.inv hh

lemma path_relative (S : Zigzag W w X Y) :
    path M hM (Relative.obj F S) = path (F.functor ⋙ M) (relativeInverts F M hM) S := by
  apply ComposableArrows.ext (F := path M hM (Relative.obj F S))
    (G := path (F.functor ⋙ M) (relativeInverts F M hM) S) (fun _ => rfl)
  intro i hi
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  change (path M hM (Relative.obj F S)).map' i (i + 1) =
    (path (F.functor ⋙ M) (relativeInverts F M hM) S).map' i (i + 1)
  dsimp only [path]
  rw [ComposableArrows.mkOfObjOfMapSucc_map_succ _ _ i hi,
    ComposableArrows.mkOfObjOfMapSucc_map_succ _ _ i hi]
  exact edge_relative F M hM S ⟨i, hi⟩

lemma value_relative (S : Zigzag W w X Y) :
    value M hM (Relative.obj F S) = value (F.functor ⋙ M) (relativeInverts F M hM) S := by
  have h := CategoryTheory.Functor.hcongr_hom (path_relative F M hM S)
    (homOfLE (show (0 : Fin (w.length + 1)) ≤ Fin.last _ from Fin.zero_le _))
  apply eq_of_heq
  dsimp only [value]
  simp only [eqToHom_comp_heq_iff, comp_eqToHom_heq_iff,
    heq_eqToHom_comp_iff, heq_comp_eqToHom_iff]
  exact h

end SerrePositivity.EInfinity.Hammock.Zigzag.Value
