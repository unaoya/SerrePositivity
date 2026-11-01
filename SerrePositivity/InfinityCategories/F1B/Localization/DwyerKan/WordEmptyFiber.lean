module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.WordColumnRecovery
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.SegmentUnits

/-!
# 語の遷移の像の外の列は元の恒等列

概要：元の列の像に含まれない列には、同じ元の頂点の恒等射を挿入する。
方針：切断の特徴付けから空 fiber の両切断を同定し、空区間の合成を回収する。
規約：単射性は不要。向きに応じた圏での元の恒等射の比較。
使われ方：語の包含の像の特徴付けと、二つの像の交わりの比較。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.EInfinity.Hammock
open CategoryTheory

lemma Word.Hom.cut_empty_fiber {a b : Word} (f : a ⟶ b) (j : Fin b.length)
    (hj : ∀ i : Fin a.length, f.orderHom i ≠ j) : f.cut j.castSucc = f.cut j.succ := by
  apply Word.Hom.vertex_ext
  intro i
  rw [Word.Hom.lt_cut_iff, Word.Hom.lt_cut_iff]
  have hi : (f.orderHom i).val ≠ j.val := fun h => hj i (Fin.ext h)
  change (f.orderHom i).val < j.val ↔ (f.orderHom i).val < j.val + 1
  omega

/-- 像の外にある元の列の向き付き射は、同じ切断頂点の恒等射。 -/
lemma WordAction.empty_fiber_arrow_heq {C : Type u} [Category.{v} C]
    {W : MorphismProperty C} [W.IsMultiplicative] {a b : Word} {X Y : C}
    (f : a ⟶ b) (S : Zigzag W a X Y) (j : Fin b.length)
    (hj : ∀ i : Fin a.length, f.orderHom i ≠ j) :
    HEq (Direction.arrow (b.direction j) (WordAction.obj f S) j rfl)
      (𝟙 (Direction.vertex (b.direction j) (S.vertex (f.cut j.castSucc)))) := by
  have hpq := f.cut_empty_fiber j hj
  have hseg := WordAction.segment_heq_of_eq (b.direction j) S rfl hpq.symm
    (f.cut_monotone (Fin.castSucc_le_succ j)) le_rfl
    (fun i hi hi' => f.fiber_direction j i hi hi')
    (fun i hi hi' => by omega)
  exact (WordAction.arrow_obj_heq f S (b.direction j) j rfl).trans
    (hseg.trans (heq_of_eq (Segment.map_refl (b.direction j) S (f.cut j.castSucc) _)))

end SerrePositivity.EInfinity.Hammock
