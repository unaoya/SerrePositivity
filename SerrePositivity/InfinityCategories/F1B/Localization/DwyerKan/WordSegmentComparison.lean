module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.WordInterval

/-!
# 圧縮後の区間合成と元の区間合成

概要：列の圧縮後の連続区間の合成は、元の切断間の連続区間の合成と等しい。
方針：圧縮後の射列を元の大区間の射列の単調な再添字付けと同定する。
規約：空 fiber と空区間を含む。比較は元の向きに応じた圏で行う。
使われ方：二つの語の写像の遷移と、合成語の遷移の同定。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.EInfinity.Hammock.WordAction
open CategoryTheory

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C} {a b : Word} {X Y : C}
  [W.IsMultiplicative]

/-- 圧縮後の同方向の射列は、元の切断間の射列の再添字付け。 -/
lemma chain_obj (f : a ⟶ b) (d : Direction) (S : Zigzag W a X Y)
    (p q : Fin (b.length + 1)) (hpq : p ≤ q)
    (hd : ∀ j : Fin b.length, p.val ≤ j.val → j.val < q.val → b.direction j = d) :
    Segment.chain d (obj f S) p q hpq hd =
      (intervalPosition f p q hpq).toFunctor ⋙ Segment.chain d S (f.cut p) (f.cut q)
        (f.cut_monotone hpq) (interval_direction f d p q hd) := by
  let hObj (k : Fin (q.val - p.val + 1)) :=
    congrArg (fun j => Direction.vertex d (S.vertex j))
      (index_intervalPosition f p q hpq k).symm
  apply ComposableArrows.ext hObj
  intro k hk
  apply (conj_eqToHom_iff_heq _ _ (hObj ⟨k, by omega⟩) (hObj ⟨k + 1, by omega⟩)).2
  let j : Fin b.length := ⟨p.val + k, by have := q.isLt; omega⟩
  have hpj : p ≤ j.castSucc := by change p.val ≤ p.val + k; omega
  have hjq : j.succ ≤ q := by change p.val + k + 1 ≤ q.val; omega
  have hj := hd j hpj (by change p.val + k < q.val; omega)
  change HEq ((Segment.chain d (obj f S) p q hpq hd).map' k (k + 1) (by omega) (by omega)) _
  rw [Segment.chain, ComposableArrows.mkOfObjOfMapSucc_map_succ _ _ k hk]
  change HEq (Direction.arrow d (obj f S) j hj)
    ((Segment.chain d S (f.cut p) (f.cut q) _ (interval_direction f d p q hd)).map
      (homOfLE (Segment.coordinate_monotone _ _ _ _
        (f.cut_monotone hpj) (f.cut_monotone (Fin.castSucc_le_succ j))
        (f.cut_monotone hjq))))
  exact (arrow_obj_heq f S d j hj).trans
    (Segment.map_parent_heq d S (f.cut p) (f.cut q) (f.cut j.castSucc) (f.cut j.succ)
      (f.cut_monotone hpj) (f.cut_monotone (Fin.castSucc_le_succ j))
      (f.cut_monotone hjq) (interval_direction f d p q hd))

omit [W.IsMultiplicative] in
/-- 区間合成は、その同じ射列の両端の射と異種等しい。 -/
lemma map_chain_heq (d : Direction) {w : Word} (S : Zigzag W w X Y)
    (p q : Fin (w.length + 1)) (hpq : p ≤ q)
    (hd : ∀ i : Fin w.length, p.val ≤ i.val → i.val < q.val → w.direction i = d) :
    HEq (Segment.map d S p q hpq hd) (Segment.chain d S p q hpq hd).hom := by
  change HEq (eqToHom _ ≫ (Segment.chain d S p q hpq hd).hom ≫ eqToHom _) _
  simp only [eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
  rfl

/-- 圧縮後の同方向の区間合成は、元の切断間の同じ区間合成。 -/
lemma segment_obj (f : a ⟶ b) (d : Direction) (S : Zigzag W a X Y)
    (p q : Fin (b.length + 1)) (hpq : p ≤ q)
    (hd : ∀ j : Fin b.length, p.val ≤ j.val → j.val < q.val → b.direction j = d) :
    Segment.map d (obj f S) p q hpq hd =
      Segment.map d S (f.cut p) (f.cut q) (f.cut_monotone hpq)
        (interval_direction f d p q hd) := by
  let F := Segment.chain d S (f.cut p) (f.cut q) (f.cut_monotone hpq)
    (interval_direction f d p q hd)
  have hc := Functor.hcongr_hom (chain_obj f d S p q hpq hd)
    (homOfLE (show (0 : Fin (q.val - p.val + 1)) ≤ Fin.last _ from Fin.zero_le _))
  have hf := Segment.fin_map_heq F (intervalPosition_zero f p q hpq)
    (intervalPosition_last f p q hpq)
    (homOfLE ((intervalPosition f p q hpq).monotone
      (show (0 : Fin (q.val - p.val + 1)) ≤ Fin.last _ from Fin.zero_le _)))
    (homOfLE (Fin.zero_le _))
  exact eq_of_heq ((map_chain_heq d (obj f S) p q hpq hd).trans
    (hc.trans (hf.trans (map_chain_heq d S _ _ _ _).symm)))

end SerrePositivity.EInfinity.Hammock.WordAction
