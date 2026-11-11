module

public import Mathlib.CategoryTheory.Limits.Shapes.Preorder.WellOrderContinuous
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.Order.SuccPred.Limit

/-!
# 余積で与えられたセル付加の超限合成

## 概要
Berger–Moerdijk 命題 4.1 のセル代数の次数付き台で、各段までの生成元を集める。

## 方針
後続段の余積性と極限段の連続性から、指定された生成元の包含で余積を示す。

## 規約
各生成元は付加の直前の段で添字づける。

## 使われ方
セル代数の各段の次数付き自由表示。
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w

namespace SerrePositivity.EInfinity

open CategoryTheory Limits

variable {C : Type u} [Category.{v} C]
  {J : Type w} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
  (F : J ⥤ C) (I : J → Type w) (A : ∀ j, I j → C)
  (ι : ∀ j, ∀ i : I j, A j i ⟶ F.obj (Order.succ j))

/-- Cells adjoined strictly before the specified stage. -/
abbrev CellsBefore (j : J) := Σ k : Set.Iio j, I k

/-- The same cell regarded as a cell before a later stage. -/
def cellsBeforeInclusion {j k : J} (h : j ≤ k) :
    CellsBefore I j → CellsBefore I k :=
  fun ⟨i, x⟩ => ⟨⟨i.1, i.2.trans_le h⟩, x⟩

/-- The inclusion of a cell into a stage after its attachment. -/
def cellStageLeg (j : J) (x : CellsBefore I j) : A x.1 x.2 ⟶ F.obj j :=
  ι x.1 x.2 ≫ F.map (homOfLE (Order.succ_le_of_lt x.1.2))

omit [OrderBot J] [WellFoundedLT J] in
@[reassoc]
lemma cellStageLeg_comp {j k : J} (h : j ≤ k) (x : CellsBefore I j) :
    cellStageLeg F I A ι j x ≫ F.map (homOfLE h) =
      cellStageLeg F I A ι k (cellsBeforeInclusion I h x) := by
  simp only [cellStageLeg, Category.assoc, ← F.map_comp]
  rfl

/-- The coproduct cocone of the generators available at a stage. -/
def cellStageCofan (j : J) : Cofan (fun x : CellsBefore I j => A x.1 x.2) :=
  Cofan.mk (F.obj j) (cellStageLeg F I A ι j)

def restrictCellCofan {j k : J} (h : j ≤ k)
    (s : Cofan (fun x : CellsBefore I k => A x.1 x.2)) :
    Cofan (fun x : CellsBefore I j => A x.1 x.2) :=
  Cofan.mk s.pt (fun x => s.inj (cellsBeforeInclusion I h x))

/-- A continuous diagram obtained by coproduct attachments is the coproduct of its generators
at each stage, starting at an initial object. -/
def cellStageCofanIsColimit [F.IsWellOrderContinuous] (h₀ : IsInitial (F.obj ⊥))
    (hs : ∀ j, ¬ IsMax j →
      IsColimit (Cofan.mk (F.obj (Order.succ j)) (fun i : Option (I j) =>
        match i with
        | none => F.map (homOfLE (Order.le_succ j))
        | some i => ι j i) : Cofan (fun i : Option (I j) => i.elim (F.obj j) (A j))))
    (j : J) : IsColimit (cellStageCofan F I A ι j) := by
  induction j using SuccOrder.limitRecOn with
  | isMin j hj =>
    obtain rfl := hj.eq_bot
    refine Cofan.IsColimit.mk _ (fun s => h₀.to s.pt) ?_ (fun _ _ _ => h₀.hom_ext _ _)
    intro s x
    exact (not_lt_of_ge bot_le x.1.2).elim
  | succ j hj hprev =>
    let H := hs j hj
    let old (s : Cofan (fun x : CellsBefore I (Order.succ j) => A x.1 x.2)) :=
      hprev.desc (restrictCellCofan I A (Order.le_succ j) s)
    let sc (s : Cofan (fun x : CellsBefore I (Order.succ j) => A x.1 x.2)) :
        Cofan (fun i : Option (I j) => i.elim (F.obj j) (A j)) :=
      Cofan.mk s.pt (fun i : Option (I j) => match i with
        | none => old s
        | some i => s.inj ⟨⟨j, Order.lt_succ_of_not_isMax hj⟩, i⟩)
    let d (s : Cofan (fun x : CellsBefore I (Order.succ j) => A x.1 x.2)) :=
      H.desc (sc s)
    have hold (s) : F.map (homOfLE (Order.le_succ j)) ≫ d s = old s :=
      H.fac (sc s) (Discrete.mk none)
    have hnew (s) (i : I j) :
        ι j i ≫ d s = s.inj ⟨⟨j, Order.lt_succ_of_not_isMax hj⟩, i⟩ :=
      H.fac (sc s) (Discrete.mk (some i))
    have hd (s) (x : CellsBefore I (Order.succ j)) :
        cellStageLeg F I A ι (Order.succ j) x ≫ d s = s.inj x := by
      obtain ⟨⟨k, hk⟩, i⟩ := x
      have hkj : k ≤ j := (Order.lt_succ_iff_of_not_isMax hj).mp hk
      rcases hkj.lt_or_eq with h | rfl
      · let x : CellsBefore I j := ⟨⟨k, h⟩, i⟩
        change cellStageLeg F I A ι _ (cellsBeforeInclusion I (Order.le_succ j) x) ≫
          d s = _
        rw [← cellStageLeg_comp, Category.assoc, hold]
        exact hprev.fac (restrictCellCofan I A (Order.le_succ j) s) (Discrete.mk x)
      · simpa only [cellStageLeg, homOfLE_refl, F.map_id, Category.comp_id] using hnew s i
    refine Cofan.IsColimit.mk _ d hd ?_
    intro s k hk
    apply Cofan.IsColimit.hom_ext H
    intro i
    cases i with
    | none =>
      apply Cofan.IsColimit.hom_ext hprev
      intro x
      change cellStageLeg F I A ι j x ≫ F.map (homOfLE (Order.le_succ j)) ≫ k =
        cellStageLeg F I A ι j x ≫ F.map (homOfLE (Order.le_succ j)) ≫ d s
      rw [← Category.assoc, ← Category.assoc, cellStageLeg_comp]
      exact (hk _).trans (hd s _).symm
    | some i =>
      change ι j i ≫ k = ι j i ≫ d s
      have h : cellStageLeg F I A ι (Order.succ j)
          ⟨⟨j, Order.lt_succ_of_not_isMax hj⟩, i⟩ ≫ k = _ :=
        hk ⟨⟨j, Order.lt_succ_of_not_isMax hj⟩, i⟩
      simp only [cellStageLeg, homOfLE_refl, F.map_id, Category.comp_id] at h
      exact h.trans (hnew s i).symm
  | isSuccLimit j hj hprev =>
    let H := F.isColimitOfIsWellOrderContinuous j hj
    let extend (s : Cofan (fun x : CellsBefore I j => A x.1 x.2)) (k : Set.Iio j) :=
      (hprev k.1 k.2).desc (restrictCellCofan I A k.2.le s)
    have he (s) (k : Set.Iio j) (x : CellsBefore I k.1) :
        cellStageLeg F I A ι k.1 x ≫ extend s k =
          s.inj (cellsBeforeInclusion I k.2.le x) :=
      (hprev k.1 k.2).fac _ (Discrete.mk x)
    let sc (s : Cofan (fun x : CellsBefore I j => A x.1 x.2)) :
        Cocone ((Set.principalSegIio j).monotone.functor ⋙ F) :=
      { pt := s.pt
        ι :=
          { app := extend s
            naturality := by
              intro k l h
              change F.map (homOfLE (leOfHom h)) ≫ extend s l = extend s k ≫ 𝟙 s.pt
              erw [Category.comp_id]
              apply Cofan.IsColimit.hom_ext (hprev k.1 k.2)
              intro x
              change cellStageLeg F I A ι k.1 x ≫ F.map (homOfLE (leOfHom h)) ≫ extend s l =
                cellStageLeg F I A ι k.1 x ≫ extend s k
              rw [cellStageLeg_comp_assoc, he, he]
              rfl } }
    let d (s : Cofan (fun x : CellsBefore I j => A x.1 x.2)) := H.desc (sc s)
    have hd (s) (x : CellsBefore I j) :
        cellStageLeg F I A ι j x ≫ d s = s.inj x := by
      let k : Set.Iio j := ⟨Order.succ x.1, hj.succ_lt x.1.2⟩
      let x' : CellsBefore I k.1 := ⟨⟨x.1, Order.lt_succ_of_not_isMax
        (not_isMax_of_lt x.1.2)⟩, x.2⟩
      change cellStageLeg F I A ι j (cellsBeforeInclusion I k.2.le x') ≫ d s = _
      rw [← cellStageLeg_comp, Category.assoc]
      have h : F.map (homOfLE k.2.le) ≫ d s = extend s k := H.fac (sc s) k
      rw [h]
      exact he s k x'
    refine Cofan.IsColimit.mk _ d hd ?_
    intro s k hk
    apply H.hom_ext
    intro l
    apply Cofan.IsColimit.hom_ext (hprev l.1 l.2)
    intro x
    change cellStageLeg F I A ι l.1 x ≫ F.map (homOfLE l.2.le) ≫ k =
      cellStageLeg F I A ι l.1 x ≫ F.map (homOfLE l.2.le) ≫ d s
    rw [cellStageLeg_comp_assoc, cellStageLeg_comp_assoc]
    exact (hk _).trans (hd s _).symm

end SerrePositivity.EInfinity
