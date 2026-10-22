module

public import SerrePositivity.KST.LocalizingInvariants.ProTowerNatMap
public import Mathlib.CategoryTheory.Products.Basic

/-!
概要：有限個の対象を持つ図式圏で、成分ごとの実 pro 同型から図式全体の実逆を作る。
方針：成分の逆を共通の添字へ送り、二段目の逆で全ての自然性の正方形を補正する。
規約：射の個数の有限性は不要。使われ方：元の class cospan の全図式の実 pro 比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory
namespace SerrePositivity.KST.LocalizingInvariants.TowerDiagram
open ProExcision
variable {J : Type w} [Category.{w} J] [Finite J]
  {C : Type u} [Category.{v} C] {X Y : Tower (J ⥤ C)} (f : LevelHom X Y)
  (hf : ∀ j, IsProIso (f.map ((CategoryTheory.evaluation J C).obj j)))

include hf in
lemma exists_uniform_pointwise_inverse (i : ℕ) :
    ∃ m, ∃ h : i ≤ m, ∃ b : ∀ j, (Y.obj m).obj j ⟶ (X.obj i).obj j,
      ∀ j, (f.app m).app j ≫ b j = (X.transition h).app j ∧
        b j ≫ (f.app i).app j = (Y.transition h).app j := by
  classical
  let : Fintype J := Fintype.ofFinite J
  choose m hm b hb bh using (fun j => hf j i)
  let p := max i (Finset.univ.sup m)
  have hp : i ≤ p := le_max_left _ _
  have hj : ∀ j, m j ≤ p := fun j =>
    (Finset.le_sup (Finset.mem_univ j)).trans (le_max_right _ _)
  refine ⟨p, hp, fun j => (Y.transition (hj j)).app j ≫ b j, ?_⟩
  intro j
  have hbj : (f.app (m j)).app j ≫ b j = (X.transition (hm j)).app j := hb j
  have bhj : b j ≫ (f.app i).app j = (Y.transition (hm j)).app j := bh j
  have hn := congrArg (fun t => t.app j) (f.naturality (hj j))
  change (X.transition (hj j)).app j ≫ (f.app (m j)).app j =
    (f.app p).app j ≫ (Y.transition (hj j)).app j at hn
  constructor
  · rw [← Category.assoc, ← hn, Category.assoc, hbj]
    exact congrArg (fun t => t.app j) (X.transition_comp (hj j) (hm j))
  · rw [Category.assoc, bhj]
    exact congrArg (fun t => t.app j) (Y.transition_comp (hj j) (hm j))

include hf in
lemma proIso_of_pointwise : IsProIso f := by
  intro i
  obtain ⟨m, hi, b, hb⟩ := exists_uniform_pointwise_inverse f hf i
  obtain ⟨k, hm, c, hc⟩ := exists_uniform_pointwise_inverse f hf m
  let a : Y.obj k ⟶ X.obj i :=
    { app := fun j => c j ≫ (X.transition hi).app j
      naturality := fun j l e => by
        calc
          (Y.obj k).map e ≫ (c l ≫ (X.transition hi).app l) =
              (Y.obj k).map e ≫ ((Y.transition hm).app l ≫ b l) := by
            rw [← (hb l).1, ← Category.assoc (c l), (hc l).2]
          _ = ((Y.transition hm).app j ≫ (Y.obj m).map e) ≫ b l := by
            rw [← Category.assoc, (Y.transition hm).naturality e]
          _ = c j ≫ (((f.app m).app j ≫ (Y.obj m).map e) ≫ b l) := by
            rw [← (hc j).2]
            simp only [Category.assoc]
          _ = c j ≫ (((X.obj m).map e ≫ (f.app m).app l) ≫ b l) := by
            rw [← (f.app m).naturality e]
          _ = c j ≫ ((X.obj m).map e ≫ (X.transition hi).app l) := by
            rw [Category.assoc, (hb l).1]
          _ = (c j ≫ (X.transition hi).app j) ≫ (X.obj i).map e := by
            rw [(X.transition hi).naturality e, Category.assoc] }
  refine ⟨k, hi.trans hm, a, ?_, ?_⟩
  · apply NatTrans.ext
    funext j
    change (f.app k).app j ≫ (c j ≫ (X.transition hi).app j) =
      (X.transition (hi.trans hm)).app j
    rw [← Category.assoc, (hc j).1]
    exact congrArg (fun t => t.app j) (X.transition_comp hm hi)
  · apply NatTrans.ext
    funext j
    change (c j ≫ (X.transition hi).app j) ≫ (f.app i).app j =
      (Y.transition (hi.trans hm)).app j
    have hn := congrArg (fun t => t.app j) (f.naturality hi)
    change (X.transition hi).app j ≫ (f.app i).app j =
      (f.app m).app j ≫ (Y.transition hi).app j at hn
    rw [Category.assoc, hn, ← Category.assoc, (hc j).2]
    exact congrArg (fun t => t.app j) (Y.transition_comp hm hi)

end SerrePositivity.KST.LocalizingInvariants.TowerDiagram
