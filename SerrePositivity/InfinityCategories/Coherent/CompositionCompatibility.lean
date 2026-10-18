module

public import SerrePositivity.InfinityCategories.Coherent.DoubleCompositionFace
public import SerrePositivity.InfinityCategories.Coherent.CompositionRecovery

/-!
# 合成面どうしの回収写像の一致

概要：順序付けられた二つの合成面の交わりで回収写像は一致する。
方針：三つの Hom に引き戻し、真部分区間の合成則と C の結合律を使う。
規約：全区間の Hom 写像の存在を仮定しない。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8–2.4.5.9 の空洞部分の貼合せ。
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory
open scoped Simplicial

namespace SerrePositivity.InfinityCategories.Coherent

variable {C : Type u} [Category.{v} C] [SimplicialCategory C]

set_option backward.isDefEq.respectTransparency false in
/-- 概要：二つの切断点の合成面の交わり上で両回収写像は厳密に一致する。
方針：三重合成の全射で前合成し、二つの真部分区間の合成則を C の結合律で結ぶ。
規約：必要な五つの区間の真部分性を明示し、外側区間の真部分性は要求しない。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.9 の合成面どうしの整合性。 -/
lemma hornCompositionHom_composition_overlap {n : ℕ} {i : Fin (n + 3)}
    (σ : (Λ[n + 2, i] : SSet.{max u v}) ⟶ SimplicialNerve C)
    (h0 : 0 < i) (hn : i < Fin.last (n + 2)) (a b c d : Fin (n + 3))
    (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d)
    (hpab : a ≠ 0 ∨ b ≠ Fin.last (n + 2))
    (hpbc : b ≠ 0 ∨ c ≠ Fin.last (n + 2))
    (hpcd : c ≠ 0 ∨ d ≠ Fin.last (n + 2))
    (hpac : a ≠ 0 ∨ c ≠ Fin.last (n + 2))
    (hpbd : b ≠ 0 ∨ d ≠ Fin.last (n + 2)) :
    SSet.Subcomplex.homOfLE
      (show pathThrough (a := ULift.up.{v} a) (c := ULift.up d) (ULift.up b) ⊓
        pathThrough (ULift.up c) ≤ pathThrough (ULift.up b) from inf_le_left) ≫
      hornCompositionHom σ h0 hn a b d hab (hbc.trans hcd) hpab hpbd =
    SSet.Subcomplex.homOfLE
      (show pathThrough (a := ULift.up.{v} a) (c := ULift.up d) (ULift.up b) ⊓
        pathThrough (ULift.up c) ≤ pathThrough (ULift.up c) from inf_le_right) ≫
      hornCompositionHom σ h0 hn a c d (hab.trans hbc) hcd hpac hpcd := by
  have := pathTripleToIntersection_epi
    (ULift.up.{v} a) (ULift.up b) (ULift.up c) (ULift.up d) hbc
  apply (cancel_epi (pathTripleToIntersection
    (ULift.up.{v} a) (ULift.up b) (ULift.up c) (ULift.up d))).mp
  simp only [← Category.assoc]
  rw [pathTripleToIntersection_toFirst, pathTripleToIntersection_toSecond]
  simp only [Category.assoc]
  rw [hornCompositionHom_on_product, hornCompositionHom_on_product]
  apply CategoryTheory.NatTrans.ext
  funext m
  apply ConcreteCategory.hom_ext
  rintro ⟨⟨x, y⟩, z⟩
  let A := hornObj σ a
  let B := hornObj σ b
  let D := hornObj σ c
  let E := hornObj σ d
  let f := hornProperIntervalHom σ h0 hn a b hab hpab
  let g := hornProperIntervalHom σ h0 hn b c hbc hpbc
  let h := hornProperIntervalHom σ h0 hn c d hcd hpcd
  have hbd := congrArg (fun k ↦ k.app m (y, z))
    (hornProperIntervalHom_comp σ h0 hn b c d hbc hcd hpbc hpcd hpbd)
  have hac := congrArg (fun k ↦ k.app m (x, y))
    (hornProperIntervalHom_comp σ h0 hn a b c hab hbc hpab hpbc hpac)
  change (hornProperIntervalHom σ h0 hn b d (hbc.trans hcd) hpbd).app m
    ((pathCompMap (ULift.up b) (ULift.up c) (ULift.up d)).app m (y, z)) =
      (SimplicialCategory.sHomComp B D E).app m (g.app m y, h.app m z) at hbd
  change (hornProperIntervalHom σ h0 hn a c (hab.trans hbc) hpac).app m
    ((pathCompMap (ULift.up a) (ULift.up b) (ULift.up c)).app m (x, y)) =
      (SimplicialCategory.sHomComp A B D).app m (f.app m x, g.app m y) at hac
  change (SimplicialCategory.sHomComp A B E).app m (f.app m x,
    (hornProperIntervalHom σ h0 hn b d (hbc.trans hcd) hpbd).app m
      ((pathCompMap (ULift.up b) (ULift.up c) (ULift.up d)).app m (y, z))) =
    (SimplicialCategory.sHomComp A D E).app m
      ((hornProperIntervalHom σ h0 hn a c (hab.trans hbc) hpac).app m
        ((pathCompMap (ULift.up a) (ULift.up b) (ULift.up c)).app m (x, y)), h.app m z)
  rw [hbd, hac]
  exact congrArg (fun k ↦ k.app m ((f.app m x, g.app m y), h.app m z))
    (e_assoc' SSet A B D E)

/-- 概要：全区間の任意の二つの内部合成面の交わり上で回収写像は一致する。
方針：切断点を比較して一般の整合性を適用し、逆順の場合は交わりの二成分を交換する。
規約：二つの切断点は一致してもよい。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.9 の空洞部分の全ての合成面の貼合せ。 -/
lemma hornInnerCompositionHom_overlap {n : ℕ} {i : Fin (n + 3)}
    (σ : (Λ[n + 2, i] : SSet.{max u v}) ⟶ SimplicialNerve C)
    (h0 : 0 < i) (hn : i < Fin.last (n + 2)) (b c : Fin (n + 3))
    (hb0 : 0 < b) (hbn : b < Fin.last (n + 2))
    (hc0 : 0 < c) (hcn : c < Fin.last (n + 2)) :
    SSet.Subcomplex.homOfLE
      (show pathThrough (a := ULift.up.{v} (0 : Fin (n + 3)))
        (c := ULift.up (Fin.last (n + 2))) (ULift.up b) ⊓
          pathThrough (ULift.up c) ≤ pathThrough (ULift.up b) from inf_le_left) ≫
      hornInnerCompositionHom σ h0 hn b hb0 hbn =
    SSet.Subcomplex.homOfLE
      (show pathThrough (a := ULift.up.{v} (0 : Fin (n + 3)))
        (c := ULift.up (Fin.last (n + 2))) (ULift.up b) ⊓
          pathThrough (ULift.up c) ≤ pathThrough (ULift.up c) from inf_le_right) ≫
      hornInnerCompositionHom σ h0 hn c hc0 hcn := by
  rcases le_total b c with hbc | hcb
  · exact hornCompositionHom_composition_overlap σ h0 hn 0 b c (Fin.last (n + 2))
      (Fin.zero_le b) hbc (Fin.le_last c)
      (Or.inr (ne_of_lt hbn)) (Or.inl (ne_of_gt hb0)) (Or.inl (ne_of_gt hc0))
      (Or.inr (ne_of_lt hcn)) (Or.inl (ne_of_gt hb0))
  · have he := hornCompositionHom_composition_overlap σ h0 hn 0 c b
      (Fin.last (n + 2)) (Fin.zero_le c) hcb (Fin.le_last b)
      (Or.inr (ne_of_lt hcn)) (Or.inl (ne_of_gt hc0)) (Or.inl (ne_of_gt hb0))
      (Or.inr (ne_of_lt hbn)) (Or.inl (ne_of_gt hc0))
    apply CategoryTheory.NatTrans.ext
    funext m
    apply ConcreteCategory.hom_ext
    intro F
    exact (congrArg (fun k ↦ k.app m ⟨F.1, ⟨F.2.2, F.2.1⟩⟩) he).symm

end SerrePositivity.InfinityCategories.Coherent
