module

public import SerrePositivity.KST.LocalizingInvariants.RelativeInvariant
public import SerrePositivity.InfinityCategories.Core.CommutativeSquareRealization

/-!
概要：提示源内の実四角形を、その実際の ν 像で Verdier 提示として認証する。
方針：包含・商の二辺と零角を照合し、独立に選択した絶対四角形との等号を要求しない。
規約：源内の可換性と ν 像の可換性を区別する。
使われ方：固定 dg 始域の零化証拠から相対局所化条件への接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.RelativeVerdierDiagram

variable {S : SSet.{u + 1}} (ν : S ⟶ StableInfinity.{u})

/-- 実際の像の二辺と零角から、同じ源四角形の相対証明書を作る。 -/
def ofSquare (d : VerdierSequence.{u})
    (F : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ S)
    (hb : squareBottomEdge ≫ F ≫ ν = SSet.yonedaEquiv.symm (stableArrow d.inclusion).edge)
    (hr : squareRightEdge ≫ F ≫ ν = SSet.yonedaEquiv.symm (stableArrow d.projection).edge)
    (hz : IsZeroCategory (stableObject (squareVertex (F ≫ ν) 0 1))) :
    RelativeVerdierDiagram ν where
  square := F
  image := {
    toVerdierSequence := d
    square := F ≫ ν
    left_eq := by
      have h := squareBottomEdge_source (F ≫ ν)
      rw [hb, Equiv.apply_symm_apply, (stableArrow d.inclusion).src_eq] at h
      exact h.symm
    middle_eq := by
      have h := squareBottomEdge_target (F ≫ ν)
      rw [hb, Equiv.apply_symm_apply, (stableArrow d.inclusion).tgt_eq] at h
      exact h.symm
    right_eq := by
      have h := squareRightEdge_target (F ≫ ν)
      rw [hr, Equiv.apply_symm_apply, (stableArrow d.projection).tgt_eq] at h
      exact h.symm
    bottom_edge := hb
    right_edge := hr
    zero_corner := hz }
  image_eq := rfl

@[simp] lemma ofSquare_square (d : VerdierSequence.{u})
    (F : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ S) (hb hr hz) :
    (ofSquare ν d F hb hr hz).square = F := rfl

@[simp] lemma ofSquare_sequence (d : VerdierSequence.{u})
    (F : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ S) (hb hr hz) :
    (ofSquare ν d F hb hr hz).image.toVerdierSequence = d := rfl

/-- 源内の可換性から、指定四辺を保つ零化四角形を実現する。
ν の像だけで可換性を仮定することはしない。 -/
lemma exists_square_of_source_comm [Quasicategory S]
    {a b z c : S _⦋0⦌}
    (i : Truncated.Edge (X := (truncation 2).obj S) a b)
    (q : Truncated.Edge (X := (truncation 2).obj S) b c)
    (l : Truncated.Edge (X := (truncation 2).obj S) a z)
    (r : Truncated.Edge (X := (truncation 2).obj S) z c)
    (h : Truncated.HomotopyCategory.homMk i ≫ Truncated.HomotopyCategory.homMk q =
      Truncated.HomotopyCategory.homMk l ≫ Truncated.HomotopyCategory.homMk r) :
    ∃ F : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ S,
      squareBottomEdge ≫ F = SSet.yonedaEquiv.symm i.edge ∧
      squareRightEdge ≫ F = SSet.yonedaEquiv.symm q.edge ∧
      squareLeftEdge ≫ F = SSet.yonedaEquiv.symm l.edge ∧
      squareTopEdge ≫ F = SSet.yonedaEquiv.symm r.edge := by
  obtain ⟨F, hb, ht, hl, hr⟩ := exists_stableSquare_of_homMk_comm i r l q h
  exact ⟨F, hb, hr, hl, ht⟩

/-- 厳密に可換な四辺を、元の四一単体を保つ coherent 四角形にする。 -/
lemma exists_coherentSquare_of_comm {C : Type v} [Category.{u} C] [SimplicialCategory C]
    [Quasicategory (SimplicialNerve C)] {a b z c : C}
    (i : a ⟶ b) (q : b ⟶ c) (l : a ⟶ z) (r : z ⟶ c) (h : i ≫ q = l ≫ r) :
    ∃ F : (Δ[1] ⊗ Δ[1] : SSet.{max u v}) ⟶ SimplicialNerve C,
      squareBottomEdge ≫ F = SSet.yonedaEquiv.symm (coherentNerveEdge i).edge ∧
      squareRightEdge ≫ F = SSet.yonedaEquiv.symm (coherentNerveEdge q).edge ∧
      squareLeftEdge ≫ F = SSet.yonedaEquiv.symm (coherentNerveEdge l).edge ∧
      squareTopEdge ≫ F = SSet.yonedaEquiv.symm (coherentNerveEdge r).edge := by
  have hc : Truncated.HomotopyCategory.homMk (coherentNerveEdge i).toTruncated ≫
      Truncated.HomotopyCategory.homMk (coherentNerveEdge q).toTruncated =
      Truncated.HomotopyCategory.homMk (coherentNerveEdge l).toTruncated ≫
        Truncated.HomotopyCategory.homMk (coherentNerveEdge r).toTruncated := by
    rw [Truncated.HomotopyCategory.homMk_comp_homMk
      (coherentNerveCompStruct i q).toTruncated,
      Truncated.HomotopyCategory.homMk_comp_homMk (coherentNerveCompStruct l r).toTruncated, h]
  obtain ⟨F, hb, ht, hl, hr⟩ := exists_stableSquare_of_homMk_comm
    (coherentNerveEdge i).toTruncated (coherentNerveEdge r).toTruncated
    (coherentNerveEdge l).toTruncated (coherentNerveEdge q).toTruncated hc
  exact ⟨F, hb, hr, hl, ht⟩

/-- 源内の零化と ν の元の二射を、同じ四辺の相対 Verdier 提示へ接続する。 -/
lemma exists_of_source_comm [Quasicategory S] (d : VerdierSequence.{u})
    {a b z c : S _⦋0⦌}
    (i : Truncated.Edge (X := (truncation 2).obj S) a b)
    (q : Truncated.Edge (X := (truncation 2).obj S) b c)
    (l : Truncated.Edge (X := (truncation 2).obj S) a z)
    (r : Truncated.Edge (X := (truncation 2).obj S) z c)
    (h : Truncated.HomotopyCategory.homMk i ≫ Truncated.HomotopyCategory.homMk q =
      Truncated.HomotopyCategory.homMk l ≫ Truncated.HomotopyCategory.homMk r)
    (hi : SSet.yonedaEquiv.symm i.edge ≫ ν =
      SSet.yonedaEquiv.symm (stableArrow d.inclusion).edge)
    (hq : SSet.yonedaEquiv.symm q.edge ≫ ν =
      SSet.yonedaEquiv.symm (stableArrow d.projection).edge)
    (hz : IsZeroCategory (stableObject (ν.app (Opposite.op ⦋0⦌) z))) :
    ∃ t : RelativeVerdierDiagram ν, t.image.toVerdierSequence = d ∧
      squareBottomEdge ≫ t.square = SSet.yonedaEquiv.symm i.edge ∧
      squareRightEdge ≫ t.square = SSet.yonedaEquiv.symm q.edge ∧
      squareLeftEdge ≫ t.square = SSet.yonedaEquiv.symm l.edge ∧
      squareTopEdge ≫ t.square = SSet.yonedaEquiv.symm r.edge := by
  obtain ⟨F, hb, hr, hl, ht⟩ := exists_square_of_source_comm i q l r h
  have hbi : squareBottomEdge ≫ F ≫ ν =
      SSet.yonedaEquiv.symm (stableArrow d.inclusion).edge := by
    rw [← Category.assoc, hb, hi]
  have hqr : squareRightEdge ≫ F ≫ ν =
      SSet.yonedaEquiv.symm (stableArrow d.projection).edge := by
    rw [← Category.assoc, hr, hq]
  have hFz : squareVertex F 0 1 = z := by
    have he := squareLeftEdge_target F
    let le := SSet.Edge.ofTruncated l
    have hle : squareLeftEdge ≫ F = SSet.yonedaEquiv.symm le.edge := hl
    have hez : S.δ 0 (SSet.yonedaEquiv (squareLeftEdge ≫ F)) = z := by
      rw [hle, Equiv.apply_symm_apply]
      exact le.tgt_eq
    exact he.symm.trans hez
  have hz' : IsZeroCategory (stableObject (squareVertex (F ≫ ν) 0 1)) := by
    change IsZeroCategory (stableObject (ν.app _ (squareVertex F 0 1)))
    rw [hFz]
    exact hz
  exact ⟨ofSquare ν d F hbi hqr hz', rfl, hb, hr, hl, ht⟩

end SerrePositivity.KST.LocalizingInvariants.RelativeVerdierDiagram
