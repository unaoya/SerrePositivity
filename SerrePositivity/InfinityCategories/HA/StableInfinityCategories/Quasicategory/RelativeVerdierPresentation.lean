module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.CommutativeSquareRealization
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.RelativeInvariant

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
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.RelativeVerdierDiagram
end SerrePositivity.KST.LocalizingInvariants.RelativeVerdierDiagram
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory
open _root_.SerrePositivity.KST.LocalizingInvariants


variable {S : SSet.{u + 1}} (ν : S ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u})

/-- 実際の像の二辺と零角から、同じ源四角形の相対証明書を作る。 -/
def ofSquare (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.VerdierSequence.{u})
    (F : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ S)
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ F ≫ ν = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow d.inclusion).edge)
    (hr : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ F ≫ ν = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow d.projection).edge)
    (hz : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (F ≫ ν) 0 1))) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.RelativeVerdierDiagram ν where
  square := F
  image := {
    toVerdierSequence := d
    square := F ≫ ν
    left_eq := by
      have h := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareBottomEdge_source (F ≫ ν)
      rw [hb, Equiv.apply_symm_apply, (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow d.inclusion).src_eq] at h
      exact h.symm
    middle_eq := by
      have h := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareBottomEdge_target (F ≫ ν)
      rw [hb, Equiv.apply_symm_apply, (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow d.inclusion).tgt_eq] at h
      exact h.symm
    right_eq := by
      have h := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareRightEdge_target (F ≫ ν)
      rw [hr, Equiv.apply_symm_apply, (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow d.projection).tgt_eq] at h
      exact h.symm
    bottom_edge := hb
    right_edge := hr
    zero_corner := hz }
  image_eq := rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.RelativeVerdierDiagram export _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory (ofSquare)


@[simp] lemma ofSquare_square (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.VerdierSequence.{u})
    (F : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ S) (hb hr hz) :
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.ofSquare ν d F hb hr hz).square = F := rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.RelativeVerdierDiagram export _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory (ofSquare_square)


@[simp] lemma ofSquare_sequence (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.VerdierSequence.{u})
    (F : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ S) (hb hr hz) :
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.ofSquare ν d F hb hr hz).image.toVerdierSequence = d := rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.RelativeVerdierDiagram export _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory (ofSquare_sequence)


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
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ F = SSet.yonedaEquiv.symm i.edge ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ F = SSet.yonedaEquiv.symm q.edge ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ F = SSet.yonedaEquiv.symm l.edge ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ F = SSet.yonedaEquiv.symm r.edge := by
  obtain ⟨F, hb, ht, hl, hr⟩ := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.exists_stableSquare_of_homMk_comm i r l q h
  exact ⟨F, hb, hr, hl, ht⟩

with_weak_namespace _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.RelativeVerdierDiagram export _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory (exists_square_of_source_comm)


/-- 厳密に可換な四辺を、元の四一単体を保つ coherent 四角形にする。 -/
lemma exists_coherentSquare_of_comm {C : Type v} [Category.{u} C] [SimplicialCategory C]
    [Quasicategory (SimplicialNerve C)] {a b z c : C}
    (i : a ⟶ b) (q : b ⟶ c) (l : a ⟶ z) (r : z ⟶ c) (h : i ≫ q = l ≫ r) :
    ∃ F : (Δ[1] ⊗ Δ[1] : SSet.{max u v}) ⟶ SimplicialNerve C,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ F = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge i).edge ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ F = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge q).edge ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ F = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge l).edge ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ F = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge r).edge := by
  have hc : Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge i).toTruncated ≫
      Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge q).toTruncated =
      Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge l).toTruncated ≫
        Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge r).toTruncated := by
    rw [Truncated.HomotopyCategory.homMk_comp_homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveCompStruct i q).toTruncated,
      Truncated.HomotopyCategory.homMk_comp_homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveCompStruct l r).toTruncated, h]
  obtain ⟨F, hb, ht, hl, hr⟩ := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.exists_stableSquare_of_homMk_comm
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge i).toTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge r).toTruncated
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge l).toTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge q).toTruncated hc
  exact ⟨F, hb, hr, hl, ht⟩

with_weak_namespace _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.RelativeVerdierDiagram export _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory (exists_coherentSquare_of_comm)


/-- 源内の零化と ν の元の二射を、同じ四辺の相対 Verdier 提示へ接続する。 -/
lemma exists_of_source_comm [Quasicategory S] (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.VerdierSequence.{u})
    {a b z c : S _⦋0⦌}
    (i : Truncated.Edge (X := (truncation 2).obj S) a b)
    (q : Truncated.Edge (X := (truncation 2).obj S) b c)
    (l : Truncated.Edge (X := (truncation 2).obj S) a z)
    (r : Truncated.Edge (X := (truncation 2).obj S) z c)
    (h : Truncated.HomotopyCategory.homMk i ≫ Truncated.HomotopyCategory.homMk q =
      Truncated.HomotopyCategory.homMk l ≫ Truncated.HomotopyCategory.homMk r)
    (hi : SSet.yonedaEquiv.symm i.edge ≫ ν =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow d.inclusion).edge)
    (hq : SSet.yonedaEquiv.symm q.edge ≫ ν =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow d.projection).edge)
    (hz : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject (ν.app (Opposite.op ⦋0⦌) z))) :
    ∃ t : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.RelativeVerdierDiagram ν, t.image.toVerdierSequence = d ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ t.square = SSet.yonedaEquiv.symm i.edge ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ t.square = SSet.yonedaEquiv.symm q.edge ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ t.square = SSet.yonedaEquiv.symm l.edge ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ t.square = SSet.yonedaEquiv.symm r.edge := by
  obtain ⟨F, hb, hr, hl, ht⟩ := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.exists_square_of_source_comm i q l r h
  have hbi : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ F ≫ ν =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow d.inclusion).edge := by
    rw [← Category.assoc, hb, hi]
  have hqr : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ F ≫ ν =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow d.projection).edge := by
    rw [← Category.assoc, hr, hq]
  have hFz : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex F 0 1 = z := by
    have he := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareLeftEdge_target F
    let le := SSet.Edge.ofTruncated l
    have hle : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ F = SSet.yonedaEquiv.symm le.edge := hl
    have hez : S.δ 0 (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ F)) = z := by
      rw [hle, Equiv.apply_symm_apply]
      exact le.tgt_eq
    exact he.symm.trans hez
  have hz' : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (F ≫ ν) 0 1)) := by
    change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject (ν.app _ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex F 0 1)))
    rw [hFz]
    exact hz
  exact ⟨_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.ofSquare ν d F hbi hqr hz', rfl, hb, hr, hl, ht⟩

with_weak_namespace _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.RelativeVerdierDiagram export _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory (exists_of_source_comm)


end SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
