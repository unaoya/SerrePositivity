module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.SmallSimplicialShapes
public import Mathlib.CategoryTheory.Subfunctor.Image

/-!
概要：単射な単体写像の像は、元の形状と同じ κ-small 性を持つ。
方針：像への因子写像の同型から非退化単体の全単射を得る。
規約：κ の正則性は不要。単射性は全次数での単射性。
使われ方：埋め込まれた小さい錐を小さい部分複体として扱う。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories

/-- 同型な形状の κ-small 性は一致する。 -/
lemma isKappaSmall_iff_of_iso {κ : Cardinal.{u}} {K L : SSet.{u}} (e : K ≅ L) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall κ K ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall κ L := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall
  rw [Cardinal.mk_congr (N.orderIsoOfIso e).toEquiv]

/-- 単射な写像の像は元の形状と同じ小ささを持つ。 -/
lemma isKappaSmall_range_of_mono {κ : Cardinal.{u}} {K L : SSet.{u}}
    (f : K ⟶ L) [Mono f] (hK : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall κ K) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall κ (Subcomplex.range f).toSSet :=
  (isKappaSmall_iff_of_iso (asIso (Subfunctor.toRange f))).mp hK

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
