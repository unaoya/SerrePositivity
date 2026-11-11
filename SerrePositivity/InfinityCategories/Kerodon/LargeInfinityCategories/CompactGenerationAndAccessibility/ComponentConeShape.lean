module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.OrdinalPrefixes
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinTensorPoint

/-!
概要：現在の成分の閉前置形状を、厳密前置形状への一頂点追加と同定する。
方針：固定成分位置の順序判定と元の posetLowerJoinIso を合成する。
規約：左境界は元の成分包含、右境界は同じ追加頂点。
使われ方：元の表示添字の延長余錐を次の全閉前置段へ戻す。

対応節は Kerodon 9.4（Tag 06GT）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility

/-- 概要：同値な頂点述語の部分順序 nerve を厳密に同型にする。
方針：同じ元の点を両方向へ送る。
規約：順射と元の値を保持する。
使われ方：同じ成分の前置形状の表示変更。 -/
def nerveSubtypeIso {I : Type u} [Preorder I] (P Q : I → Prop)
    (h : ∀ i, P i ↔ Q i) : nerve {i : I // P i} ≅ nerve {i : I // Q i} where
  hom := nerveMap (⟨fun i ↦ ⟨i.val, (h i.val).mp i.property⟩, fun _ _ h ↦ h⟩ :
    {i : I // P i} →o {i : I // Q i}).toFunctor
  inv := nerveMap (⟨fun i ↦ ⟨i.val, (h i.val).mpr i.property⟩, fun _ _ h ↦ h⟩ :
    {i : I // Q i} →o {i : I // P i}).toFunctor
  hom_inv_id := rfl
  inv_hom_id := rfl

/-- 概要：同じ色の交互位置の厳密順序は元の段の厳密順序。
方針：辞書式順序を展開する。
規約：元の色を固定する。
使われ方：厳密成分前置形状の同定。 -/
lemma sameComponent_lt (κ : Cardinal.{u}) (a b : κ.ord.ToType) (c : Fin 2) :
    toLex (a, c) < toLex (b, c) ↔ a < b := by
  simp only [Prod.Lex.toLex_lt_toLex, lt_self_iff_false, and_false, or_false]

/-- 概要：同じ色の交互位置の弱順序は元の段の弱順序。
方針：辞書式順序を展開する。
規約：元の色を固定する。
使われ方：閉成分前置形状の同定。 -/
lemma sameComponent_le (κ : Cardinal.{u}) (a b : κ.ord.ToType) (c : Fin 2) :
    toLex (a, c) ≤ toLex (b, c) ↔ a ≤ b := by
  rw [Prod.Lex.toLex_le_toLex]
  constructor
  · rintro (h | ⟨rfl, _⟩)
    · exact h.le
    · exact le_rfl
  · intro h
    exact h.lt_or_eq.elim Or.inl (fun h ↦ Or.inr ⟨h, le_rfl⟩)

/-- 概要：同じ成分の閉前置形状は、厳密前置形状へ現在の一頂点を加えた形状と同型。
方針：成分位置の順序判定で通常の下方形状へ移し、元の順序余錐同型を使う。
規約：元の追加頂点を保持する厳密な形状同型。
使われ方：元の表示添字の延長余錐を閉成分図式へ移す。 -/
def componentConeIso (κ : Cardinal.{u}) (a : κ.ord.ToType) (c : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (nerve (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AlternatingComponentLower κ (toLex (a, c)) c)) Δ[0] ≅
      nerve (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AlternatingComponentClosed κ (toLex (a, c)) c) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinIso (nerveSubtypeIso _ _ (fun b ↦ sameComponent_lt κ b a c)) (Iso.refl Δ[0]) ≪≫
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.posetLowerJoinIso a ≪≫
      (nerveSubtypeIso _ _ (fun b ↦ sameComponent_le κ b a c)).symm

/-- 概要：成分余錐形状同型の左境界は元の同じ成分包含。
方針：join の左境界と元の順序余錐同型の左境界を合成する。
規約：全単体上の厳密な等式。
使われ方：元の成分前置図式を保持する制限条件。 -/
lemma componentConeIso_inl (κ : Cardinal.{u}) (a : κ.ord.ToType) (c : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl _ Δ[0] ≫ (componentConeIso κ a c).hom =
      nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.alternatingComponentLowerToClosed κ (toLex (a, c)) c) := by
  dsimp only [componentConeIso, Iso.trans_hom, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinIso, Iso.refl_hom, Iso.symm_hom]
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap, Category.assoc, ← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl _ _),
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.posetLowerJoinIso_inl]
  rfl

/-- 概要：成分余錐形状同型の右境界は元の追加頂点。
方針：join の右境界と元の順序余錐同型の右境界を使う。
規約：同じ元の順序段を固定する。
使われ方：追加した表示段の頂点の回収。 -/
lemma componentConeIso_inr (κ : Cardinal.{u}) (a : κ.ord.ToType) (c : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr _ Δ[0] ≫ (componentConeIso κ a c).hom =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (⟨a, (sameComponent_le κ a a c).mpr le_rfl⟩ :
        _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AlternatingComponentClosed κ (toLex (a, c)) c) := by
  dsimp only [componentConeIso, Iso.trans_hom, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinIso, Iso.refl_hom, Iso.symm_hom]
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap, Category.id_comp, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.posetLowerJoinIso_inr]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility
