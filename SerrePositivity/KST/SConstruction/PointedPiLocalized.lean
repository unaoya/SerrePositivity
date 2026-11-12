module
public import SerrePositivity.KST.SConstruction.LocalizedPiComparison
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.PointedKanWhitehead

/-! # 点つき Kan 射の π 同型から局所化同型への回収
概要：全基点 π 同型の点つき Kan 射は anodyne 局所化で可逆になる。
方針：既存の Whitehead の実ホモトピー逆を局所化へ写す。
規約：標準三公理のみ。使われ方：元の零行 loop の同型性を元の随伴射へ移す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open SerrePositivity.SimplicialModel

/-- 全基点 π 同型の点つき Kan 射は元の anodyne 局所化で可逆。 -/
lemma pointed_localized_isIso_of_piIsomorphism {A B : PointedSimplicialSet.{u}}
    [KanComplex A.right] [KanComplex B.right] (f : A ⟶ B)
    (hf : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism f.right) :
    IsIso (AnodyneHomotopy.anodyneQ.map f.right) := by
  let Q := AnodyneHomotopy.anodyneQ
  obtain ⟨g, ⟨H, _⟩, ⟨G, _⟩⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.exists_pointedHomotopyInverse f hf
  have hH := AnodyneHomotopy.map_homotopy_eq Q (Localization.inverts Q anodyneExtensions) H
  have hG := AnodyneHomotopy.map_homotopy_eq Q (Localization.inverts Q anodyneExtensions) G
  change Q.map (𝟙 A.right) = Q.map (f.right ≫ g.right) at hH
  change Q.map (𝟙 B.right) = Q.map (g.right ≫ f.right) at hG
  rw [Q.map_id] at hH hG
  exact ⟨⟨Q.map g.right,
    (Q.map_comp _ _).symm.trans hH.symm, (Q.map_comp _ _).symm.trans hG.symm⟩⟩

end SerrePositivity.KST.SConstruction
