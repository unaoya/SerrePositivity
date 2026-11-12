module
public import SerrePositivity.KST.SConstruction.PointedMappingLocalizedImage
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.PointedKanWhitehead

/-! # 点つき実ホモトピー逆からの suspension の局所化可逆性
概要：元の点つき射の実ホモトピー逆を suspension の写像空間へ移し、局所化像を可逆にする。
方針：全写像空間の成分の suspension 保存と、成分から局所化射への実写像を使う。
規約：逆は可逆性の証明にだけ使い、関手の自然な逆は定義しない。使われ方：span 左脚。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open Spectra Spectra.PointedMapping SerrePositivity.SimplicialModel
variable {D : Type v} [Category.{w} D] (L : SSet.{u} ⥤ D)
  (hL : anodyneExtensions.IsInvertedBy L)
include hL

/-- 点つき写像空間の成分で逆を持つ元の射の suspension は、局所化像で可逆。 -/
lemma suspensionImage_isIso_of_inverse_components {X Y : PointedSimplicialSet.{u}}
    (f : X ⟶ Y) (g : Y ⟶ X)
    (hfg : componentOf (f ≫ g) = componentOf (𝟙 X))
    (hgf : componentOf (g ≫ f) = componentOf (𝟙 Y)) :
    IsIso (L.map (PointedSimplicialSet.circle.{u} ◁ f).right) := by
  have h₀ := pointedMappingImage_eq_of_component L hL (componentOf_suspension hfg)
  have h₁ := pointedMappingImage_eq_of_component L hL (componentOf_suspension hgf)
  simp only [whiskerLeft_comp, whiskerLeft_id, Under.comp_right, Under.id_right,
    L.map_comp, L.map_id] at h₀ h₁
  exact ⟨⟨L.map (PointedSimplicialSet.circle.{u} ◁ g).right, h₀, h₁⟩⟩

/-- 元の点つき Kan 射の全基点 π 同型は、suspension 後にも局所化で可逆。 -/
lemma suspensionImage_isIso_of_piIsomorphism {X Y : PointedSimplicialSet.{u}}
    [KanComplex X.right] [KanComplex Y.right] (f : X ⟶ Y) (hf : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism f.right) :
    IsIso (L.map (PointedSimplicialSet.circle.{u} ◁ f).right) := by
  obtain ⟨g, ⟨HX, hX⟩, ⟨HY, hY⟩⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.exists_pointedHomotopyInverse f hf
  apply suspensionImage_isIso_of_inverse_components L hL f g
  · exact (π₀.sound (edgeOfHomotopy (f := 𝟙 X) (g := f ≫ g) HX hX)).symm
  · exact (π₀.sound (edgeOfHomotopy (f := 𝟙 Y) (g := g ≫ f) HY hY)).symm

end SerrePositivity.KST.SConstruction
