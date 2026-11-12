module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.TerminalKanColimit
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.LeftKanHomComposition

/-!
概要：元の全余極限を、一点の nerve への指定左 Kan 拡張として比較する。
方針：全ての局所添字の射影が同型であることから、F1B の局所存在定理を使う。
規約：一点の対象と射は同じ宇宙 u。余極限存在を Kan 普遍性の仮定に置き換えない。
使われ方：左 Kan 拡張を経由する二つの既存余極限の頂点比較。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 一点の通常の圏の指定対象は終対象。 -/
def pointKanTerminal (t : PUnit.{u + 1}) : IsTerminal t :=
  IsTerminal.ofUniqueHom (fun x ↦ homOfLE (le_of_eq (Subsingleton.elim x t)))
    (fun _ _ ↦ Subsingleton.elim _ _)

/-- 元の全図式の余極限が存在すれば、一点への任意の射に沿う左 Kan 拡張が存在する。 -/
lemma exists_pointLeftKanExtension {K X : SSet.{u}} [Quasicategory K] [Quasicategory X]
    (p : K ⟶ nerve PUnit.{u + 1}) (F : K ⟶ X) (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit F) :
    ∃ (G : nerve PUnit.{u + 1} ⟶ X) (β : SSet.Homotopy F (p ≫ G)),
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsLeftKanExtension p F G β := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.exists_kanLeftExtension_of_local_colimits p F
  intro v
  obtain ⟨t, rfl⟩ := nerveEquiv.symm.surjective v
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftKanDiagram_nerveTerminal_hasColimit (pointKanTerminal t) p F hF

/-- 左 Kan 延長の前後で既に存在する二つの全余極限の頂点は同型。 -/
def leftKan_colimitVertexIso {A B X : SSet.{u}}
    [Quasicategory A] [Quasicategory B] [Quasicategory X]
    (p : A ⟶ B) {F : A ⟶ X} {G : B ⟶ X}
    (β : SSet.Homotopy F (p ≫ G)) (hβ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsLeftKanExtension p F G β)
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone F) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c)
    (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone G) (hd : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone d) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso d.vertex c.vertex := by
  apply Classical.choice
  let q : B ⟶ nerve PUnit.{u + 1} := SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex PUnit.unit)
  obtain ⟨L, α, hα⟩ := exists_pointLeftKanExtension q G ⟨d, hd⟩
  obtain ⟨M, γ, hγ⟩ := exists_pointLeftKanExtension (p ≫ q) F ⟨c, hc⟩
  let b := SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy β)
  let a := SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy α)
  let g := SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy γ)
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanHomUniversalIso (p ≫ q) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftKanCompositeUnit p q b a) g
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftKanHomUniversal_comp p q b a (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftKanExtension_homUniversal p β hβ)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftKanExtension_homUniversal q α hα))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftKanExtension_homUniversal (p ≫ q) γ hγ)
  obtain ⟨cG, hcG, hvG⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftKan_nerveTerminal_colimitValue (pointKanTerminal PUnit.unit) hα
  obtain ⟨cF, hcF, hvF⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftKan_nerveTerminal_colimitValue (pointKanTerminal PUnit.unit) hγ
  have ev : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso cG.vertex cF.vertex := by
    rw [hvG, hvF]
    exact e.toNatIso.app (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex PUnit.unit))
  exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitVertexIso d cG hd hcG ≪≫ ev ≪≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitVertexIso cF c hcF hc⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
