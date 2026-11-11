module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.SectionFatConeComparison
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.RightFatConeHomotopy

/-!
概要：固定頂点の coslice の切断空間と内部 Hom の錐の共通模型の標準比較の同値性。
方針：右因子の図式を両端固定の join 比較で回収し、ホモトピー右逆と厳密な左逆を合わせる。
規約：切断空間からの実際の標準射について証明する。
使われ方：Kerodon 4.6.6.8（Tag 04J5）、7.4.1.6（Tag 05QS）、7.5.4.6（Tag 03BB） の錐の頂点 fiber と切断空間の比較。

対応節は Kerodon 7.4（Tag 02SX）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces

/-- 概要：共通模型への任意の族は切断空間の族の像としてホモトピーまで回収できる。
方針：右パラメータの図式を両端固定の join 図式へ移し、切断へ curry してホモトピーも戻す。
規約：パラメータ A と図式 K は任意、X の quasicategory 性だけを要求する。
使われ方：Kerodon §4.6.6（Tag 04HY）、7.4.1.6（Tag 05QS） の切断側の比較のホモトピー右逆。 -/
lemma sectionFatConeComparison_exists_homotopy {A K X : SSet.{u}} [Quasicategory X]
    {p : K ⟶ X} {x : X _⦋0⦌} (a : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedEndpointFatConeSpace p x) :
    ∃ b : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coherentConeSectionSpace p x,
      Nonempty (SSet.Homotopy (b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.sectionFatConeComparison p x) a) := by
  let F := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightFatConeDiagram a
  obtain ⟨G, hG, H, hH, _⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.exists_joinDiagram_of_fatJoinDiagram
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinEndpointInclusion (Δ[0] : SSet.{u}) (K ⊗ A) ≫ F) F rfl
  have hx : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{u}) (K ⊗ A) ≫ G = SSet.yonedaEquiv.symm x := by
    have h := congrArg (fun z ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointInl (Δ[0] : SSet.{u}) (K ⊗ A) ≫ z) hG
    simpa only [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointInl_inclusion, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointInl_fatInclusion,
      F, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightFatConeDiagram_inl] using h
  have hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[0] : SSet.{u}) (K ⊗ A) ≫ G = fst K A ≫ p := by
    have h := congrArg (fun z ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointInr (Δ[0] : SSet.{u}) (K ⊗ A) ≫ z) hG
    simpa only [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointInr_inclusion, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointInr_fatInclusion,
      F, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightFatConeDiagram_inr] using h
  let b := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.sectionConeCurry G hx hp
  have hF : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightFatConeDiagram (b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.sectionFatConeComparison p x) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinComparison (Δ[0] : SSet.{u}) (K ⊗ A) ≫ G := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.sectionFatConeComparison_diagram, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.sectionConeUncurry_curry]
  have hxH : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl (Δ[0] : SSet.{u}) (K ⊗ A) ▷ Δ[1]) ≫ H.h =
      fst (Δ[0] : SSet.{u}) Δ[1] ≫ SSet.yonedaEquiv.symm x := by
    have hh := congrArg (fun z ↦
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointInl (Δ[0] : SSet.{u}) (K ⊗ A) ▷ Δ[1]) ≫ z) hH
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl (Δ[0] : SSet.{u}) (K ⊗ A) ▷ Δ[1]) ≫ H.h =
      fst (Δ[0] : SSet.{u}) Δ[1] ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl Δ[0] (K ⊗ A) ≫ F at hh
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightFatConeDiagram_inl] at hh
    exact hh
  have hpH : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr (Δ[0] : SSet.{u}) (K ⊗ A) ▷ Δ[1]) ≫ H.h =
      fst (K ⊗ A) Δ[1] ≫ fst K A ≫ p := by
    have hh := congrArg (fun z ↦
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointInr (Δ[0] : SSet.{u}) (K ⊗ A) ▷ Δ[1]) ≫ z) hH
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr (Δ[0] : SSet.{u}) (K ⊗ A) ▷ Δ[1]) ≫ H.h =
      fst (K ⊗ A) Δ[1] ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr Δ[0] (K ⊗ A) ≫ F at hh
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightFatConeDiagram_inr] at hh
    exact hh
  let H' : SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightFatConeDiagram (b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.sectionFatConeComparison p x))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightFatConeDiagram a) :=
    { h := H.h
      h₀ := H.h₀.trans hF.symm
      h₁ := H.h₁
      rel := by
        apply SSet.hom_ext
        intro d
        apply ConcreteCategory.hom_ext
        intro z
        exact False.elim z.1.property }
  exact ⟨b, ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightFatConeHomotopyOfDiagram (b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.sectionFatConeComparison p x) a H'
    hxH hpH⟩⟩

/-- 概要：切断空間から固定頂点の fat join 模型への標準比較は圏同値。
方針：厳密な左逆と恒等族のホモトピー右逆を、Kan な標的の関手の同型で合わせる。
規約：K は任意、X に quasicategory 性だけを要求する。
使われ方：Kerodon §4.6.6（Tag 04HY）、7.4.1.6（Tag 05QS） の切断側の共通模型への同値。 -/
lemma sectionFatConeComparison_isQCatEquivalence {K X : SSet.{u}} [Quasicategory X]
    (p : K ⟶ X) (x : X _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.sectionFatConeComparison p x) := by
  obtain ⟨r, hr⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.sectionFatConeComparison_exists_retraction p x
  obtain ⟨b, ⟨H⟩⟩ := sectionFatConeComparison_exists_homotopy
    (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedEndpointFatConeSpace p x))
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_retraction_of_rightInverseIso _ r b hr
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorIsoOfSimplicialHomotopy H)

/-- 概要：切断空間から内部 Hom の固定頂点の錐への標準比較は圏同値。
方針：fat join への合成と後段の比較の同値性から二対三則を適用する。
規約：実際の sectionFixedApexConeFamilyMap の性質を述べる。
使われ方：Kerodon 4.6.6.8（Tag 04J5）、7.4.1.6（Tag 05QS）、7.5.4.6（Tag 03BB） の切断空間と錐の頂点 fiber の比較。 -/
lemma sectionFixedApexConeFamilyMap_isQCatEquivalence {K X : SSet.{u}} [Quasicategory X]
    (p : K ⟶ X) (x : X _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.sectionFixedApexConeFamilyMap p x) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedApexFatConeComparison_isQCatEquivalence p x).cancel_right
    (sectionFatConeComparison_isQCatEquivalence p x)

/-- 概要：切断空間から内部 Hom の固定頂点の錐への標準比較はホモトピー同値。
方針：両模型の Kan 性と圏同値性を使う。
規約：図式 K の quasicategory 性や非空性は要求しない。
使われ方：Kerodon 7.4.1.6（Tag 05QS）、7.5.4.6（Tag 03BB） の ∞ 極限の表現可能な判定の終域の移送。 -/
lemma sectionFixedApexConeFamilyMap_homotopyEquivalence {K X : SSet.{u}} [Quasicategory X]
    (p : K ⟶ X) (x : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.sectionFixedApexConeFamilyMap p x) :=
  (sectionFixedApexConeFamilyMap_isQCatEquivalence p x).isSimplicialHomotopyEquivalence

/-- 概要：錐の slice の頂点 fiber と coslice の切断空間は同値。
方針：内部 Hom の固定頂点の錐への二つの標準比較の同値を合成する。
規約：切断側の逆の選択を含む圏同値を返す。
使われ方：Kerodon 7.4.1.6（Tag 05QS）、7.5.4.6（Tag 03BB） の ∞ 極限の写像空間と切断空間の接続。 -/
noncomputable def coneVertexFiberSectionEquivalence {K X : SSet.{u}} [Quasicategory X]
    (p : K ⟶ X) (x : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection p) x) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coherentConeSectionSpace p x) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coneVertexFiberFamilyMap_isQCatEquivalence p x).choose.trans
    (sectionFixedApexConeFamilyMap_isQCatEquivalence p x).choose.symm

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
