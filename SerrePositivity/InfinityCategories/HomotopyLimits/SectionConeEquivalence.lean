module

public import SerrePositivity.InfinityCategories.HomotopyLimits.SectionFatConeComparison
public import SerrePositivity.InfinityCategories.HomotopyLimits.RightFatConeHomotopy

/-!
概要：固定頂点の coslice の切断空間と内部 Hom の錐の共通模型の標準比較の同値性。
方針：右因子の図式を両端固定の join 比較で回収し、ホモトピー右逆と厳密な左逆を合わせる。
規約：切断空間からの実際の標準射について証明する。
使われ方：Kerodon 4.6.6.8、7.4.1.6、7.5.4.6 の錐の頂点 fiber と切断空間の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 概要：共通模型への任意の族は切断空間の族の像としてホモトピーまで回収できる。
方針：右パラメータの図式を両端固定の join 図式へ移し、切断へ curry してホモトピーも戻す。
規約：パラメータ A と図式 K は任意、X の quasicategory 性だけを要求する。
使われ方：Kerodon §4.6.6、7.4.1.6 の切断側の比較のホモトピー右逆。 -/
lemma sectionFatConeComparison_exists_homotopy {A K X : SSet.{u}} [Quasicategory X]
    {p : K ⟶ X} {x : X _⦋0⦌} (a : A ⟶ fixedEndpointFatConeSpace p x) :
    ∃ b : A ⟶ coherentConeSectionSpace p x,
      Nonempty (SSet.Homotopy (b ≫ sectionFatConeComparison p x) a) := by
  let F := rightFatConeDiagram a
  obtain ⟨G, hG, H, hH, _⟩ := exists_joinDiagram_of_fatJoinDiagram
    (fatJoinEndpointInclusion (Δ[0] : SSet.{u}) (K ⊗ A) ≫ F) F rfl
  have hx : joinInl (Δ[0] : SSet.{u}) (K ⊗ A) ≫ G = SSet.yonedaEquiv.symm x := by
    have h := congrArg (fun z ↦ joinEndpointInl (Δ[0] : SSet.{u}) (K ⊗ A) ≫ z) hG
    simpa only [← Category.assoc, joinEndpointInl_inclusion, joinEndpointInl_fatInclusion,
      F, rightFatConeDiagram_inl] using h
  have hp : joinInr (Δ[0] : SSet.{u}) (K ⊗ A) ≫ G = fst K A ≫ p := by
    have h := congrArg (fun z ↦ joinEndpointInr (Δ[0] : SSet.{u}) (K ⊗ A) ≫ z) hG
    simpa only [← Category.assoc, joinEndpointInr_inclusion, joinEndpointInr_fatInclusion,
      F, rightFatConeDiagram_inr] using h
  let b := sectionConeCurry G hx hp
  have hF : rightFatConeDiagram (b ≫ sectionFatConeComparison p x) =
      fatJoinComparison (Δ[0] : SSet.{u}) (K ⊗ A) ≫ G := by
    rw [sectionFatConeComparison_diagram, sectionConeUncurry_curry]
  have hxH : (fatJoinInl (Δ[0] : SSet.{u}) (K ⊗ A) ▷ Δ[1]) ≫ H.h =
      fst (Δ[0] : SSet.{u}) Δ[1] ≫ SSet.yonedaEquiv.symm x := by
    have hh := congrArg (fun z ↦
      (joinEndpointInl (Δ[0] : SSet.{u}) (K ⊗ A) ▷ Δ[1]) ≫ z) hH
    change (fatJoinInl (Δ[0] : SSet.{u}) (K ⊗ A) ▷ Δ[1]) ≫ H.h =
      fst (Δ[0] : SSet.{u}) Δ[1] ≫ fatJoinInl Δ[0] (K ⊗ A) ≫ F at hh
    rw [rightFatConeDiagram_inl] at hh
    exact hh
  have hpH : (fatJoinInr (Δ[0] : SSet.{u}) (K ⊗ A) ▷ Δ[1]) ≫ H.h =
      fst (K ⊗ A) Δ[1] ≫ fst K A ≫ p := by
    have hh := congrArg (fun z ↦
      (joinEndpointInr (Δ[0] : SSet.{u}) (K ⊗ A) ▷ Δ[1]) ≫ z) hH
    change (fatJoinInr (Δ[0] : SSet.{u}) (K ⊗ A) ▷ Δ[1]) ≫ H.h =
      fst (K ⊗ A) Δ[1] ≫ fatJoinInr Δ[0] (K ⊗ A) ≫ F at hh
    rw [rightFatConeDiagram_inr] at hh
    exact hh
  let H' : SSet.Homotopy (rightFatConeDiagram (b ≫ sectionFatConeComparison p x))
      (rightFatConeDiagram a) :=
    { h := H.h
      h₀ := H.h₀.trans hF.symm
      h₁ := H.h₁
      rel := by
        apply SSet.hom_ext
        intro d
        apply ConcreteCategory.hom_ext
        intro z
        exact False.elim z.1.property }
  exact ⟨b, ⟨rightFatConeHomotopyOfDiagram (b ≫ sectionFatConeComparison p x) a H'
    hxH hpH⟩⟩

/-- 概要：切断空間から固定頂点の fat join 模型への標準比較は圏同値。
方針：厳密な左逆と恒等族のホモトピー右逆を、Kan な標的の関手の同型で合わせる。
規約：K は任意、X に quasicategory 性だけを要求する。
使われ方：Kerodon §4.6.6、7.4.1.6 の切断側の共通模型への同値。 -/
lemma sectionFatConeComparison_isQCatEquivalence {K X : SSet.{u}} [Quasicategory X]
    (p : K ⟶ X) (x : X _⦋0⦌) : IsQCatEquivalence (sectionFatConeComparison p x) := by
  obtain ⟨r, hr⟩ := sectionFatConeComparison_exists_retraction p x
  obtain ⟨b, ⟨H⟩⟩ := sectionFatConeComparison_exists_homotopy
    (𝟙 (fixedEndpointFatConeSpace p x))
  exact isQCatEquivalence_of_retraction_of_rightInverseIso _ r b hr
    (functorIsoOfSimplicialHomotopy H)

/-- 概要：切断空間から内部 Hom の固定頂点の錐への標準比較は圏同値。
方針：fat join への合成と後段の比較の同値性から二対三則を適用する。
規約：実際の sectionFixedApexConeFamilyMap の性質を述べる。
使われ方：Kerodon 4.6.6.8、7.4.1.6、7.5.4.6 の切断空間と錐の頂点 fiber の比較。 -/
lemma sectionFixedApexConeFamilyMap_isQCatEquivalence {K X : SSet.{u}} [Quasicategory X]
    (p : K ⟶ X) (x : X _⦋0⦌) : IsQCatEquivalence (sectionFixedApexConeFamilyMap p x) :=
  (fixedApexFatConeComparison_isQCatEquivalence p x).cancel_right
    (sectionFatConeComparison_isQCatEquivalence p x)

/-- 概要：切断空間から内部 Hom の固定頂点の錐への標準比較はホモトピー同値。
方針：両模型の Kan 性と圏同値性を使う。
規約：図式 K の quasicategory 性や非空性は要求しない。
使われ方：Kerodon 7.4.1.6、7.5.4.6 の ∞ 極限の表現可能な判定の終域の移送。 -/
lemma sectionFixedApexConeFamilyMap_homotopyEquivalence {K X : SSet.{u}} [Quasicategory X]
    (p : K ⟶ X) (x : X _⦋0⦌) :
    IsSimplicialHomotopyEquivalence (sectionFixedApexConeFamilyMap p x) :=
  (sectionFixedApexConeFamilyMap_isQCatEquivalence p x).isSimplicialHomotopyEquivalence

/-- 概要：錐の slice の頂点 fiber と coslice の切断空間は同値。
方針：内部 Hom の固定頂点の錐への二つの標準比較の同値を合成する。
規約：切断側の逆の選択を含む圏同値を返す。
使われ方：Kerodon 7.4.1.6、7.5.4.6 の ∞ 極限の写像空間と切断空間の接続。 -/
noncomputable def coneVertexFiberSectionEquivalence {K X : SSet.{u}} [Quasicategory X]
    (p : K ⟶ X) (x : X _⦋0⦌) :
    QCatEquivalence (vertexFiber (sliceOverProjection p) x) (coherentConeSectionSpace p x) :=
  (coneVertexFiberFamilyMap_isQCatEquivalence p x).choose.trans
    (sectionFixedApexConeFamilyMap_isQCatEquivalence p x).choose.symm

end SerrePositivity.InfinityCategories.HomotopyLimits
