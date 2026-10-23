module

public import SerrePositivity.InfinityCategories.HomotopyLimits.RightFatConeNaturality
public import SerrePositivity.InfinityCategories.F1.Joins.JoinDiagramRightRelativeExtension
public import SerrePositivity.InfinityCategories.Core.JoinTensorInterval

/-!
概要：切断空間から固定頂点の fat join 模型への標準比較と厳密な左逆。
方針：既存の射の右パラメータでの表示を同定し、相対 join 延長で像の部分族を固定する。
規約：頂点も底の図式も高次のパラメータを含めて固定する。
使われ方：Kerodon §4.6.6、7.4.1.6、7.5.4.6 の切断側の比較の同値性の準備。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 概要：切断空間から両端固定の fat join の錐への標準比較。
方針：固定頂点の内部 Hom の錐への射と既存の fat join 比較を合成する。
規約：既存の標準射を選び直さない。
使われ方：Kerodon 7.4.1.6、7.5.4.6 の切断側の実際の比較射。 -/
noncomputable def sectionFatConeComparison {K X : SSet.{u}} (p : K ⟶ X) (x : X _⦋0⦌) :
    coherentConeSectionSpace p x ⟶ fixedEndpointFatConeSpace p x :=
  sectionFixedApexConeFamilyMap p x ≫ fixedApexFatConeComparison p x

/-- 概要：切断の普遍錐の直積上の表示は任意の族の展開と一致する。
方針：join の右直積比較の自然性と coslice の uncurry の自然性を使う。
規約：全てのパラメータ A を扱う。
使われ方：Kerodon 7.4.1.6 の標準比較の任意パラメータでの計算。 -/
lemma sectionConeFamilyUncurry_parameter {A K X : SSet.{u}} {p : K ⟶ X} {x : X _⦋0⦌}
    (f : A ⟶ coherentConeSectionSpace p x) :
    (join (Δ[0] : SSet.{u}) K ◁ f) ≫ sectionConeFamilyUncurry p x =
      joinTensorRight (Δ[0] : SSet.{u}) K A ≫ sectionConeUncurry f := by
  rw [sectionConeFamilyUncurry, ← Category.assoc, joinTensorRight_parameter, Category.assoc,
    ← sliceUnderUncurry_precomp, ← relativeFunctorUncurry_parameter, Category.comp_id]
  rfl

/-- 概要：切断の標準比較の普遍族は通常の join の右直積比較と fat join 比較を通る。
方針：fiber の包含を消去して uncurry し、パラメータへの自然性を使う。
規約：元の X の充填性を要求しない。
使われ方：Kerodon §4.6.6、7.4.1.6 の二つの図式の標準比較の同定。 -/
lemma sectionFatConeComparison_family {A K X : SSet.{u}} {p : K ⟶ X} {x : X _⦋0⦌}
    (f : A ⟶ coherentConeSectionSpace p x) :
    fixedFatConeFamily (f ≫ sectionFatConeComparison p x) =
      (fatJoinComparison (Δ[0] : SSet.{u}) K ▷ A) ≫
        joinTensorRight (Δ[0] : SSet.{u}) K A ≫ sectionConeUncurry f := by
  change uncurry ((f ≫ curry (sectionConeFamilyUncurry p x)) ≫
    (pre (fatJoinComparison (Δ[0] : SSet.{u}) K)).app X) = _
  rw [uncurry_pre_app, uncurry_natural_left, uncurry_curry,
    sectionConeFamilyUncurry_parameter]

/-- 概要：切断の標準比較を右パラメータの図式へ展開すると、元の join 図式の標準 fat join 比較。
方針：左端と右直積比較への引き戻しで決定し、二つの右直積比較の可換性を使う。
規約：射の等式として任意の族を扱う。
使われ方：Kerodon §4.6.6、7.4.1.6 の相対 join 延長の部分族上の一致条件。 -/
lemma sectionFatConeComparison_diagram {A K X : SSet.{u}} {p : K ⟶ X} {x : X _⦋0⦌}
    (f : A ⟶ coherentConeSectionSpace p x) :
    rightFatConeDiagram (f ≫ sectionFatConeComparison p x) =
      fatJoinComparison (Δ[0] : SSet.{u}) (K ⊗ A) ≫ sectionConeUncurry f := by
  apply fatJoinTensorRight_hom_ext
  · rw [rightFatConeDiagram_inl, ← Category.assoc, fatJoinInl_comparison,
      sectionConeUncurry_inl]
  · rw [rightFatConeDiagram_family, sectionFatConeComparison_family,
      ← Category.assoc, ← fatJoinTensorRight_comparison, Category.assoc]

/-- 概要：切断空間から両端固定の fat join 模型への標準比較は単射。
方針：右パラメータの図式の同定の後で fat join 比較のエピ性と切断の展開の単射性を使う。
規約：充填性の仮定は不要。
使われ方：Kerodon §4.6.6 の比較の像の部分族を固定するための仮定。 -/
instance sectionFatConeComparison_mono {K X : SSet.{u}} (p : K ⟶ X) (x : X _⦋0⦌) :
    Mono (sectionFatConeComparison p x) := by
  constructor
  intro A f g h
  apply sectionConeUncurry_injective p x
  apply (cancel_epi (fatJoinComparison (Δ[0] : SSet.{u}) (K ⊗ A))).mp
  rw [← sectionFatConeComparison_diagram, ← sectionFatConeComparison_diagram, h]

/-- 概要：切断空間から固定頂点の fat join 模型への標準比較には厳密な左逆がある。
方針：右因子の部分族を相対 join 延長で固定し、両端を保った図式を切断空間へ curry する。
規約：K は任意、X の quasicategory 性だけを仮定する。
使われ方：Kerodon §4.6.6、7.4.1.6 の切断側の比較の同値性の単位の構成。 -/
lemma sectionFatConeComparison_exists_retraction {K X : SSet.{u}} [Quasicategory X]
    (p : K ⟶ X) (x : X _⦋0⦌) :
    ∃ r : fixedEndpointFatConeSpace p x ⟶ coherentConeSectionSpace p x,
      sectionFatConeComparison p x ≫ r = 𝟙 _ := by
  let S := coherentConeSectionSpace p x
  let B := fixedEndpointFatConeSpace p x
  let c := sectionFatConeComparison p x
  let F := rightFatConeDiagram (𝟙 B)
  let G := sectionConeUncurry (𝟙 S)
  have hFG : fatJoinMap (𝟙 (Δ[0] : SSet.{u})) (K ◁ c) ≫ F =
      fatJoinComparison (Δ[0] : SSet.{u}) (K ⊗ S) ≫ G := by
    rw [← rightFatConeDiagram_precomp, Category.comp_id]
    simpa only [Category.id_comp] using sectionFatConeComparison_diagram (𝟙 S)
  have : Mono (K ◁ c) := (tensorLeft K).map_mono c
  obtain ⟨H, hH, hp, hx⟩ := exists_joinDiagram_right_relative_extension (K ◁ c) F G hFG
  have hx' : joinInl (Δ[0] : SSet.{u}) (K ⊗ B) ≫ H = SSet.yonedaEquiv.symm x :=
    hx.trans (rightFatConeDiagram_inl (𝟙 B))
  have hp' : joinInr (Δ[0] : SSet.{u}) (K ⊗ B) ≫ H = fst K B ≫ p :=
    hp.trans (rightFatConeDiagram_inr (𝟙 B))
  refine ⟨sectionConeCurry H hx' hp', ?_⟩
  apply sectionConeUncurry_injective p x
  rw [sectionConeUncurry_precomp, sectionConeUncurry_curry]
  exact hH

end SerrePositivity.InfinityCategories.HomotopyLimits
