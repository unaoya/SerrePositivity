module

public import SerrePositivity.InfinityCategories.HomotopyLimits.ConeDiagramRestriction
public import SerrePositivity.InfinityCategories.HomotopyLimits.ConeDiagramTensor
public import SerrePositivity.InfinityCategories.HomotopyLimits.SectionConeEquivalence

/-!
概要：coslice の切断から両端固定の錐への標準比較は図式の制限と可換である。
方針：包含後の uncurry を普遍族で計算し、join と直積の自然性を使う。
規約：選択した逆同値の自然性は使わず、実際の標準比較を追跡する。
使われ方：HTT 4.2.4.1、Kerodon 7.4.1.6 の極限検出の模型の移送。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 概要：coslice の切断を両端固定の錐の空間へ写す標準比較。
方針：固定頂点の内部 Hom の錐への比較に二重 fiber の同型を合成する。
規約：図式と頂点を全次数で固定する。
使われ方：Kerodon 7.4.1.6 の制限の可換四角形の切断側。 -/
noncomputable def sectionEndpointConeComparison {K X : SSet.{u}} (p : K ⟶ X)
    (x : X _⦋0⦌) : coherentConeSectionSpace p x ⟶ fixedEndpointConeSpace p x :=
  sectionFixedApexConeFamilyMap p x ≫ (fixedApexEndpointConeSpaceIso p x).hom

/-- 概要：切断からの標準比較を展開すると、右パラメータ付き join の図式になる。
方針：二つの fiber の包含と curry の往復を計算する。
規約：任意のパラメータ A について述べる。
使われ方：Kerodon 7.4.1.6 の実際の比較の自然性の検査。 -/
lemma sectionEndpointConeComparison_uncurry {A K X : SSet.{u}} {p : K ⟶ X}
    {x : X _⦋0⦌} (s : A ⟶ coherentConeSectionSpace p x) :
    uncurry (s ≫ sectionEndpointConeComparison p x ≫ endpointConeEvaluation p x) =
      joinTensorRight Δ[0] K A ≫ sectionConeUncurry s := by
  change uncurry (s ≫ (sectionFixedApexConeFamilyMap p x ≫
    (fixedApexToEndpointConeSpace p x ≫ endpointConeEvaluation p x))) = _
  rw [fixedApexToEndpointConeSpace, vertexFiberLift_ι]
  change uncurry (s ≫ (sectionFixedApexConeFamilyMap p x ≫
    (vertexFiberι (coneFamilyApex p) x ≫
      vertexFiberι (coneRestriction K X) (functorVertex p)))) = _
  rw [← Category.assoc (sectionFixedApexConeFamilyMap p x),
    sectionFixedApexConeFamilyMap, vertexFiberLift_ι, sectionConeFamilyMap,
    vertexFiberLift_ι, uncurry_natural_left, uncurry_curry]
  unfold sectionConeFamilyUncurry sectionConeUncurry
  rw [← Category.assoc, joinTensorRight_parameter, Category.assoc,
    ← sliceUnderUncurry_precomp, ← relativeFunctorUncurry_parameter, Category.comp_id]

/-- 概要：切断からの標準比較は図式の射に沿う制限と可換。
方針：両端固定の fiber の包含後に uncurry し、二つの自然性を合わせる。
規約：K、J、X は任意で、図式に strict 性や充填性は要求しない。
使われ方：HTT 4.2.4.1 の native な極限判定から切断の制限への移送。 -/
lemma sectionEndpointConeComparison_restrict {K J X : SSet.{u}} (p : J ⟶ X)
    (x : X _⦋0⦌) (f : K ⟶ J) :
    relativeFunctorPre (sliceUnderProjection (SSet.yonedaEquiv.symm x)) p f ≫
        sectionEndpointConeComparison (f ≫ p) x =
      sectionEndpointConeComparison p x ≫ endpointConeRestrict p x f := by
  apply vertexFiber_hom_ext
    ((pre (joinEndpointInclusion (Δ[0] : SSet.{u}) K)).app X)
    (functorVertex (joinEndpointDesc (SSet.yonedaEquiv.symm x) (f ≫ p)))
  change (_ ≫ sectionEndpointConeComparison (f ≫ p) x) ≫
      endpointConeEvaluation (f ≫ p) x =
    (sectionEndpointConeComparison p x ≫ endpointConeRestrict p x f) ≫
      endpointConeEvaluation (f ≫ p) x
  rw [Category.assoc, Category.assoc, endpointConeRestrict_evaluation, ← Category.assoc]
  apply uncurry_injective
  rw [Category.assoc, sectionEndpointConeComparison_uncurry]
  have hr := sectionConeUncurry_restrict
    (p := p) (x := x) (𝟙 (coherentConeSectionSpace p x)) f
  simp only [Category.id_comp] at hr
  rw [hr, ← Category.assoc (sectionEndpointConeComparison p x), uncurry_pre_app]
  have he := sectionEndpointConeComparison_uncurry
    (p := p) (x := x) (𝟙 (coherentConeSectionSpace p x))
  simp only [Category.id_comp] at he
  rw [he, ← Category.assoc, ← joinTensorRight_diagram, Category.assoc]

/-- 概要：quasicategory では切断から両端固定の錐への標準比較はホモトピー同値。
方針：既存の切断比較の同値性と二重 fiber の厳密な同型を合成する。
規約：図式の始域 K は任意。
使われ方：Kerodon 7.4.1.6 の制限の可換四角形の同値辺。 -/
lemma sectionEndpointConeComparison_homotopyEquivalence {K X : SSet.{u}}
    [Quasicategory X] (p : K ⟶ X) (x : X _⦋0⦌) :
    IsSimplicialHomotopyEquivalence (sectionEndpointConeComparison p x) := by
  have := fixedEndpointConeSpace_kanComplex p x
  exact ((sectionFixedApexConeFamilyMap_isQCatEquivalence p x).comp
    (qCatEquivalenceOfIso (fixedApexEndpointConeSpaceIso p x)).isQCatEquivalence
      ).isSimplicialHomotopyEquivalence

/-- 概要：切断の制限のホモトピー同値性は両端固定の錐の制限で検出できる。
方針：実際の標準比較の可換四角形と二対三則を使う。
規約：X の quasicategory 性以外の充填性は要求しない。
使われ方：HTT 4.2.4.1 の native な極限判定の切断側への移送。 -/
lemma sectionRestriction_homotopyEquivalence_iff_endpoint {K J X : SSet.{u}}
    [Quasicategory X] (p : J ⟶ X) (x : X _⦋0⦌) (f : K ⟶ J) :
    IsSimplicialHomotopyEquivalence
        (relativeFunctorPre (sliceUnderProjection (SSet.yonedaEquiv.symm x)) p f) ↔
      IsSimplicialHomotopyEquivalence (endpointConeRestrict p x f) := by
  have hs := (sectionEndpointConeComparison_homotopyEquivalence p x).isQCatEquivalence
  have ht := (sectionEndpointConeComparison_homotopyEquivalence (f ≫ p) x).isQCatEquivalence
  constructor
  · intro h
    have hc := h.isQCatEquivalence.comp ht
    rw [sectionEndpointConeComparison_restrict] at hc
    exact (hs.cancel_left hc).isSimplicialHomotopyEquivalence
  · intro h
    have hc := hs.comp h.isQCatEquivalence
    rw [← sectionEndpointConeComparison_restrict] at hc
    exact (ht.cancel_right hc).isSimplicialHomotopyEquivalence

end SerrePositivity.InfinityCategories.HomotopyLimits
