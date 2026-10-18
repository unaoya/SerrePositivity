module

public import SerrePositivity.InfinityCategories.HomotopyLimits.ConeRestrictionComparison
public import SerrePositivity.InfinityCategories.HomotopyLimits.ConeSliceRestrictionCriterion

/-!
概要：slice の頂点 fiber から両端固定の錐への実際の標準比較を追跡する。
方針：fiber の包含後の普遍族を展開し、join と直積の比較の自然性を使う。
規約：選択した逆同値は用いず、全ての単体的パラメータを扱う。
使われ方：HTT 4.2.4.1、Kerodon 7.4.1.6 の native な極限判定の切断への移送。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 概要：slice の頂点 fiber を両端固定の錐の空間へ写す標準比較。
方針：内部 Hom の錐への比較と二重 fiber の同型を合成する。
規約：頂点 x と図式 p を全次数で固定する。
使われ方：Kerodon 7.4.1.6 の制限の可換四角形の slice 側。 -/
noncomputable def sliceEndpointConeComparison {K X : SSet.{u}} (p : K ⟶ X)
    (x : X _⦋0⦌) : vertexFiber (sliceOverProjection p) x ⟶ fixedEndpointConeSpace p x :=
  coneVertexFiberFamilyMap p x ≫ (fixedApexEndpointConeSpaceIso p x).hom

/-- 概要：slice の普遍族の標準比較の展開はパラメータの射と可換。
方針：直積の対称性、join と直積の自然性、slice の uncurry の前合成則を使う。
規約：A は任意のパラメータ。
使われ方：Kerodon 4.6.6.8 の実際の比較の全パラメータでの値。 -/
lemma sliceConeFamilyUncurry_parameter {A K X : SSet.{u}} {p : K ⟶ X}
    (s : A ⟶ sliceOver p) :
    (join (Δ[0] : SSet.{u}) K ◁ s) ≫ sliceConeFamilyUncurry p =
      (β_ (join (Δ[0] : SSet.{u}) K) A).hom ≫ joinTensorLeft A Δ[0] K ≫
        joinMap (fst A Δ[0]) (𝟙 K) ≫ sliceOverUncurry s := by
  have hb : (join (Δ[0] : SSet.{u}) K ◁ s) ≫
      (β_ (join (Δ[0] : SSet.{u}) K) (sliceOver p)).hom =
      (β_ (join (Δ[0] : SSet.{u}) K) A).hom ≫ (s ▷ join Δ[0] K) := rfl
  unfold sliceConeFamilyUncurry
  rw [← Category.assoc (join (Δ[0] : SSet.{u}) K ◁ s), hb]
  simp only [Category.assoc]
  rw [← Category.assoc (s ▷ join (Δ[0] : SSet.{u}) K), joinTensorLeft_naturality]
  simp only [Category.assoc]
  rw [← Category.assoc (joinMap (s ▷ (Δ[0] : SSet.{u})) (𝟙 K)), ← joinMap_comp]
  have hf : (s ▷ (Δ[0] : SSet.{u})) ≫ fst (sliceOver p) Δ[0] = fst A Δ[0] ≫ s := rfl
  rw [hf, Category.id_comp]
  have hj := joinMap_comp (fst A (Δ[0] : SSet.{u})) s (𝟙 K) (𝟙 K)
  rw [Category.id_comp] at hj
  rw [hj, Category.assoc, ← sliceOverUncurry_precomp, Category.comp_id]

/-- 概要：slice の標準比較を展開すると、左パラメータ付きの join の図式になる。
方針：二つの fiber の包含と内部 Hom の curry の往復を計算する。
規約：全パラメータでの式であり、充填性は不要。
使われ方：Kerodon 7.4.1.6 の slice 側の図式制限の自然性。 -/
lemma sliceEndpointConeComparison_uncurry {A K X : SSet.{u}} {p : K ⟶ X}
    {x : X _⦋0⦌} (s : A ⟶ vertexFiber (sliceOverProjection p) x) :
    uncurry (s ≫ sliceEndpointConeComparison p x ≫ endpointConeEvaluation p x) =
      (β_ (join (Δ[0] : SSet.{u}) K) A).hom ≫ joinTensorLeft A Δ[0] K ≫
        joinMap (fst A Δ[0]) (𝟙 K) ≫
          sliceOverUncurry (s ≫ vertexFiberι (sliceOverProjection p) x) := by
  change uncurry (s ≫ (coneVertexFiberFamilyMap p x ≫
    (fixedApexToEndpointConeSpace p x ≫ endpointConeEvaluation p x))) = _
  rw [fixedApexToEndpointConeSpace, vertexFiberLift_ι]
  change uncurry (s ≫ (coneVertexFiberFamilyMap p x ≫
    (vertexFiberι (coneFamilyApex p) x ≫
      vertexFiberι (coneRestriction K X) (functorVertex p)))) = _
  rw [← Category.assoc (coneVertexFiberFamilyMap p x), coneVertexFiberFamilyMap,
    vertexFiberMap_ι, Category.assoc, sliceConeFamilyMap, vertexFiberLift_ι,
    ← Category.assoc s, uncurry_natural_left, uncurry_curry]
  exact sliceConeFamilyUncurry_parameter _

/-- 概要：slice の図式の制限は可変頂点の射影を保つ。
方針：制限を展開し、join の左包含上で射影を回収する。
規約：任意の図式の射について成立する。
使われ方：Kerodon 7.4.1.6 の同じ頂点上の fiber への制限。 -/
lemma sliceOverRestrict_projection {K J X : SSet.{u}} (p : J ⟶ X) (f : K ⟶ J) :
    sliceOverRestrict p f ≫ sliceOverProjection (f ≫ p) = sliceOverProjection p := by
  have h := sliceOverUncurry_projection (sliceOverRestrict p f)
  have hu := sliceOverUncurry_restrict (𝟙 (sliceOver p)) f
  simp only [Category.id_comp] at hu
  rw [hu, ← Category.assoc, joinInl_joinMap, Category.id_comp,
    sliceOverUncurry_projection, Category.id_comp] at h
  exact h.symm

/-- 概要：slice の図式の制限を同じ頂点の fiber へ移す。
方針：可変頂点の射影との可換性から fiber の射を作る。
規約：充填性や単射性は仮定しない。
使われ方：Kerodon 7.4.1.6 の slice 側の実際の制限射。 -/
def sliceRestrictionFiberMap {K J X : SSet.{u}} (p : J ⟶ X) (x : X _⦋0⦌)
    (f : K ⟶ J) :
    vertexFiber (sliceOverProjection p) x ⟶ vertexFiber (sliceOverProjection (f ≫ p)) x :=
  vertexFiberMap _ _ (sliceOverRestrict p f) (sliceOverRestrict_projection p f) x

/-- 概要：slice からの標準比較は図式の射に沿う制限と可換。
方針：包含後の uncurry と普遍族の式で検出し、join と直積の自然性を使う。
規約：K、J、X は任意。選択した逆同値は使わない。
使われ方：HTT 4.2.4.1 の native な極限判定と切断の制限の接続。 -/
lemma sliceEndpointConeComparison_restrict {K J X : SSet.{u}} (p : J ⟶ X)
    (x : X _⦋0⦌) (f : K ⟶ J) :
    sliceRestrictionFiberMap p x f ≫ sliceEndpointConeComparison (f ≫ p) x =
      sliceEndpointConeComparison p x ≫ endpointConeRestrict p x f := by
  let A := vertexFiber (sliceOverProjection p) x
  have hb : (joinMap (𝟙 (Δ[0] : SSet.{u})) f ▷ A) ≫
      (β_ (join (Δ[0] : SSet.{u}) J) A).hom =
      (β_ (join (Δ[0] : SSet.{u}) K) A).hom ≫
        (A ◁ joinMap (𝟙 (Δ[0] : SSet.{u})) f) := rfl
  apply vertexFiber_hom_ext
    ((pre (joinEndpointInclusion (Δ[0] : SSet.{u}) K)).app X)
    (functorVertex (joinEndpointDesc (SSet.yonedaEquiv.symm x) (f ≫ p)))
  change (_ ≫ sliceEndpointConeComparison (f ≫ p) x) ≫
      endpointConeEvaluation (f ≫ p) x =
    (sliceEndpointConeComparison p x ≫ endpointConeRestrict p x f) ≫
      endpointConeEvaluation (f ≫ p) x
  rw [Category.assoc, Category.assoc, endpointConeRestrict_evaluation, ← Category.assoc]
  apply uncurry_injective
  rw [Category.assoc, sliceEndpointConeComparison_uncurry, sliceRestrictionFiberMap,
    vertexFiberMap_ι, sliceOverUncurry_restrict,
    ← Category.assoc (sliceEndpointConeComparison p x), uncurry_pre_app]
  have he := sliceEndpointConeComparison_uncurry
    (p := p) (x := x) (𝟙 A)
  simp only [Category.id_comp] at he
  rw [he, ← Category.assoc (joinMap (𝟙 (Δ[0] : SSet.{u})) f ▷ A), hb]
  simp only [Category.assoc]
  rw [← Category.assoc (A ◁ joinMap (𝟙 (Δ[0] : SSet.{u})) f), joinTensorLeft_diagram]
  simp only [Category.assoc]
  rw [← Category.assoc (joinMap (fst A (Δ[0] : SSet.{u})) (𝟙 K)), ← joinMap_comp,
    ← Category.assoc (joinMap (𝟙 (A ⊗ (Δ[0] : SSet.{u}))) f), ← joinMap_comp]
  simp only [Category.comp_id, Category.id_comp]
  dsimp only [A]
  rw [Category.comp_id]

/-- 概要：quasicategory では slice から両端固定の錐への標準比較はホモトピー同値。
方針：既存の固定頂点の比較の同値と二重 fiber の同型を合成する。
規約：図式の始域 K は任意。
使われ方：Kerodon 7.4.1.6 の制限の可換四角形の同値辺。 -/
lemma sliceEndpointConeComparison_homotopyEquivalence {K X : SSet.{u}}
    [Quasicategory X] (p : K ⟶ X) (x : X _⦋0⦌) :
    IsSimplicialHomotopyEquivalence (sliceEndpointConeComparison p x) := by
  exact ((coneVertexFiberFamilyMap_isQCatEquivalence p x).comp
    (qCatEquivalenceOfIso (fixedApexEndpointConeSpaceIso p x)).isQCatEquivalence
      ).isSimplicialHomotopyEquivalence

/-- 概要：slice の制限の同値性は coslice の切断の制限の同値性と同値。
方針：両端固定の錐への二つの標準比較の可換四角形と二対三則を使う。
規約：X は quasicategory、添字の単体集合と射は任意。
使われ方：HTT 4.2.4.1、Kerodon 7.4.1.6 の native な極限判定の移送。 -/
lemma sliceRestriction_homotopyEquivalence_iff_sections {K J X : SSet.{u}}
    [Quasicategory X] (p : J ⟶ X) (x : X _⦋0⦌) (f : K ⟶ J) :
    IsSimplicialHomotopyEquivalence (sliceRestrictionFiberMap p x f) ↔
      IsSimplicialHomotopyEquivalence
        (relativeFunctorPre (sliceUnderProjection (SSet.yonedaEquiv.symm x)) p f) := by
  rw [sectionRestriction_homotopyEquivalence_iff_endpoint]
  have := vertexFiber_kanComplex (sliceOverProjection p) x
  have := vertexFiber_kanComplex (sliceOverProjection (f ≫ p)) x
  have hs := (sliceEndpointConeComparison_homotopyEquivalence p x).isQCatEquivalence
  have ht := (sliceEndpointConeComparison_homotopyEquivalence (f ≫ p) x).isQCatEquivalence
  constructor
  · intro h
    have hc := h.isQCatEquivalence.comp ht
    rw [sliceEndpointConeComparison_restrict] at hc
    exact (hs.cancel_left hc).isSimplicialHomotopyEquivalence
  · intro h
    have hc := hs.comp h.isQCatEquivalence
    rw [← sliceEndpointConeComparison_restrict] at hc
    exact (ht.cancel_right hc).isSimplicialHomotopyEquivalence

end SerrePositivity.InfinityCategories.HomotopyLimits
