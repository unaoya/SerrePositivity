module

public import SerrePositivity.KST.Spectra.SpectrumMappingLaws

/-!
概要：BF Ω スペクトルの局所 Kan な単体的圏。
方針：逆極限の写像空間の厳密合成と零次単体の同値を束ねる。
規約：導来写像空間との比較は γ3 後の工程。
使われ方：HTT A.3.3、BF 1978 §2、HTT 1.1.5.10。coherent nerve の入力。
-/

@[expose] public section

universe u

open CategoryTheory SSet MonoidalCategory

namespace SerrePositivity.KST.Spectra.OmegaSpectrum

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

local instance : SimplicialCategory PointedSimplicialSet.{u} := PointedEnrichment.simplicialCategory

/-- 概要：厳密な射を表す終対象パラメータの射は各段の豊穣射と一致する。
方針：頂点の同値を介した両方の定義を比較する。
規約：通常の点つき射の単体的表示。
使われ方：BF 1978 §2。通常の合成と単体的合成の比較。 -/
theorem homFamily_eq_eHom {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y) (n : ℕ) :
    homFamily f n = eHomEquiv SSet (f.app n) := by
  apply (SSet.unitHomEquiv _).injective
  rw [homFamily, Equiv.apply_symm_apply]
  rfl

/-- 概要：厳密な射を表す終対象からの射は各段で元の豊穣射に評価される。
方針：切断写像空間の普遍的な持ち上げを評価する。
規約：全ての自然数段 n。
使われ方：BF 1978 §2。単体的圏と通常の圏の接続。 -/
@[reassoc (attr := simp)]
theorem vertexOfHomMap_evaluation {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y) (n : ℕ) :
    vertexOfHomMap f ≫ evaluation X Y n = eHomEquiv SSet (f.app n) := by
  have h := TruncatedMapping.familyLift_evaluation
    (fun n ↦ (X.level n).space) (fun n ↦ (Y.level n).space)
    (fun n ↦ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space) X.sigma (mappingStep X Y)
    (homFamily f) (homFamily_condition f) n
  exact h.trans (homFamily_eq_eHom f n)

/-- 概要：通常の射の合成は写像空間の単体的合成へ移される。
方針：各段評価で検査し、点つき単体集合の豊穣射の合成法則を使う。
規約：終対象パラメータの射の厳密な等式。
使われ方：BF 1978 §2、HTT A.3.3。通常の豊穣圏の構成。 -/
theorem vertexOfHomMap_comp {X Y Z : OmegaSpectrum.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    vertexOfHomMap (f ≫ g) =
      (λ_ (𝟙_ SSet.{u})).inv ≫ (vertexOfHomMap f ⊗ₘ vertexOfHomMap g) ≫
        mappingComposition X Y Z := by
  apply mapping_hom_ext
  intro n
  simp only [Category.assoc, mappingComposition_evaluation, compositionFamily,
    vertexOfHomMap_evaluation]
  rw [tensorHom_comp_tensorHom_assoc,
    vertexOfHomMap_evaluation, vertexOfHomMap_evaluation]
  exact eHomEquiv_comp SSet (f.app n) (g.app n)

/-- 概要：Ω スペクトルの構成済みの写像空間と厳密合成による豊穣圏。
方針：評価で証明した単位律・結合律を束ねる。
規約：豊穣基礎圏は通常の単体集合。
使われ方：BF 1978 §2、HTT A.3.3。coherent nerve の入力。 -/
@[instance_reducible]
def mappingEnrichedCategory : EnrichedCategory SSet.{u} OmegaSpectrum.{u} where
  Hom := mappingSpace
  id := mappingIdentity
  comp := mappingComposition
  id_comp := mappingIdentity_comp
  comp_id := mappingComposition_identity
  assoc := mappingComposition_assoc

/-- 概要：Ω スペクトルの通常の射と整合する単体的圏。
方針：写像空間の頂点との同値と恒等・合成の保存を使う。
規約：局所 Kan 性は実際に構成済みの写像空間の充填から得る。
使われ方：BF 1978 §2、HTT A.3.3、HTT 1.1.5.10。Sp の coherent nerve。
-/
@[instance_reducible]
def simplicialCategory : SimplicialCategory OmegaSpectrum.{u} where
  toEnrichedCategory := mappingEnrichedCategory
  homEquiv {X Y} := (homVertexEquiv X Y).trans (SSet.unitHomEquiv (mappingSpace X Y)).symm
  homEquiv_id X := by
    change (SSet.unitHomEquiv _).symm (vertexOfHom (𝟙 X)) = mappingIdentity X
    exact Equiv.symm_apply_apply _ _
  homEquiv_comp f g := by
    change (SSet.unitHomEquiv _).symm (vertexOfHom (f ≫ g)) =
      (λ_ (𝟙_ SSet.{u})).inv ≫
        ((SSet.unitHomEquiv _).symm (vertexOfHom f) ⊗ₘ
          (SSet.unitHomEquiv _).symm (vertexOfHom g)) ≫ mappingComposition _ _ _
    simp only [vertexOfHom, Equiv.symm_apply_apply]
    exact vertexOfHomMap_comp f g

end

end SerrePositivity.KST.Spectra.OmegaSpectrum
