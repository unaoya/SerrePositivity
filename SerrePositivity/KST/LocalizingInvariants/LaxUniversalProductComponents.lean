module

public import SerrePositivity.KST.LocalizingInvariants.LaxUniversalProductSquare
public import SerrePositivity.InfinityCategories.Core.SquareHomotopyCategory

/-!
概要：実積への図式移送後の四頂点と、指定積同値を持つ自然変換の各成分。
方針：頂点で指定した path を評価し、その成分の Arrow 等号を回収する。
規約：四辺の自然性も同じ全図式から読む。使われ方：元の BF 積射への四辺の正規化。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants.LaxUniversalProduct
local instance : SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory
variable {Φ : StableInfinity.{u} ⟶ Sp.{u}} (hΦ : IsLocalizingInvariant Φ)
  {C D E A Q : StableCategory.{u}} (p : ExactMap C E) (q : ExactMap D E)
  (i : ExactMap A (laxCategory p q)) (r : ExactMap (laxCategory p q) Q)
  (h : IsVerdierSequence i r)

lemma vertex_at (a b : Fin 2) : squareVertex (square hΦ p q i r h) a b =
    (cornerIso hΦ p q i r h a b).1 := by
  have hv := DiagramVertexPaths.Extension.target_vertex_ofIso (vertexIsos hΦ p q i r h)
    (extension hΦ p q i r h) (stdSimplex.obj₀Equiv.symm a, stdSimplex.obj₀Equiv.symm b)
  refine hv.trans ?_
  change (cornerIso hΦ p q i r h
    (stdSimplex.obj₀Equiv.{u + 1} (stdSimplex.obj₀Equiv.symm a))
    (stdSimplex.obj₀Equiv.{u + 1} (stdSimplex.obj₀Equiv.symm b))).1 = _
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]

lemma vertex00 : squareVertex (square hΦ p q i r h) 0 0 =
    coherentNerveVertex (value Φ A) := vertex_at hΦ p q i r h 0 0

lemma vertex01 : squareVertex (square hΦ p q i r h) 0 1 =
    coherentNerveVertex (value Φ Q) := vertex_at hΦ p q i r h 0 1

lemma vertex10 : squareVertex (square hΦ p q i r h) 1 0 =
    coherentNerveVertex (Binary.obj (value Φ C) (value Φ D)) := vertex_at hΦ p q i r h 1 0

lemma vertex11 : squareVertex (square hΦ p q i r h) 1 1 =
    coherentNerveVertex (Binary.obj (value Φ Q) (value Φ Q)) := vertex_at hΦ p q i r h 1 1

def component (a b : Fin 2) : squareHoVertex (LaxUniversalValue.square Φ p q i r h) a b ⟶
    squareHoVertex (square hΦ p q i r h) a b :=
  (extension hΦ p q i r h).naturalTransformation.app
    (HomotopyCategory.mk (stdSimplex.obj₀Equiv.symm a, stdSimplex.obj₀Equiv.symm b))

lemma component_arrow (a b : Fin 2) : Arrow.mk (component hΦ p q i r h a b) =
    Arrow.mk (cornerIso hΦ p q i r h a b).2.hom := by
  have he := DiagramVertexPaths.Extension.naturalTransformation_component_ofIso
    (vertexIsos hΦ p q i r h) (extension hΦ p q i r h)
    (stdSimplex.obj₀Equiv.symm a, stdSimplex.obj₀Equiv.symm b)
  change Arrow.mk (component hΦ p q i r h a b) = _ at he
  refine he.trans ?_
  simp only [vertexIsos, Iso.trans_hom, eqToIso.hom]
  exact arrow_mk_eqToHom_comp _ _

lemma bottom_naturality : squareHoBottom (LaxUniversalValue.square Φ p q i r h) ≫
    component hΦ p q i r h 1 0 = component hΦ p q i r h 0 0 ≫
      squareHoBottom (square hΦ p q i r h) :=
  (extension hΦ p q i r h).naturalTransformation.naturality
    (squareHoBottom (𝟙 ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])))

lemma top_naturality : squareHoTop (LaxUniversalValue.square Φ p q i r h) ≫
    component hΦ p q i r h 1 1 = component hΦ p q i r h 0 1 ≫
      squareHoTop (square hΦ p q i r h) :=
  (extension hΦ p q i r h).naturalTransformation.naturality
    (squareHoTop (𝟙 ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])))

lemma left_naturality : squareHoLeft (LaxUniversalValue.square Φ p q i r h) ≫
    component hΦ p q i r h 0 1 = component hΦ p q i r h 0 0 ≫
      squareHoLeft (square hΦ p q i r h) :=
  (extension hΦ p q i r h).naturalTransformation.naturality
    (squareHoLeft (𝟙 ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])))

lemma right_naturality : squareHoRight (LaxUniversalValue.square Φ p q i r h) ≫
    component hΦ p q i r h 1 1 = component hΦ p q i r h 1 0 ≫
      squareHoRight (square hΦ p q i r h) :=
  (extension hΦ p q i r h).naturalTransformation.naturality
    (squareHoRight (𝟙 ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])))

end SerrePositivity.KST.LocalizingInvariants.LaxUniversalProduct
