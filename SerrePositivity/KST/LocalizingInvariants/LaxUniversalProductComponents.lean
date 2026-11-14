module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalProductSquare
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.SquareHomotopyCategory

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
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants.LaxUniversalProduct
local instance : SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory
variable {Φ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} ⟶ Sp.{u}} (hΦ : IsLocalizingInvariant Φ)
  {C D E A Q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap C E) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap D E)
  (i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A (laxCategory p q)) (r : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (laxCategory p q) Q)
  (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i r)

lemma vertex_at (a b : Fin 2) : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalProductSquare.square hΦ p q i r h) a b =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalProductSquare.cornerIso hΦ p q i r h a b).1 := by
  have hv := DiagramVertexPaths.Extension.target_vertex_ofIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalProductSquare.vertexIsos hΦ p q i r h)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalProductSquare.extension hΦ p q i r h) (stdSimplex.obj₀Equiv.symm a, stdSimplex.obj₀Equiv.symm b)
  refine hv.trans ?_
  change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalProductSquare.cornerIso hΦ p q i r h
    (stdSimplex.obj₀Equiv.{u + 1} (stdSimplex.obj₀Equiv.symm a))
    (stdSimplex.obj₀Equiv.{u + 1} (stdSimplex.obj₀Equiv.symm b))).1 = _
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]

lemma vertex00 : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalProductSquare.square hΦ p q i r h) 0 0 =
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (value Φ A) := vertex_at hΦ p q i r h 0 0

lemma vertex01 : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalProductSquare.square hΦ p q i r h) 0 1 =
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (value Φ Q) := vertex_at hΦ p q i r h 0 1

lemma vertex10 : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalProductSquare.square hΦ p q i r h) 1 0 =
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (Binary.obj (value Φ C) (value Φ D)) := vertex_at hΦ p q i r h 1 0

lemma vertex11 : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalProductSquare.square hΦ p q i r h) 1 1 =
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (Binary.obj (value Φ Q) (value Φ Q)) := vertex_at hΦ p q i r h 1 1

def component (a b : Fin 2) : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoVertex (LaxUniversalValue.square Φ p q i r h) a b ⟶
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoVertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalProductSquare.square hΦ p q i r h) a b :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalProductSquare.extension hΦ p q i r h).naturalTransformation.app
    (HomotopyCategory.mk (stdSimplex.obj₀Equiv.symm a, stdSimplex.obj₀Equiv.symm b))

lemma component_arrow (a b : Fin 2) : Arrow.mk (component hΦ p q i r h a b) =
    Arrow.mk (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalProductSquare.cornerIso hΦ p q i r h a b).2.hom := by
  have he := DiagramVertexPaths.Extension.naturalTransformation_component_ofIso
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalProductSquare.vertexIsos hΦ p q i r h) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalProductSquare.extension hΦ p q i r h)
    (stdSimplex.obj₀Equiv.symm a, stdSimplex.obj₀Equiv.symm b)
  change Arrow.mk (component hΦ p q i r h a b) = _ at he
  refine he.trans ?_
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalProductSquare.vertexIsos, Iso.trans_hom, eqToIso.hom]
  exact arrow_mk_eqToHom_comp _ _

lemma bottom_naturality : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoBottom (LaxUniversalValue.square Φ p q i r h) ≫
    component hΦ p q i r h 1 0 = component hΦ p q i r h 0 0 ≫
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoBottom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalProductSquare.square hΦ p q i r h) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalProductSquare.extension hΦ p q i r h).naturalTransformation.naturality
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoBottom (𝟙 ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])))

lemma top_naturality : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoTop (LaxUniversalValue.square Φ p q i r h) ≫
    component hΦ p q i r h 1 1 = component hΦ p q i r h 0 1 ≫
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoTop (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalProductSquare.square hΦ p q i r h) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalProductSquare.extension hΦ p q i r h).naturalTransformation.naturality
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoTop (𝟙 ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])))

lemma left_naturality : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoLeft (LaxUniversalValue.square Φ p q i r h) ≫
    component hΦ p q i r h 0 1 = component hΦ p q i r h 0 0 ≫
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoLeft (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalProductSquare.square hΦ p q i r h) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalProductSquare.extension hΦ p q i r h).naturalTransformation.naturality
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoLeft (𝟙 ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])))

lemma right_naturality : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoRight (LaxUniversalValue.square Φ p q i r h) ≫
    component hΦ p q i r h 1 1 = component hΦ p q i r h 1 0 ≫
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoRight (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalProductSquare.square hΦ p q i r h) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalProductSquare.extension hΦ p q i r h).naturalTransformation.naturality
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoRight (𝟙 ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])))

end SerrePositivity.KST.LocalizingInvariants.LaxUniversalProduct
