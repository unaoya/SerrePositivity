module
public import SerrePositivity.KST.SConstruction.PerfectLaxQuotientProductVertices
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.SquareHomotopyCategory

/-! # 実積へ移送した同じ全図式の四辺の自然性
概要：全図式の移送から、指定した四成分と四辺の自然性をそのまま回収する。
方針：元の延長の自然変換を四つの辺と頂点で評価する。
規約：全正方形の同型と同じ延長を使う。使われ方：四辺の元の射への正規化。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet Spectra
open SerrePositivity.InfinityCategories LocalizingInvariants
open scoped Simplicial
namespace PerfectLaxQuotient
local instance productComponentsSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory
variable {C D B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap C B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap D B}
  (d : PerfectLaxQuotient p q)
  {F : perfectStableInfinity.{u} ⟶ Sp.{u}} (hF : IsPerfectLocalizingInvariant F)

/-- 同じ全図式の移送の自然変換の、元の四角における成分。 -/
def productComponent (a b : Fin 2) : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoVertex (d.universalValueSquare F) a b ⟶
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoVertex (d.productSquare hF) a b :=
  (d.productExtension hF).naturalTransformation.app
    (HomotopyCategory.mk (stdSimplex.obj₀Equiv.symm a, stdSimplex.obj₀Equiv.symm b))

/-- 同じ自然変換の成分は、指定した元の頂点同型の射そのもの。 -/
lemma productComponent_arrow (a b : Fin 2) : Arrow.mk (d.productComponent hF a b) =
    Arrow.mk (d.productCornerIso hF a b).2.hom := by
  have he := DiagramVertexPaths.Extension.naturalTransformation_component_ofIso
    (d.productVertexIsos hF) (d.productExtension hF)
    (stdSimplex.obj₀Equiv.symm a, stdSimplex.obj₀Equiv.symm b)
  change Arrow.mk (d.productComponent hF a b) = _ at he
  refine he.trans ?_
  simp only [productVertexIsos, Iso.trans_hom, eqToIso.hom]
  exact arrow_mk_eqToHom_comp _ _

/-- 元の底辺と移送後の底辺は、同じ全図式の自然性で可換する。 -/
lemma productSquare_bottom_naturality : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoBottom (d.universalValueSquare F) ≫
    d.productComponent hF 1 0 = d.productComponent hF 0 0 ≫
      _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoBottom (d.productSquare hF) :=
  (d.productExtension hF).naturalTransformation.naturality
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoBottom (𝟙 ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])))

/-- 元の上辺と移送後の上辺は、同じ全図式の自然性で可換する。 -/
lemma productSquare_top_naturality : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoTop (d.universalValueSquare F) ≫
    d.productComponent hF 1 1 = d.productComponent hF 0 1 ≫
      _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoTop (d.productSquare hF) :=
  (d.productExtension hF).naturalTransformation.naturality
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoTop (𝟙 ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])))

/-- 元の左辺と移送後の左辺は、同じ全図式の自然性で可換する。 -/
lemma productSquare_left_naturality : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoLeft (d.universalValueSquare F) ≫
    d.productComponent hF 0 1 = d.productComponent hF 0 0 ≫
      _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoLeft (d.productSquare hF) :=
  (d.productExtension hF).naturalTransformation.naturality
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoLeft (𝟙 ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])))

/-- 元の右辺と移送後の右辺は、同じ全図式の自然性で可換する。 -/
lemma productSquare_right_naturality : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoRight (d.universalValueSquare F) ≫
    d.productComponent hF 1 1 = d.productComponent hF 1 0 ≫
      _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoRight (d.productSquare hF) :=
  (d.productExtension hF).naturalTransformation.naturality
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoRight (𝟙 ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])))

end PerfectLaxQuotient
end SerrePositivity.KST.SConstruction
