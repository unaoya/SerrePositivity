module

public import
  SerrePositivity.InfinityCategories.F2.FilteredExchange.SpaceSimplexPointedBoundaryEndpoint
public import
  SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitApexPointedVertexEndpoints
/-!
概要：元の全三角形の指定比較は同じ全初点係数で恒等となる。
方針：実初点を固定境界内で評価し、同じ元の境界値への定値性を使う。
規約：初点の実 fiber・全係数と元の指定比較を保持する。
使われ方：第一面の指定初点像と native 像の恒等性。
-/

@[expose] public section
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
variable (B : SSet.{u})
  {F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {a : SSet.Homotopy F G} {b : SSet.Homotopy G J} {d : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle a b d)
local notation "p" => pointedSpaceProjection
local notation "s" => coherentColimitApexTriangle B T
local notation "A" => spaceSimplexPointedCoefficients s
local notation "q" => coherentColimitApexCoefficientMap B T
local notation "x" => JoinCocone.vertex (coherentDiagramTotalCocone F)
local notation "γ" => fst Δ[2] A ≫ SSet.yonedaEquiv.symm s
local notation "r" => simplexPrismVertex 2 0 A
local notation "L" => coherentColimitRawUniversalTrianglePrism B T q
/-- 概要：元の全初点の底は同じ実初余錐頂点に定値。
方針：同じ初点の実頂点表示で移す。規約：実頂点を保持。
使われ方：第一面の固定初点評価。 -/
lemma coherentColimitApexPointedInitial_base : r ≫ γ = SSet.const x :=
  (spaceSimplexPointedVertex_base s 0).trans
    (congrArg SSet.const (coherentColimitApexCoefficient_vertex B T).symm)
/-- 概要：同じ全比較の固定初点像は元の初期係数の恒等比較。
方針：元の初点評価を同じ境界包含で分解する。
規約：両実境界と指定比較を保持。使われ方：第一面の初点整合。 -/
lemma coherentColimitApexPointedInitialEndpointIso_eq_refl
    (hs : r ≫ spaceSimplexPointedFamily s = q ≫ vertexFiberι p x)
    (ht : r ≫ L = q ≫ vertexFiberι p x) :
    spaceSimplexPointedFamilyEndpointIso s L
      (coherentColimitApexPointedFamily_projection B T)
      (coherentColimitApexPointedFamily_initial B T) r x
      (coherentColimitApexPointedInitial_base B T) q q hs ht =
      Iso.refl (SSet.HomotopyCategory.mk (functorVertex q)) := by
  let t : A ⟶ (Δ[0] : SSet.{u + 1}) ⊗ A :=
    lift (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1))) (𝟙 A)
  have hr : r = t ≫ (scaffoldFirstVertex 2 ▷ A) := by
    apply SSet.hom_ext
    intro n
    rfl
  refine spaceSimplexPointedFamilyEndpointIso_eq_refl_of_boundary s L
    (coherentColimitApexPointedFamily_projection B T)
    (coherentColimitApexPointedFamily_initial B T) r t hr x
    (coherentColimitApexPointedInitial_base B T) q hs ht ?_
  simpa only [t, ← Category.assoc, lift_snd, Category.id_comp] using
    (coherentColimitApexCoefficientMap_ι B T).symm
end
end SerrePositivity.InfinityCategories.F2
