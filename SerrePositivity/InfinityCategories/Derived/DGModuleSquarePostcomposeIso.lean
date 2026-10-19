module
public import SerrePositivity.InfinityCategories.Derived.DGModuleSquarePostcomposeEdge
public import SerrePositivity.InfinityCategories.Derived.DGModuleNerveHomotopyEquivalence
public import SerrePositivity.InfinityCategories.Stable.SquareFunctorTransport

/-! # 終点の加群同型による実四角形の関手同型

概要：四角形の終点を実加群同型で後合成すると、四角形全体の関手同型を得る。
方針：coslice 比較辺の射影を指定射に同定し、可逆性を反映して全余錐へ送る。
規約：span と二つの実二単体を保持。使われ方：cone 同型から押し出し性への輸送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.DGModuleSquareData
open CategoryTheory DifferentialGraded DGNerve
open scoped Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D] [Small.{u} D]
variable {W X Y Z T : ModuleCategory A D}
variable (s : DGModuleSquareData A D W X Y Z) (q : Z ⟶ T) [IsIso q]

/-- 同型による後合成比較の実 coslice 辺は可逆。 -/
lemma postcomposeSliceEdge_isInvertible :
    IsInvertibleEdge (X := sliceUnder (pushoutSpan s.square)) (s.postcomposeSliceEdge q) := by
  have := dgModuleEdge_isIso_of_homotopy A D q (by infer_instance)
  have he : IsInvertibleEdge (X := dgModuleNerve A D) (dgModuleEdge A D q).toTruncated :=
    (edgeToPathHomotopyCategory _).map_isIso
      (SSet.Truncated.HomotopyCategory₂.homMk (dgModuleEdge A D q).toTruncated)
  have hp := (isInvertibleEdge_congr (X := dgModuleNerve A D)
    (s.postcomposeSliceEdge_projection q)).mpr he
  exact leftFibration_reflects_invertibleEdge
    (sliceUnderProjection (pushoutSpan s.square)) (s.postcomposeSliceEdge q) hp

/-- 実終点同型による、二つの三角形を含む四角形全体の関手同型。 -/
def postcomposeFunctorIso : FunctorIso s.square (s.postcompose q).square := by
  have := s.postcomposeSliceEdge_isInvertible q
  let e := asIso (SSet.Truncated.HomotopyCategory.homMk (s.postcomposeSliceEdge q))
  let t := (coconeFunctorIsoOfVertexIso (pushoutCocone s.square) (s.postcomposeCocone q) e).precomp
    spanCoconeSquareIso.inv
  have h₀ : spanCoconeSquareIso.inv ≫ (pushoutCocone s.square).val = s.square := by
    change spanCoconeSquareIso.inv ≫ (spanCoconeSquareIso.hom ≫ s.square) = _
    rw [Iso.inv_hom_id_assoc]
  have h₁ : spanCoconeSquareIso.inv ≫ (s.postcomposeCocone q).val = (s.postcompose q).square := by
    change spanCoconeSquareIso.inv ≫ (spanCoconeSquareIso.hom ≫ (s.postcompose q).square) = _
    rw [Iso.inv_hom_id_assoc]
  exact (h₀ ▸ h₁ ▸ t)

/-- 終点同型による後合成は実押し出し性を保つ。 -/
lemma isPushout_postcompose (h : IsPushoutSquare s.square) :
    IsPushoutSquare (s.postcompose q).square :=
  h.of_functorIso (s.postcomposeFunctorIso q)

end SerrePositivity.InfinityCategories.DGModuleSquareData
