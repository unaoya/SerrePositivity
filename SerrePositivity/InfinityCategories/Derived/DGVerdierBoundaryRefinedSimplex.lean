module
public import SerrePositivity.InfinityCategories.Derived.DGVerdierBoundaryLastDenominator
public import SerrePositivity.InfinityCategories.Derived.DGOverBoundaryRefinedFaces
public import SerrePositivity.InfinityCategories.Derived.DGVerdierSimplexInitialRefinement
public import SerrePositivity.InfinityCategories.Derived.FullSubcomplexSimplexApexLift

/-! # 一般境界充填の回収単体を同じ実分母部分圏へ戻す

概要：追加実分母後の回収 over 単体の新 apex と全単体を、同じ実分母部分圏に入れる。
方針：正番号一面は元の同じ境界一面の実分母細分なので、新始頂点の分母性をそこから得る。
規約：元の零面と全回収単体を厳密に保持。使われ方：任意次元の有限共通始錐。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [IsDGPretriangulated A D]
variable (P : Set D) (x : D) {n : ℕ}
variable (B : (∂Δ[n + 1] : SSet.{max u v}) ⟶ (dgVerdierOver A D P x : SSet))
variable (q : D) (s : ForgetEnrichment.of (Complex A) q ⟶ ForgetEnrichment.of (Complex A)
  ((HornData.knownData (dgVerdierBoundaryHorn A D P x B)).obj 0))
variable (F : Δ[n + 2] ⟶ dgNerve A D)
variable (hF : (horn (n + 2) (Fin.last (n + 2))).ι ≫ F =
  dgGeneralLastHornSourceRefinement (dgVerdierBoundaryHorn A D P x B) q s)

include hF in
/-- 同じ追加実分母後の回収単体の始頂点は、同じ指定実分母である。 -/
lemma dgVerdierBoundaryRefinedApex_mem
    (hs : (dgClosedEdge A D s).edge ∈ dgVerdierEdges A D P) :
    IsDGVerdierOverVertex A D P x
      ((sliceOver _).map (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ 0).op
        (dgOverBoundaryRefinedSimplex _ (B ≫ (dgVerdierOver A D P x).ι) q s F hF)) := by
  let j : Fin (n + 2) := ⟨1, by omega⟩
  have hj : j ≠ 0 := by
    intro he
    have hv := congrArg Fin.val he
    change 1 = 0 at hv
    omega
  let b := SSet.yonedaEquiv (boundary.ι j ≫ B)
  let t := dgClosedTargetTransport A D s
    (dgOverBoundaryFace_source _ (B ≫ (dgVerdierOver A D P x).ι) j hj)
  have ht : (dgClosedEdge A D t).edge ∈ dgVerdierEdges A D P :=
    dgClosedTargetTransport_mem A D P s _ hs
  let e := dgVerdierSimplexInitialRefinement A D P x b q t ht
  have h₁ : (sliceOver _).δ j
      (dgOverBoundaryRefinedSimplex _ (B ≫ (dgVerdierOver A D P x).ι) q s F hF) = e.val := by
    exact dgOverBoundaryRefinedSimplex_face_initial _ _ q s F hF j hj
  have he : SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ 0 =
      SimplexCategory.const ⦋0⦌ ⦋n⦌ 0 ≫ SimplexCategory.δ j := by
    apply SimplexCategory.Hom.ext_zero_left
    exact (dgPositiveCoface_zero j hj).symm
  rw [he, op_comp, Functor.map_comp_apply]
  change IsDGVerdierOverVertex A D P x ((sliceOver _).map
    (SimplexCategory.const ⦋0⦌ ⦋n⦌ 0).op ((sliceOver _).δ j _))
  rw [h₁]
  exact e.property _

/-- 回収単体の同じ台を、全次数で同じ実分母 over 部分圏へ持ち上げる。 -/
def dgVerdierBoundaryRefinedSimplex
    (hs : (dgClosedEdge A D s).edge ∈ dgVerdierEdges A D P) :
    (dgVerdierOver A D P x : SSet.{max u v}) _⦋n + 1⦌ :=
  fullSubcomplexSimplexApexLift (IsDGVerdierOverVertex A D P x)
    (dgOverBoundaryRefinedSimplex _ (B ≫ (dgVerdierOver A D P x).ι) q s F hF)
    (SSet.yonedaEquiv (boundary.ι (0 : Fin (n + 2)) ≫ B))
    (dgOverBoundaryRefinedSimplex_face_zero _ _ q s F hF)
    (dgVerdierBoundaryRefinedApex_mem A D P x B q s F hF hs)

/-- 同じ実分母部分圏への持ち上げは、元の回収単体全体を保持する。 -/
lemma dgVerdierBoundaryRefinedSimplex_val
    (hs : (dgClosedEdge A D s).edge ∈ dgVerdierEdges A D P) :
    (dgVerdierBoundaryRefinedSimplex A D P x B q s F hF hs).val =
      dgOverBoundaryRefinedSimplex _ (B ≫ (dgVerdierOver A D P x).ι) q s F hF := rfl

/-- 同じ実分母部分圏内での零面も、元の指定境界零面そのもの。 -/
lemma dgVerdierBoundaryRefinedSimplex_face_zero
    (hs : (dgClosedEdge A D s).edge ∈ dgVerdierEdges A D P) :
    (dgVerdierOver A D P x : SSet).δ (0 : Fin (n + 2))
      (dgVerdierBoundaryRefinedSimplex A D P x B q s F hF hs) =
        SSet.yonedaEquiv (boundary.ι (0 : Fin (n + 2)) ≫ B) :=
  Subtype.ext (dgOverBoundaryRefinedSimplex_face_zero _ _ q s F hF)

/-- 同じ部分圏内の全正番号面は、元の同じ境界面の同じ実分母細分。 -/
lemma dgVerdierBoundaryRefinedSimplex_face_positive
    (hs : (dgClosedEdge A D s).edge ∈ dgVerdierEdges A D P)
    (j : Fin (n + 2)) (hj : j ≠ 0) :
    (dgVerdierOver A D P x : SSet).δ j
        (dgVerdierBoundaryRefinedSimplex A D P x B q s F hF hs) =
      dgVerdierSimplexInitialRefinement A D P x (SSet.yonedaEquiv (boundary.ι j ≫ B)) q
        (dgClosedTargetTransport A D s
          (dgOverBoundaryFace_source _ (B ≫ (dgVerdierOver A D P x).ι) j hj))
        (dgClosedTargetTransport_mem A D P s _ hs) :=
  Subtype.ext (dgOverBoundaryRefinedSimplex_face_initial _ _ q s F hF j hj)

end SerrePositivity.InfinityCategories
