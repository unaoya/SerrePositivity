module
public import SerrePositivity.InfinityCategories.Derived.DGClosedDenominatorIdentityEdge
public import SerrePositivity.InfinityCategories.Derived.PinchedConstantHomotopy
public import SerrePositivity.InfinityCategories.Derived.PinchedClosedVertexSlice
/-!
概要：実閉分母から恒等分母への細分辺を任意パラメータの全時刻の族にする。
方針：同じ辺の定数区間族を使い、その始域射影を元の閉辺の像と厳密に照合する。
規約：全底の写像を保持する。使われ方：任意標的の実評価の pullback 比較。
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
/-- 任意パラメータ上の、指定閉分母から恒等分母への同じ実細分ホモトピー。 -/
def dgClosedDenominatorHomotopy (P : Set D) (x : D)
    (r : DGClosedVerdierDenominators A D P x) (K : SSet.{max u v}) :
    SSet.Homotopy (SSet.const (X := K) (dgClosedVerdierDenominatorVertex A D P x r))
      (SSet.const (dgVerdierOverIdentityVertex A D P x)) :=
  intervalFamilyHomotopy (SSet.const (intervalMappingVertexOfEdge
    (SSet.Edge.ofTruncated (X := (dgVerdierOver A D P x : SSet))
      (dgClosedDenominatorIdentityEdge A D P x r))))
/-- 指定細分ホモトピーの像は、元の指定閉分母の像の全区間と厳密に同じ。 -/
lemma dgClosedDenominatorHomotopy_source (P : Set D) (x : D)
    (r : DGClosedVerdierDenominators A D P x) (K : SSet.{max u v})
    {Y : SSet.{max u v}} (F : dgNerve A D ⟶ Y) :
    (dgClosedDenominatorHomotopy A D P x r K).h ≫ (dgVerdierOverSource A D P x ≫ F) =
      (intervalFamilyHomotopy
        ((SSet.const (X := K) (pinchedClosedVertex A D r.obj.hom) ≫
          pinchedHomMap F
            (Simplex.vertex (ForgetEnrichment.to (Complex A) r.obj.left)) (Simplex.vertex x)) ≫
              pinchedHomToIntervalMappingSpace _ _)).h := by
  let e := SSet.Edge.ofTruncated (X := (dgVerdierOver A D P x : SSet))
    (dgClosedDenominatorIdentityEdge A D P x r)
  have h₀ := intervalFamilyHomotopy_const_edge_h (K := K) e
  have h₁ := congrArg (F.app (Opposite.op ⦋1⦌))
    (dgClosedDenominatorIdentityEdge_source A D P x r)
  calc
    _ = (CartesianMonoidalCategory.snd K (Δ[1] : SSet.{max u v}) ≫
        SSet.yonedaEquiv.symm e.edge) ≫ (dgVerdierOverSource A D P x ≫ F) :=
      congrArg (fun a => a ≫ (dgVerdierOverSource A D P x ≫ F)) h₀
    _ = CartesianMonoidalCategory.snd K (Δ[1] : SSet.{max u v}) ≫
        SSet.yonedaEquiv.symm ((dgVerdierOverSource A D P x ≫ F).app
          (Opposite.op ⦋1⦌) e.edge) := by
      rw [Category.assoc, SSet.yonedaEquiv_symm_comp]
    _ = CartesianMonoidalCategory.snd K (Δ[1] : SSet.{max u v}) ≫
        SSet.yonedaEquiv.symm (F.app (Opposite.op ⦋1⦌) (pinchedClosedVertex A D r.obj.hom).val) :=
      congrArg (fun a => CartesianMonoidalCategory.snd K (Δ[1] : SSet.{max u v}) ≫
        SSet.yonedaEquiv.symm a) h₁
    _ = _ := (pinchedConstantHomotopy_postcomp_h (K := K) F
      (pinchedClosedVertex A D r.obj.hom)).symm
end SerrePositivity.InfinityCategories
