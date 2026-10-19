module

public import SerrePositivity.KST.Spectra.EnrichedParameterCylinderEdgeOrdinary
public import SerrePositivity.InfinityCategories.F1.CoherentHomOrdinary
public import SerrePositivity.InfinityCategories.PinchedHom.Paths

/-!
概要：パラメータ空間の辺から、二対象の円柱の coherent な三角形を作る。
方針：豊穣 Hom の辺を右 pinched Hom に送り、先頭辺が恒等である三角形に読む。
規約：元の辺と両端を保持する。使われ方：円の生成辺から評価の三角形を構成する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.EnrichedParameterCylinder
variable {A : SSet.{u}}

/-- パラメータ射の豊穣 Hom の頂点は、そのパラメータと単位の対。 -/
lemma parameterHom_vertex (i : 𝟙_ SSet.{u} ⟶ A) :
    SimplicialCategory.homEquiv'
        (⟨false, ⟨PUnit.unit⟩⟩ : Object A Point.{v}) ⟨true, ⟨PUnit.unit⟩⟩
        (parameterHom i) = (A.unitHomEquiv i, PUnit.unit) := rfl

/-- パラメータ辺を、宇宙を持ち上げた豊穣 Hom の辺として保持する。 -/
def parameterHomEdge {x y : A _⦋0⦌} (e : A.Edge x y) :
    ((SSet.uliftFunctor.{v, u}).obj
      (SimplicialCategory.sHom
        (⟨false, ⟨PUnit.unit⟩⟩ : Object A Point.{v}) ⟨true, ⟨PUnit.unit⟩⟩)).Edge
      (ULift.up (x, PUnit.unit)) (ULift.up (y, PUnit.unit)) :=
  SSet.Edge.mk (ULift.up (e.edge, PUnit.unit))
    (by change ULift.up (A.δ 1 e.edge, PUnit.unit) = _; rw [e.src_eq])
    (by change ULift.up (A.δ 0 e.edge, PUnit.unit) = _; rw [e.tgt_eq])

/-- Hom 比較のパラメータ頂点は、元のパラメータ射の coherent な辺へ移る。 -/
lemma parameterComparisonVertex (x : A _⦋0⦌) :
    PinchedHom.vertexEquiv (leftVertex.{u, v} A) (rightVertex.{u, v} A)
      ((coherentHomComparison
        (⟨false, ⟨PUnit.unit⟩⟩ : Object A Point.{v}) ⟨true, ⟨PUnit.unit⟩⟩).app
          (Opposite.op ⦋0⦌) (ULift.up (x, PUnit.unit))) =
        coherentNerveEdge (parameterHom (A.unitHomEquiv.symm x)) := by
  apply SSet.Edge.ext
  have h := coherentHomComparison_ordinary
    (parameterHom.{u, v} (A.unitHomEquiv.symm x))
  rw [parameterHom_vertex, Equiv.apply_symm_apply] at h
  exact h

/-- パラメータの辺は、先頭辺が恒等で、残りが両端の評価である実際の三角形を与える。 -/
def parameterCompStruct {x y : A _⦋0⦌} (e : A.Edge x y) :
    SSet.Edge.CompStruct (SSet.Edge.id (leftVertex.{u, v} A))
      (coherentNerveEdge (parameterHom (A.unitHomEquiv.symm y)))
      (coherentNerveEdge (parameterHom (A.unitHomEquiv.symm x))) := by
  let e' := (parameterHomEdge.{u, v} e).map
    (coherentHomComparison
      (⟨false, ⟨PUnit.unit⟩⟩ : Object A Point.{v}) ⟨true, ⟨PUnit.unit⟩⟩)
  have h := PinchedHom.pathCompStruct e'
  erw [parameterComparisonVertex.{u, v} (A := A) y,
    parameterComparisonVertex.{u, v} (A := A) x] at h
  exact h

/-- パラメータの辺が与える、二対象の円柱内の標準二単体の図式。 -/
def parameterTriangle {x y : A _⦋0⦌} (e : A.Edge x y) :
    (Δ[2] : SSet.{max u v}) ⟶ SimplicialNerve (Object A Point.{v}) :=
  SSet.yonedaEquiv.symm (parameterCompStruct.{u, v} e).simplex

/-- パラメータ三角形の 1–2 辺は終点パラメータでの辺。 -/
lemma parameterTriangle_target {x y : A _⦋0⦌} (e : A.Edge x y) :
    stdSimplex.δ (0 : Fin 3) ≫ parameterTriangle.{u, v} e =
      parameterEdge (A.unitHomEquiv.symm y) := by
  rw [parameterTriangle, SSet.Edge.CompStruct.δ_zero_yonedaEquiv_symm, parameterEdge_eq]

/-- パラメータ三角形の 0–2 辺は始点パラメータでの辺。 -/
lemma parameterTriangle_source {x y : A _⦋0⦌} (e : A.Edge x y) :
    stdSimplex.δ (1 : Fin 3) ≫ parameterTriangle.{u, v} e =
      parameterEdge (A.unitHomEquiv.symm x) := by
  rw [parameterTriangle, SSet.Edge.CompStruct.δ_one_yonedaEquiv_symm, parameterEdge_eq]

/-- パラメータ三角形の 0–1 辺は左端の恒等辺。 -/
lemma parameterTriangle_identity {x y : A _⦋0⦌} (e : A.Edge x y) :
    stdSimplex.δ (2 : Fin 3) ≫ parameterTriangle.{u, v} e = SSet.const (leftVertex A) := by
  rw [parameterTriangle, SSet.Edge.CompStruct.δ_two_yonedaEquiv_symm]
  apply SSet.yonedaEquiv.injective
  rw [Equiv.apply_symm_apply]
  change (SimplicialNerve (Object A Point.{v})).σ 0 (leftVertex A) =
    PinchedHom.constant (leftVertex A) 1
  exact (PinchedHom.constant_one _).symm

end SerrePositivity.KST.Spectra.EnrichedParameterCylinder
