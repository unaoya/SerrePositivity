module

public import SerrePositivity.InfinityCategories.F2.CatInfinity.NativeConeTriangle
public import SerrePositivity.InfinityCategories.Stable.FiniteShapes
public import SerrePositivity.KST.Spectra.DiagramLimitExistenceTransport

/-!
概要：cospan 錐の正方形の下辺を、元の錐の左脚として計算する。
方針：正方形の下側三角形の面を join の二点間の辺へ戻す。
規約：射の類だけでなく元の一次単体を保持する。使われ方：K-5 の fiber 包含の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants.ConeSquareLeg

/-- cospan の左辺の始点。 -/
def leftVertex : (horn 2 2 : SSet.{u}) _⦋0⦌ :=
  (horn 2 2 : SSet.{u}).δ 1 (SSet.yonedaEquiv horn₂₂.ι₀₂)

lemma leftVertex_map : SSet.yonedaEquiv.symm leftVertex.{u} =
    stdSimplex.δ (1 : Fin 2) ≫ horn₂₂.ι₀₂ := by
  apply SSet.yonedaEquiv.injective
  rw [Equiv.apply_symm_apply, stdSimplex.yonedaEquiv_δ_comp]
  rfl

lemma triangle_face :
    stdSimplex.δ (2 : Fin 3) ≫ cospanConeTriangleLeft.{u} =
      F2.coneLegInclusion leftVertex := by
  have h := F2.coneTriangleInclusion_face horn₂₂.ι₀₂ (1 : Fin 2)
  change stdSimplex.δ (2 : Fin 3) ≫ cospanConeTriangleLeft.{u} =
    (joinStdSimplexIso 0 0).inv ≫ joinMap (𝟙 Δ[0]) (stdSimplex.δ (1 : Fin 2) ≫
      horn₂₂.ι₀₂) at h
  simpa only [F2.coneLegInclusion, leftVertex_map] using h

/-- 四角形の下辺は錐の左脚そのもの。 -/
lemma bottom {X : SSet.{u}} {p : (horn 2 2 : SSet.{u}) ⟶ X} (c : JoinCone p) :
    squareBottomEdge ≫ coneSquare c = F2.coneLegInclusion leftVertex ≫ c.val := by
  have hface : stdSimplex.δ (2 : Fin 3) ≫ squareTriangle.{u} 1 = squareBottomEdge := by
    apply SSet.yonedaEquiv.injective
    apply Prod.ext <;> decide
  rw [← hface, ← cospanConeSquareIso_left, Category.assoc]
  change stdSimplex.δ (2 : Fin 3) ≫
    (cospanConeTriangleLeft ≫ cospanConeSquareIso.hom) ≫
      (cospanConeSquareIso.inv ≫ c.val) = _
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc, triangle_face]

/-- 形状の制限は指定した頂点への元の脚を保つ。 -/
lemma leg_restrict {K L X : SSet.{u}} {p : K ⟶ X}
    (c : JoinCone p) (i : L ⟶ K) (k : L _⦋0⦌) :
    F2.coneLegInclusion k ≫ (DiagramLimitTransport.restrict c i).val =
      F2.coneLegInclusion (i.app (Opposite.op ⦋0⦌) k) ≫ c.val := by
  change ((joinStdSimplexIso 0 0).inv ≫ joinMap (𝟙 Δ[0]) (SSet.yonedaEquiv.symm k)) ≫
    (joinMap (𝟙 Δ[0]) i ≫ c.val) = _
  have hj : joinMap (𝟙 (Δ[0] : SSet.{u})) (SSet.yonedaEquiv.symm k) ≫
      joinMap (𝟙 Δ[0]) i =
    joinMap (𝟙 Δ[0]) (SSet.yonedaEquiv.symm (i.app (Opposite.op ⦋0⦌) k)) := by
    rw [← joinMap_comp, Category.id_comp, SSet.yonedaEquiv_symm_comp]
  simpa only [Category.assoc, F2.coneLegInclusion] using
    congrArg (fun q ↦ (joinStdSimplexIso 0 0).inv ≫ q ≫ c.val) hj

end SerrePositivity.KST.LocalizingInvariants.ConeSquareLeg
