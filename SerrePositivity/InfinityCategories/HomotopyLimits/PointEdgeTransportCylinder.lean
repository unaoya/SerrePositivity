module

public import SerrePositivity.InfinityCategories.HomotopyLimits.PrismTransportPointEvaluation

/-!
概要：実際の辺と標準の点輸送を結ぶ指定円柱を、一点係数の prism 比較に移す。
方針：同じ円柱を第一射影で前合成し、底と初期値をそのまま保持する。
規約：比較を選び直さない。使われ方：左三角形の初辺から付加辺輸送への照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {E B : SSet.{u}} (p : E ⟶ B) [LeftFibration p]
  {a b : B _⦋0⦌} (e : B.Edge a b) (v : (vertexFiber p a) _⦋0⦌)
  (W : (Δ[1] : SSet.{u}) ⟶ E)
  (M : SSet.Homotopy W (prismVertexEvaluation (transportEdgePrism p e) v))
  (hM : M.h ≫ p = fst (Δ[1] : SSet.{u}) Δ[1] ≫ SSet.yonedaEquiv.symm e.edge)
  (hM₀ : (scaffoldFirstVertex 1 ▷ (Δ[1] : SSet.{u})) ≫ M.h =
    fst (Δ[0] : SSet.{u}) Δ[1] ≫ SSet.yonedaEquiv.symm v.val)

/-- 指定された辺の円柱を、同じ始点の一点係数 prism の比較円柱へ戻す。 -/
def pointEdgeTransportCylinder :
    PrismTransportCylinder p e (SSet.yonedaEquiv.symm v)
      (fst (Δ[1] : SSet.{u}) Δ[0] ≫ W) := by
  let K := functorHomotopyPrecomp M (fst (Δ[1] : SSet.{u}) (Δ[0] : SSet.{u}))
  refine
    { homotopy :=
        { h := K.h
          h₀ := K.h₀
          h₁ := K.h₁.trans
            (prismParameterPrecomp_point (transportEdgePrism p e) v).symm
          rel := by
            apply SSet.hom_ext
            intro n
            apply ConcreteCategory.hom_ext
            intro z
            exact False.elim z.1.property }
      projection := ?_
      initial := ?_ }
  · change ((fst (Δ[1] : SSet.{u}) Δ[0] ▷ (Δ[1] : SSet.{u})) ≫ M.h) ≫ p = _
    rw [Category.assoc, hM, ← Category.assoc, whiskerRight_fst, Category.assoc]
  · change ((scaffoldFirstVertex 1 ▷ (Δ[0] : SSet.{u})) ▷ (Δ[1] : SSet.{u})) ≫
      ((fst (Δ[1] : SSet.{u}) Δ[0] ▷ (Δ[1] : SSet.{u})) ≫ M.h) = _
    rw [← Category.assoc, ← MonoidalCategory.comp_whiskerRight, whiskerRight_fst,
      MonoidalCategory.comp_whiskerRight, Category.assoc, hM₀,
      ← Category.assoc, whiskerRight_fst]
    simp only [SSet.yonedaEquiv_symm_zero, Category.assoc, SSet.comp_const, SSet.const_comp]
    rfl

/-- 一点 prism の円柱も、元の指定円柱の raw な射を前合成したものそのもの。 -/
lemma pointEdgeTransportCylinder_raw :
    (pointEdgeTransportCylinder p e v W M hM hM₀).homotopy.h =
      (fst (Δ[1] : SSet.{u}) Δ[0] ▷ (Δ[1] : SSet.{u})) ≫ M.h := rfl

variable (g : (Δ[0] : SSet.{u}) ⟶ vertexFiber p b)
  (hW₁ : prismEndpoint 1 Δ[0] ≫ (fst (Δ[1] : SSet.{u}) Δ[0] ≫ W) = g ≫ vertexFiberι p b)

/-- 同じ指定円柱の終点を、一点からの fiber への射の間のホモトピーとして保持する。 -/
def pointEdgeTransportEndpointHomotopy :
    SSet.Homotopy g (SSet.yonedaEquiv.symm v ≫ edgeTransport p e) :=
  prismCylinderEndpointHomotopy p e (SSet.yonedaEquiv.symm v)
    (fst (Δ[1] : SSet.{u}) Δ[0] ≫ W)
    (pointEdgeTransportCylinder p e v W M hM hM₀) g hW₁

/-- 終点の円柱も、元の辺の比較円柱を終点で制限した raw な射そのもの。 -/
lemma pointEdgeTransportEndpointHomotopy_projection :
    (pointEdgeTransportEndpointHomotopy p e v W M hM hM₀ g hW₁).h ≫ vertexFiberι p b =
      (stdSimplex.δ (0 : Fin 2) ▷ (Δ[1] : SSet.{u})) ≫ M.h := by
  rw [pointEdgeTransportEndpointHomotopy, prismCylinderEndpointHomotopy_projection,
    pointEdgeTransportCylinder_raw, ← Category.assoc, ← MonoidalCategory.comp_whiskerRight]
  have hj : prismEndpoint 1 (Δ[0] : SSet.{u}) ≫ fst (Δ[1] : SSet.{u}) Δ[0] =
      stdSimplex.δ (0 : Fin 2) := by
    rw [prismEndpoint, lift_fst, stdSimplex.δ_zero_eq_const]
  rw [hj]

/-- 同じ指定円柱の終点の類は、元の一点 prism に対する既存の輸送比較の射である。 -/
lemma pointEdgeTransportEndpointHomotopy_hom
    (hW₀ : prismEndpoint 0 Δ[0] ≫ (fst (Δ[1] : SSet.{u}) Δ[0] ≫ W) =
      SSet.yonedaEquiv.symm v ≫ vertexFiberι p a)
    (hWp : (fst (Δ[1] : SSet.{u}) Δ[0] ≫ W) ≫ p =
      fst (Δ[1] : SSet.{u}) Δ[0] ≫ SSet.yonedaEquiv.symm e.edge) :
    SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
      (pointEdgeTransportEndpointHomotopy p e v W M hM hM₀ g hW₁)) =
      (leftFibrationPrism_transportIso p e (SSet.yonedaEquiv.symm v) g
        (fst (Δ[1] : SSet.{u}) Δ[0] ≫ W) hW₀ hW₁ hWp).hom :=
  prismCylinderEndpointHomotopy_hom p e (SSet.yonedaEquiv.symm v)
    (fst (Δ[1] : SSet.{u}) Δ[0] ≫ W) hW₀ hWp
    (pointEdgeTransportCylinder p e v W M hM hM₀) g hW₁

end
end SerrePositivity.InfinityCategories.HomotopyLimits
