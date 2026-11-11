module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentFunctorCospan
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.FunctorLimits

/-!
概要：元の共通対角円柱を持つ二三角形を、関手 ∞ 圏の元の全 cospan 錐へ貼る。
方針：cospan の錐形状の厳密な pushout を使う。
規約：左右二単体と共通対角辺を保持。使われ方：各点の元の錐と native cospan の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}}
  {F X Y Z : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {a : SSet.Homotopy F X} {b : SSet.Homotopy F Y}
  {f : SSet.Homotopy X Z} {g : SSet.Homotopy Y Z} {d : SSet.Homotopy F Z}
  (L : FunctorCompositionTriangle a f d) (R : FunctorCompositionTriangle b g d)

/-- 二つの元の関手三角形を共通の指定対角辺で貼った全錐図式。 -/
def functorCospanConeDiagram : join (Δ[0] : SSet.{u + 1}) (horn 2 2 : SSet.{u + 1}) ⟶
    (ihom ((SSet.uliftFunctor.{u + 1, u}).obj B)).obj SpaceInfinity.{u} :=
  cospanCone_isPushout.desc L.diagram R.diagram (by rw [L.face_one, R.face_one])

/-- 元の左三角形は全単体を保って回収される。 -/
lemma functorCospanConeDiagram_left :
    cospanConeTriangleLeft ≫ functorCospanConeDiagram L R = L.diagram :=
  cospanCone_isPushout.inl_desc _ _ _

/-- 元の右三角形は全単体を保って回収される。 -/
lemma functorCospanConeDiagram_right :
    cospanConeTriangleRight ≫ functorCospanConeDiagram L R = R.diagram :=
  cospanCone_isPushout.inr_desc _ _ _

/-- 元の二三角形から貼った、元の関手圏内の cospan 錐。 -/
def functorCospanCone : JoinCone (joinInr Δ[0] (horn 2 2 : SSet.{u + 1}) ≫
    functorCospanConeDiagram L R) := ⟨functorCospanConeDiagram L R, rfl⟩

/-- 元の全錐の頂点関手は、元の入力 F そのもの。 -/
lemma functorCospanCone_vertex : (functorCospanCone L R).vertex = functorVertex F := by
  have he : (stdSimplex.δ (1 : Fin 2) : (Δ[0] : SSet.{u + 1}) ⟶ Δ[1]) ≫
      stdSimplex.δ (2 : Fin 3) ≫ cospanConeTriangleLeft = joinInl Δ[0] (horn 2 2) := by
    have hi : (stdSimplex.δ (1 : Fin 2) : (Δ[0] : SSet.{u + 1}) ⟶ Δ[1]) ≫
        stdSimplex.δ (2 : Fin 3) ≫ (joinStdSimplexIso 0 1).inv = joinInl Δ[0] Δ[1] := by
      apply (cancel_mono (joinStdSimplexIso 0 1).hom).1
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      apply SSet.yonedaEquiv.injective
      decide
    have h := congrArg (fun q => q ≫ joinMap (𝟙 (Δ[0] : SSet.{u + 1})) horn₂₂.ι₀₂) hi
    rw [joinInl_joinMap, Category.id_comp] at h
    simpa only [cospanConeTriangleLeft, Category.assoc] using h
  have hv : joinInl Δ[0] (horn 2 2) ≫ functorCospanConeDiagram L R =
      SSet.const (functorVertex F) := by
    rw [← he, Category.assoc, Category.assoc, functorCospanConeDiagram_left]
    exact L.vertex_zero
  rw [JoinCone.vertex_eq]
  change SSet.yonedaEquiv (joinInl Δ[0] (horn 2 2) ≫ functorCospanConeDiagram L R) = _
  rw [hv, SSet.yonedaEquiv_const]

end SerrePositivity.InfinityCategories.F2
