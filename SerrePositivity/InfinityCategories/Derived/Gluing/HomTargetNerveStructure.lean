module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetCommaFunctor
public import SerrePositivity.InfinityCategories.Derived.DGCommaAugUnlifted
public import SerrePositivity.InfinityCategories.F1B.HomotopyPrecompVertex
/-!
概要：元二脚の Hom gluing の augmentation を、元の共通終域の全単体族として公開する。
方針：元終域への comma dg 関手で既存の実 augmentation prism を引き戻す。
規約：導来係数への制限で代用せず、元の左右射影と閉比較辺を保持する。
使われ方：元二脚と恒等二脚の lax 全比較の指定された比較写像。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory DifferentialGraded DGNerve SSet
open KST.SConstruction
open scoped Simplicial
variable (R : Type u) [CommRing R]
  (C D E : Type (max (u + 1) v)) [DGCategory R C] [Small.{u} C]
  [DGCategory R D] [DGCategory R E] [Small.{u} E]
  (p : DGFunctor R C E) (q : DGFunctor R D E)
local notation "M" => dgHomGluingBimodule R C D E p q
local notation "G" => DGGluingObject R C D M

/-- 元の終域における比較射の全単体ホモトピー。 -/
def dgGluingHomTargetAugmentationHomotopy :
    SSet.Homotopy
      (dgNerve.map (dgGluingLeft R C D M) ≫ dgNerve.map p)
      (dgNerve.map (dgGluingRight R C D M) ≫ dgNerve.map q) where
  h := (dgNerve.map (dgGluingHomTargetToComma R C D E p q) ▷ (Δ[1] : SSet)) ≫
    (dgCommaAugmentationUnliftedHomotopy R D E q).h
  h₀ := by
    rw [← Category.assoc, SSet.ι₀_comp, Category.assoc,
      SSet.Homotopy.h₀, ← dgNerve.map_comp]
    change dgNerve.map ((dgGluingHomTargetToComma R C D E p q).comp
      (dgFunctorCommaReplacement R D E q)) = _
    rw [dgGluingHomTargetToComma_replacement, dgNerve.map_comp]
    rfl
  h₁ := by
    rw [← Category.assoc, SSet.ι₁_comp, Category.assoc,
      SSet.Homotopy.h₁, ← dgNerve.map_comp]
    change dgNerve.map ((dgGluingHomTargetToComma R C D E p q).comp
      ((dgFunctorCommaSource R D E q).comp q)) = _
    change dgNerve.map (((dgGluingHomTargetToComma R C D E p q).comp
      (dgFunctorCommaSource R D E q)).comp q) = _
    rw [dgGluingHomTargetToComma_source, dgNerve.map_comp]
    rfl
  rel := by
    ext n s
    exact False.elim s.1.2

/-- 全単体比較の各頂点では、元の閉比較射を回収する。 -/
lemma dgGluingHomTargetAugmentationHomotopy_vertex_edge (X : G) :
    (simplicialHomotopyVertexEdge (dgGluingHomTargetAugmentationHomotopy R C D E p q)
      (Simplex.vertex X)).edge =
    (dgClosedEdge R E (dgHomGluingTargetMap R C D E p q X)).edge := by
  change (simplicialHomotopyVertexEdge
    (functorHomotopyPrecomp (dgCommaAugmentationUnliftedHomotopy R D E q)
      (dgNerve.map (dgGluingHomTargetToComma R C D E p q))) (Simplex.vertex X)).edge = _
  rw [simplicialHomotopyVertexEdge_precomp_edge]
  have hx : (dgNerve.map (dgGluingHomTargetToComma R C D E p q)).app
      (Opposite.op ⦋0⦌) (Simplex.vertex X) =
      Simplex.vertex (dgGluingHomTargetCommaObject R C D E p q X) := by
    apply (Simplex.vertexEquiv (A := R) (D := DGFunctorCommaObject R D E q)).injective
    rfl
  rw [hx]
  exact dgCommaAugmentationUnliftedHomotopy_vertex_edge R D E q _

end SerrePositivity.InfinityCategories
