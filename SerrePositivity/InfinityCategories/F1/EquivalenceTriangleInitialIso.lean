module

public import SerrePositivity.InfinityCategories.F1.EquivalenceTriangleEvaluation
public import SerrePositivity.InfinityCategories.F1.TriangleInitialContractionInvertible
public import SerrePositivity.InfinityCategories.F1.FullyFaithfulPostcomposition
public import SerrePositivity.InfinityCategories.F1B.RestrictedPrecomposition

/-!
概要：可逆三角形の初頂点評価から同じ元の三角形への全体の関手同型。
方針：元の縮約の制限前合成を使い、全部分複体の充満忠実性で同型を戻す。
規約：頂点ごとに別の同型を選ばず、全高次の族を保持する。
使われ方：三角形の各面の Hom 射影の同値性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 元の可逆三角形の全族上では、初頂点への変形の前合成は関手同型。 -/
def equivalenceTriangleInitialAmbientIso (Y : SSet.{u}) [Quasicategory Y] :
    FunctorIso
      (equivalenceTriangleι Y ≫ (pre (SSet.const
        (stdSimplex.obj₀Equiv.symm (0 : Fin 3)) : (Δ[2] : SSet.{u}) ⟶ Δ[2])).app Y)
      (equivalenceTriangleι Y) := by
  have e := functorIsoRestrictedPrecompositionOfHomotopy triangleInitialContraction
    (equivalenceTriangleι Y) (by
      intro v f hf a
      have hv := fullSubcomplexOnVertices_vertex v
      change v.val = functorVertex f at hf
      have h : IsEquivalenceTriangleVertex (functorVertex f) := hf ▸ hv
      exact triangleInitialContraction_mapped_isInvertible f h a)
  simpa only [pre_id, NatTrans.id_app, Category.comp_id] using e

/-- 初頂点で評価して定値三角形にした全族は、同じ元の可逆三角形の全族と同型。 -/
def equivalenceTriangleInitialIso (Y : SSet.{u}) [Quasicategory Y] :
    FunctorIso (equivalenceTriangleEvaluation Y 0 ≫ equivalenceTriangleConstant Y)
      (𝟙 (equivalenceTriangle Y)) := by
  apply (isFullyFaithful_fullSubcomplexOnVertices_ι
    ((ihom (Δ[2] : SSet.{u})).obj Y) IsEquivalenceTriangleVertex).preimageFunctorIso
  change FunctorIso ((equivalenceTriangleEvaluation Y 0 ≫ equivalenceTriangleConstant Y) ≫
    equivalenceTriangleι Y) (𝟙 (equivalenceTriangle Y) ≫ equivalenceTriangleι Y)
  simpa only [Category.assoc, equivalenceTriangleConstant_ι,
    equivalenceTriangleEvaluation_zero_constant, Category.id_comp] using
      equivalenceTriangleInitialAmbientIso Y

end SerrePositivity.InfinityCategories
