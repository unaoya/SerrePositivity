module

public import SerrePositivity.InfinityCategories.F1.BoundaryFactorization
public import SerrePositivity.InfinityCategories.F1.MappingCylinderTargetComparison
public import SerrePositivity.InfinityCategories.F1B.KanSectionMappingCylinderIntervalEquivalence

/-!
概要：quasicategory の任意の関手の写像円柱の比較。
方針：構造射を単射と trivial Kan fibration に分解し、終域変更の円柱比較で単射の場合から戻す。
規約：構造射の単射性は仮定しない。
使われ方：Kerodon Theorem 5.2.4.1、因子が quasicategory の場合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.KanSection

attribute [local instance] vertexFiber_quasicategory_of_innerFibration

/-- 概要：quasicategory の関手の写像円柱は両端の同値と垂直辺の cocartesian 性で前合成同値になる。
方針：終域を同値な quasicategory へ置き換えて単射の場合を適用し、円柱の比較の同値を消去する。
規約：X・Y・E は quasicategory、f は任意。
使われ方：Kerodon Theorem 5.2.4.1、一般の単体集合への因子の置換の準備。 -/
lemma mappingCylinder_isPrecompositionEquivalence_of_quasicategory_factors
    {X Y E : SSet.{u}} [Quasicategory X] [Quasicategory Y] [Quasicategory E]
    (f : X ⟶ Y) (p : E ⟶ (Δ[1] : SSet.{u}))
    (H : (Δ[1] : SSet.{u}) ⊗ X ⟶ E) (g : Y ⟶ E)
    (w : prismEndpoint 1 X ≫ H = f ≫ g) (hH : H ≫ p = fst Δ[1] X)
    (hg : g ≫ p = SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
    (z0 : X ⟶ vertexFiber p (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))
    (hz0 : z0 ≫ vertexFiberι p (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) = prismEndpoint 0 X ≫ H)
    (z1 : Y ⟶ vertexFiber p (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
    (hz1 : z1 ≫ vertexFiberι p (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) = g)
    (he0 : IsPrecompositionEquivalence z0) (he1 : IsPrecompositionEquivalence z1)
    (hc : ∀ x : X _⦋0⦌, IsCocartesianEdge p (prismVerticalSimplex H x)) :
    IsPrecompositionEquivalence (pushout.desc H g w) := by
  obtain ⟨Z, i, q, hi, hq, hfac⟩ := exists_mono_trivialKan_factorization f
  have : Mono i := hi
  have : TrivialKanFibration q := hq
  have : Quasicategory Z := quasicategory_of_innerFibration q
  have hqe : IsPrecompositionEquivalence q :=
    (isQCatEquivalence_of_trivialKanFibration q).isPrecompositionEquivalence
  have wi : prismEndpoint 1 X ≫ H = i ≫ (q ≫ g) := by
    rw [← Category.assoc, hfac]
    exact w
  have hgi : (q ≫ g) ≫ p = SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) := by
    rw [Category.assoc, hg, SSet.comp_const]
  have hzi : (q ≫ z1) ≫ vertexFiberι p (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) = q ≫ g := by
    rw [Category.assoc, hz1]
  have hmono := mappingCylinder_isPrecompositionEquivalence_of_quasicategories i p H (q ≫ g)
    wi hH hgi z0 hz0 (q ≫ z1) hzi he0 (hqe.comp he1) hc
  apply (mappingCylinderTargetMap_isPrecompositionEquivalence f i q hfac hqe).cancel_left
  rw [mappingCylinderTargetMap_desc f i q hfac H g w wi]
  exact hmono

end SerrePositivity.InfinityCategories.KanSection
