module

public import SerrePositivity.HomologicalAlgebra.KoszulCoordinateControl
public import SerrePositivity.HomologicalAlgebra.KoszulScalarControl

/-! # 列のイデアルと係数の零化元による Koszul ホモロジーの零化

最後の元が前の列と係数の零化元の生成イデアルに属する場合、
前の列のホモロジーに対する最後の元の作用は零になる。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity
open CategoryTheory
variable {R : Type u} [CommRing R]

/-- 列のイデアルと係数の零化元が生成するイデアルは、Koszul ホモロジーを消す。 -/
theorem koszulModuleHomology_smul_zero_of_mem_span_sup
    {e : ℕ} (z : Fin e → R) (M : ModuleCat.{u} R) (a r : R)
    (ha : ∀ m : M, a • m = 0)
    (hr : r ∈ Ideal.span (Set.range z) ⊔ Ideal.span {a}) (q : ℤ) :
    ∀ x : ((koszulModuleFunctor z).obj M).homology q, r • x = 0 := by
  have hs := span_le_annihilator_koszulModuleHomology z M q
  have hA : Ideal.span {a} ≤ Module.annihilator R (((koszulModuleFunctor z).obj M).homology q) := by
    rw [Ideal.span_singleton_le_iff_mem, Module.mem_annihilator]
    exact koszulModuleHomology_annihilated z M a ha q
  exact Module.mem_annihilator.mp ((sup_le hs hA) hr)

/-- 最後の元の所属条件と係数の零化から、前の列上のホモロジー写像の零性を供給する。 -/
theorem koszul_last_homologyMap_eq_zero_of_mem_span_sup
    {e : ℕ} (z : Fin (e + 1) → R) (M : ModuleCat.{u} R) (a : R)
    (ha : ∀ m : M, a • m = 0)
    (hz : z (Fin.last e) ∈ Ideal.span (Set.range (Fin.init z)) ⊔ Ideal.span {a}) (q : ℤ) :
    HomologicalComplex.homologyMap
      (smulId (z (Fin.last e)) ((koszulModuleFunctor (Fin.init z)).obj M)) q = 0 := by
  rw [smulId, homologyMap_smul, HomologicalComplex.homologyMap_id]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact koszulModuleHomology_smul_zero_of_mem_span_sup (Fin.init z) M a (z (Fin.last e)) ha hz q x

end SerrePositivity
