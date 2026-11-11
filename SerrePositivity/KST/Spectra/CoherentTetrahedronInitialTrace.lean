module

public import SerrePositivity.KST.Spectra.CoherentTriangleDegenerateTrace
public import SerrePositivity.KST.Spectra.CoherentSimplexCompositionFaces

/-!
概要：三単体の最初の辺の trace は、元の apex 辺の Hom 頂点の定値経路。
方針：最初の二頂点への面写像の path を計算する。
規約：元の三単体とその面を保持。使われ方：比較正方形の右辺を前合成へ戻す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory SimplicialThickening MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.CoherentPathCoordinates
variable {C : Type v} [Category.{u} C] [SimplicialCategory C]

/-- 最初の二頂点への二つの面は、元の順序辺の同じ包含。 -/
lemma tetrahedronApex_faces :
    stdSimplex.δ (2 : Fin 3) ≫ stdSimplex.δ (3 : Fin 4) =
      SSet.yonedaEquiv.symm (stdSimplex.edge.{u} 3 0 1 (by decide)) := by
  apply SSet.yonedaEquiv.injective
  apply SSet.stdSimplex.ext
  intro i
  fin_cases i <;> rfl

/-- 最初の辺への面制限は、元の順序辺の Yoneda 制限そのもの。 -/
lemma tetrahedronApex_yoneda (σ : (SimplicialNerve C) _⦋3⦌) :
    (SimplicialNerve C).δ 2 ((SimplicialNerve C).δ 3 σ) = SSet.yonedaEquiv
      (SSet.yonedaEquiv.symm (stdSimplex.edge 3 0 1 (by decide)) ≫
        SSet.yonedaEquiv.symm σ) := by
  rw [← tetrahedronApex_faces, Category.assoc, stdSimplex.yonedaEquiv_δ_comp,
    stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply]

/-- 元の最初の辺への制限で読み取った Hom 頂点は、元の initial trace の定値。 -/
lemma tetrahedronInitialTrace_apex (σ : (SimplicialNerve C) _⦋3⦌) :
    tetrahedronInitialTrace σ = SSet.const
      (((SimplicialNerve C).δ 2 ((SimplicialNerve C).δ 3 σ)).map
        ⟨ULift.up 0⟩ ⟨ULift.up 1⟩ |>.app (Opposite.op ⦋0⦌)
          (ComposableArrows.mk₀ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentOnePath)) := by
  rw [tetrahedronInitialTrace, constantPathParameter_eq_const, SSet.const_comp]
  congr 1
  apply congrArg ((σ.map ⟨ULift.up 0⟩ ⟨ULift.up 1⟩).app (Opposite.op ⦋0⦌))
  refine CategoryTheory.Functor.ext (fun r ↦ ?_) ?_
  · fin_cases r
    apply SimplicialThickening.Path.ext
    ext i
    change (i.down = 0 ∨ i.down = 1) ↔ i ∈
      (SimplexCategory.δ (3 : Fin 4)).toOrderHom.uliftMap ''
        ((SimplexCategory.δ (2 : Fin 3)).toOrderHom.uliftMap '' Set.univ)
    rcases i with ⟨i⟩
    fin_cases i <;> simp only [Set.mem_image, Set.mem_univ, ULift.exists,
      Fin.exists_fin_succ, Fin.exists_fin_zero] <;> decide
  · intro i j f
    exact Subsingleton.elim _ _

/-- apex 辺の厳密等式は、端点を移した元の initial trace の定値表示を与える。 -/
lemma tetrahedronInitialTrace_of_apex {σ : (SimplicialNerve C) _⦋3⦌}
    {τ : (SimplicialNerve C) _⦋1⦌}
    (h : (SimplicialNerve C).δ 2 ((SimplicialNerve C).δ 3 σ) = τ) :
    tetrahedronInitialTrace σ ≫ eqToHom (congrArg
      (fun s : (SimplicialNerve C) _⦋1⦌ ↦
        SimplicialCategory.sHom (s.obj ⟨ULift.up 0⟩) (s.obj ⟨ULift.up 1⟩)) h) =
      SSet.const ((τ.map ⟨ULift.up 0⟩ ⟨ULift.up 1⟩).app (Opposite.op ⦋0⦌)
        (ComposableArrows.mk₀ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentOnePath)) := by
  cases h
  rw [eqToHom_refl, Category.comp_id, tetrahedronInitialTrace_apex]

end SerrePositivity.KST.Spectra.CoherentPathCoordinates
