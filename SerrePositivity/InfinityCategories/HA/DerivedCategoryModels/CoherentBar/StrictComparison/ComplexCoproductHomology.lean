module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.ComplexColimit
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import SerrePositivity.DifferentialGraded.Complexes.HomComplex
public import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
概要：非有界加群複体の直和のホモロジーを、成分ホモロジーの直和へ同定する。
方針：ModuleCat の AB4 による完全な直和を短複体へ適用する。
規約：全整数次数を扱い、下方有界性を仮定しない。
使われ方：実 coherent bar の次元層の内部ホモロジー。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
open CategoryTheory Limits DifferentialGraded HomologicalComplex
variable (R : Type u) [CommRing R] {I : Type u} (K : I → Complex R) (q : ℤ)

def dgComplexCoproductHomologyDiagramIso :
    Discrete.functor (fun i => (K i).homology q) ≅
      ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgStrictComplexDiagram R (Discrete.functor K)).sc' (q - 1) q (q + 1)).homology := by
  let S := (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgStrictComplexDiagram R (Discrete.functor K)).sc' (q - 1) q (q + 1)
  refine NatIso.ofComponents (fun i =>
    (K i.as).homologyIsoSc' (q - 1) q (q + 1) (by simp) (by simp) ≪≫
      S.mapHomologyIso ((evaluation (Discrete I) (ModuleCat R)).obj i)) ?_
  intro i j f
  have hij : i = j := Discrete.ext (Discrete.eq_of_hom f)
  subst j
  have hf : f = 𝟙 i := Subsingleton.elim _ _
  subst f
  simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]

def dgComplexCoproductColimitIso :
    ((colim (J := Discrete I) (C := ModuleCat.{u} R)).mapHomologicalComplex (.up ℤ)).obj
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgStrictComplexDiagram R (Discrete.functor K)) ≅ ∐ K :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgStrictComplexColimitIso R (Discrete.functor K) ≪≫
    ((coproductIsCoproduct K).coconePointUniqueUpToIso
      (colimit.isColimit (Discrete.functor K))).symm

def dgComplexCoproductHomologyIso : (∐ K).homology q ≅ ∐ fun i => (K i).homology q := by
  let T := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgStrictComplexDiagram R (Discrete.functor K)
  let S := T.sc' (q - 1) q (q + 1)
  let L := ((colim (J := Discrete I) (C := ModuleCat.{u} R)).mapHomologicalComplex (.up ℤ)).obj T
  exact (HomologicalComplex.homologyMapIso (dgComplexCoproductColimitIso R K) q).symm ≪≫
    L.homologyIsoSc' (q - 1) q (q + 1) (by simp) (by simp) ≪≫
    S.mapHomologyIso (colim (J := Discrete I) (C := ModuleCat.{u} R)) ≪≫
    (colim.mapIso (dgComplexCoproductHomologyDiagramIso R K q)).symm ≪≫
    ((coproductIsCoproduct (fun i => (K i).homology q)).coconePointUniqueUpToIso
      (colimit.isColimit (Discrete.functor (fun i => (K i).homology q)))).symm

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
