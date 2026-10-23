module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitRawInterval
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitConstantTriangle

/-!
概要：元の定値余極限三角形の三面を、元の両余錐頂点間の同じ全区間族で照合する。
方針：元の全三角形の面と元の定値区間族の厳密な一致を合成する。
規約：三辺も全三角形も選び直さない。使われ方：同じ長辺証拠を輸送比較へ渡す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {a : SSet.Homotopy F G} {b : SSet.Homotopy G J} {c : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle a b c)
local notation "V" => coherentTriangleOfFunctorTriangle (coherentColimitConstantTriangle B T)
local notation "H" => CoherentTransformationVertexTriangle.diagram V

/-- 元の最初の面は、元の最初の余極限区間族の定値図式そのもの。 -/
lemma coherentColimitConstantTriangle_first_rawInterval :
    (stdSimplex.δ (2 : Fin 3) ▷
      (((SSet.uliftFunctor.{u + 1, u}).obj B) ⊗ (Δ[0] : SSet.{u + 1}))) ≫ H =
      coherentTransformationFamilyDiagram
        (constantDiagramTransformation ((SSet.uliftFunctor.{u + 1, u}).obj B)
        (SSet.yonedaEquiv.symm (coherentColimitRawIntervalVertex B a))) := by
  have h := coherentColimitRawIntervalVertex_constant B a
  rw [SSet.yonedaEquiv_symm_zero] at h
  exact (V).first.trans (congrArg coherentTransformationFamilyDiagram h.symm)

/-- 元の最後の面も、元の最後の余極限区間族の定値図式そのもの。 -/
lemma coherentColimitConstantTriangle_last_rawInterval :
    (stdSimplex.δ (0 : Fin 3) ▷
      (((SSet.uliftFunctor.{u + 1, u}).obj B) ⊗ (Δ[0] : SSet.{u + 1}))) ≫ H =
      coherentTransformationFamilyDiagram
        (constantDiagramTransformation ((SSet.uliftFunctor.{u + 1, u}).obj B)
        (SSet.yonedaEquiv.symm (coherentColimitRawIntervalVertex B b))) := by
  have h := coherentColimitRawIntervalVertex_constant B b
  rw [SSet.yonedaEquiv_symm_zero] at h
  exact (V).second.trans (congrArg coherentTransformationFamilyDiagram h.symm)

/-- 元の長辺の面も、元の共有対角の余極限区間族を厳密に回収する。 -/
lemma coherentColimitConstantTriangle_long_rawInterval :
    (stdSimplex.δ (1 : Fin 3) ▷
      (((SSet.uliftFunctor.{u + 1, u}).obj B) ⊗ (Δ[0] : SSet.{u + 1}))) ≫ H =
      coherentTransformationFamilyDiagram
        (constantDiagramTransformation ((SSet.uliftFunctor.{u + 1, u}).obj B)
        (SSet.yonedaEquiv.symm (coherentColimitRawIntervalVertex B c))) := by
  have h := coherentColimitRawIntervalVertex_constant B c
  rw [SSet.yonedaEquiv_symm_zero] at h
  exact (V).long.trans (congrArg coherentTransformationFamilyDiagram h.symm)

end SerrePositivity.InfinityCategories.F2
