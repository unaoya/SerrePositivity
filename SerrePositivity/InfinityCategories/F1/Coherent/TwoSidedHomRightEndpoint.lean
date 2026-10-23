module

public import SerrePositivity.InfinityCategories.F1.Coherent.PathCutRightEndpoint
public import SerrePositivity.InfinityCategories.F1.Coherent.TwoSidedHomIntervals
public import SerrePositivity.InfinityCategories.F1.Coherent.PrismEvaluation

/-!
概要：補間段階の右端を、元の coherent Hom の同じ右区間族に厳密に同定する。
方針：合成単体の前面と交差 Hom を照合し、既存の prism の評価式へ戻す。
規約：全 Hom の共通解像を維持し、端点の同値や頂点だけの一致で代用しない。
使われ方：左右を補間する族を元の反転 unstraightening の区間族へ接続する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory SimplicialThickening MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 右端の二対象の単体は、元の右 Hom の合成単体の前面そのもの。 -/
lemma coherentTwoSidedHomSimplex_one_front {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {X Y Z : C} {n : ℕ}
    (σ : (edgewiseSubdivision (SimplicialCategory.sHom X Y)) _⦋n⦌)
    (τ : (SimplicialCategory.sHom Y Z) _⦋n⦌) (t : Fin (n + 1) →o Fin 2) :
    coherentTwoSidedHomSimplex σ t (OrderHom.const _ 1) =
      (SimplicialNerve C).map (PinchedHom.front n).op
        (coherentCompositionSimplex ((edgewiseRight _).app _ σ) τ t) := by
  apply EnrichedFunctor.ext SSet
    (F := coherentTwoSidedHomSimplex σ t (OrderHom.const _ 1))
    (G := (SimplicialNerve C).map (PinchedHom.front n).op
      (coherentCompositionSimplex ((edgewiseRight _).app _ σ) τ t)) (fun a => by
        change coherentTwoSidedHomObj X Y t a.as.down =
          coherentCompositionObj X Y Z t a.as.down.castSucc
        simp only [coherentTwoSidedHomObj, coherentCompositionObj, Fin.lastCases_castSucc])
  rintro ⟨⟨i⟩⟩ ⟨⟨j⟩⟩
  change coherentTwoSidedHom σ t (OrderHom.const _ 1) i j ≫ eqToHom _ =
    thickeningDirectHom (PinchedHom.front n) i j ≫
      coherentCompositionHom ((edgewiseRight _).app _ σ) τ t i.castSucc j.castSucc
  by_cases hi : t i = 0 <;> by_cases hj : t j = 0
  · apply (cancel_mono (eqToHom (congrArg₂ SimplicialCategory.sHom
      (coherentCompositionObj_zero X Y Z t i hi)
      (coherentCompositionObj_zero X Y Z t j hj)))).1
    simp only [Category.assoc, eqToHom_trans]
    rw [coherentTwoSidedHom_zero_zero σ t (OrderHom.const _ 1) i j hi hj,
      coherentCompositionHom_zero_zero ((edgewiseRight _).app _ σ) τ t i j hi hj]
    apply SSet.hom_ext
    intro d
    rfl
  · apply (cancel_mono (eqToHom (congrArg₂ SimplicialCategory.sHom
      (coherentCompositionObj_zero X Y Z t i hi)
      (coherentCompositionObj_one X Y Z t j hj)))).1
    simp only [Category.assoc, eqToHom_trans]
    rw [coherentTwoSidedHom_zero_one σ t (OrderHom.const _ 1) i j hi hj,
      coherentCompositionHom_zero_one ((edgewiseRight _).app _ σ) τ t i j hi hj,
      pathCutEdgewiseStageMap_one, pathCutLastZeroMap_front, Category.assoc]
  · apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro P
    exact False.elim (pathCutSameSimplex_backward_false t hi hj (P.obj 0))
  · apply (cancel_mono (eqToHom (congrArg₂ SimplicialCategory.sHom
      (coherentCompositionObj_one X Y Z t i hi)
      (coherentCompositionObj_one X Y Z t j hj)))).1
    simp only [Category.assoc, eqToHom_trans]
    rw [coherentTwoSidedHom_one_one σ t (OrderHom.const _ 1) i j hi hj,
      coherentCompositionHom_one_one ((edgewiseRight _).app _ σ) τ t i j hi hj]
    apply SSet.hom_ext
    intro d
    rfl

/-- 右端の単体は、元の右 Hom 比較の同じ切断写像による制限。 -/
lemma coherentTwoSidedHomSimplex_one_cut {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {X Y : C} {n : ℕ}
    (σ : (edgewiseSubdivision (SimplicialCategory.sHom X Y)) _⦋n⦌)
    (t : Fin (n + 1) →o Fin 2) :
    coherentTwoSidedHomSimplex σ t (OrderHom.const _ 1) =
      (SimplicialNerve C).map (SimplexCategory.mkHom (coherentPrismCut t)).op
        (coherentHomComparisonSimplex ((edgewiseRight _).app _ σ)) := by
  let τ := PinchedHom.constant (SimplicialCategory.homEquiv' Y Y (𝟙 Y)) n
  exact (coherentTwoSidedHomSimplex_one_front σ τ t).trans
    (coherentCompositionSimplex_front ((edgewiseRight _).app _ σ) τ t)

/-- 補間段階の右端は、元の右 Hom 比較へ右射影を前合成した区間族そのもの。 -/
lemma coherentTwoSidedHomIntervalFamily_one {C : Type v} [Category.{u} C]
    [SimplicialCategory C] (X Y : C) :
    prismEndpoint 1 _ ≫ coherentTwoSidedHomIntervalFamily X Y =
      (SSet.uliftFunctor.{v, u}).map (edgewiseRight (SimplicialCategory.sHom X Y)) ≫
        coherentHomComparison X Y ≫
          pinchedHomToIntervalMappingSpace (coherentNerveVertex X) (coherentNerveVertex Y) := by
  apply intervalMappingUncurry_injective _ _
  rw [intervalMappingUncurry_precomp, coherentTwoSidedHomIntervalFamily_uncurry]
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨t, σ⟩
  calc
    _ = coherentTwoSidedHomSimplex σ.down (stdSimplex.objEquiv t).toOrderHom
        (OrderHom.const _ 1) := rfl
    _ = _ := (coherentTwoSidedHomSimplex_one_cut σ.down
      (stdSimplex.objEquiv t).toOrderHom).trans
        (pinchedHomToIntervalMappingSpace_evaluate
          ((SSet.uliftFunctor.{v, u}).map (edgewiseRight (SimplicialCategory.sHom X Y)) ≫
            coherentHomComparison X Y) σ t).symm

end SerrePositivity.InfinityCategories
