module

public import SerrePositivity.InfinityCategories.Project.SetWeightedTensors.KanLeftCutHead

/-!
概要：cone の tail の全 Hom を、既に合成則を証明した元の weighted Hom に厳密に同定する。
方針：正頂点の path の逆移送と、実際の対角単体の三つの時間分岐の式を合成する。
規約：tail は元の単体の豊穣関手を前合成したもので、射の選択を追加しない。
使われ方：具体的な weighted head を CoherentConeHead に束ねる際の合成則。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory MonoidalClosed SimplicialThickening SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.SetWeightedTensors


private lemma tailMap_normalized {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {n : ℕ} (A : (SimplicialNerve C) _⦋n⦌) (i j : Fin (n + 1)) {X Y : C}
    (hi : A.obj ⟨ULift.up i⟩ = X) (hj : A.obj ⟨ULift.up j⟩ = Y) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentConeTailExtension A).map ⟨ULift.up i.succ⟩ ⟨ULift.up j.succ⟩ ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom hi hj) =
    (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.pathPositiveShiftIso i j).inv ≫
      (A.map ⟨ULift.up i⟩ ⟨ULift.up j⟩ ≫ eqToHom (congrArg₂ SimplicialCategory.sHom hi hj)) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentConeTailExtension_map, Category.assoc]

/-- 時刻零同士の tail は、元の始域図式の weighted tail Hom を厳密に回収する。 -/
lemma weightedKanLeftCutTail_zero {I : Type u} [SmallCategory I]
    (F G : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramObject I) {n : ℕ} (σ : (nerve I) _⦋n⦌)
    (s : (SimplicialCategory.sHom F G).op _⦋n⦌)
    (t : (Δ[1] : SSet.{u + 1}) _⦋n⦌) (i j : Fin (n + 1)) (hij : i ≤ j)
    (hi : (stdSimplex.objEquiv t).toOrderHom i = 0)
    (hj : (stdSimplex.objEquiv t).toOrderHom j = 0) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentConeTailExtension (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.kanDiagramLeftHomCutSimplex F G σ s t)).map
      ⟨ULift.up i.succ⟩ ⟨ULift.up j.succ⟩ ≫ eqToHom (congrArg₂ SimplicialCategory.sHom
        (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.kanDiagramLeftHomCutSimplex_obj_zero F G σ s t i hi)
        (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.kanDiagramLeftHomCutSimplex_obj_zero F G σ s t j hj)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeTailHom (σ ⋙ F.val) i j := by
  rw [tailMap_normalized (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.kanDiagramLeftHomCutSimplex F G σ s t) i j
    (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.kanDiagramLeftHomCutSimplex_obj_zero F G σ s t i hi)
    (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.kanDiagramLeftHomCutSimplex_obj_zero F G σ s t j hj)]
  have h := congrArg (fun f => (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.pathPositiveShiftIso i j).inv ≫ f)
    (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.kanDiagramLeftHomCutSimplex_hom_zero F G σ s t i j hij hi hj)
  calc
    _ = (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.pathPositiveShiftIso i j).inv ≫ (SemiCartesianMonoidalCategory.toUnit _ ≫
        curry' (show (F.val.obj (σ.obj i)).obj ⟶ (F.val.obj (σ.obj j)).obj from
          F.val.map (σ.map (homOfLE hij)))) := h
    _ = _ := by
      rw [← Category.assoc, SemiCartesianMonoidalCategory.comp_toUnit]
      exact (_root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.weightedKanConeTailHom_eq_curry F.val σ i j hij).symm

/-- 時刻一同士の tail は、元の終域図式の weighted tail Hom を厳密に回収する。 -/
lemma weightedKanLeftCutTail_one {I : Type u} [SmallCategory I]
    (F G : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramObject I) {n : ℕ} (σ : (nerve I) _⦋n⦌)
    (s : (SimplicialCategory.sHom F G).op _⦋n⦌)
    (t : (Δ[1] : SSet.{u + 1}) _⦋n⦌) (i j : Fin (n + 1)) (hij : i ≤ j)
    (hi : (stdSimplex.objEquiv t).toOrderHom i = 1)
    (hj : (stdSimplex.objEquiv t).toOrderHom j = 1) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentConeTailExtension (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.kanDiagramLeftHomCutSimplex F G σ s t)).map
      ⟨ULift.up i.succ⟩ ⟨ULift.up j.succ⟩ ≫ eqToHom (congrArg₂ SimplicialCategory.sHom
        (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.kanDiagramLeftHomCutSimplex_obj_one F G σ s t i hi)
        (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.kanDiagramLeftHomCutSimplex_obj_one F G σ s t j hj)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeTailHom (σ ⋙ G.val) i j := by
  rw [tailMap_normalized (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.kanDiagramLeftHomCutSimplex F G σ s t) i j
    (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.kanDiagramLeftHomCutSimplex_obj_one F G σ s t i hi)
    (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.kanDiagramLeftHomCutSimplex_obj_one F G σ s t j hj)]
  have h := congrArg (fun f => (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.pathPositiveShiftIso i j).inv ≫ f)
    (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.kanDiagramLeftHomCutSimplex_hom_one F G σ s t i j hij hi hj)
  calc
    _ = (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.pathPositiveShiftIso i j).inv ≫ (SemiCartesianMonoidalCategory.toUnit _ ≫
        curry' (show (G.val.obj (σ.obj i)).obj ⟶ (G.val.obj (σ.obj j)).obj from
          G.val.map (σ.map (homOfLE hij)))) := h
    _ = _ := by
      rw [← Category.assoc, SemiCartesianMonoidalCategory.comp_toUnit]
      exact (_root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.weightedKanConeTailHom_eq_curry G.val σ i j hij).symm

/-- 混合する tail は、初点からの係数と同じ weighted な切断 Hom を厳密に回収する。 -/
lemma weightedKanLeftCutTail_mixed {I : Type u} [SmallCategory I]
    (F G : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramObject I) {n : ℕ} (σ : (nerve I) _⦋n⦌)
    (s : (SimplicialCategory.sHom F G).op _⦋n⦌)
    (t : (Δ[1] : SSet.{u + 1}) _⦋n⦌) (i j : Fin (n + 1)) (hij : i ≤ j)
    (hi : (stdSimplex.objEquiv t).toOrderHom i = 0)
    (hj : (stdSimplex.objEquiv t).toOrderHom j = 1) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentConeTailExtension (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.kanDiagramLeftHomCutSimplex F G σ s t)).map
      ⟨ULift.up i.succ⟩ ⟨ULift.up j.succ⟩ ≫ eqToHom (congrArg₂ SimplicialCategory.sHom
        (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.kanDiagramLeftHomCutSimplex_obj_zero F G σ s t i hi)
        (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.kanDiagramLeftHomCutSimplex_obj_one F G σ s t j hj)) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.weightedConeCutTailHom F.val σ (stdSimplex.objEquiv t).toOrderHom i j hj
      (G.val.obj (σ.obj j)) (SSet.yonedaEquiv.symm s ≫ SSet.opFunctor.map
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingComponent (F.val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget)
          (G.val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) (σ.obj j))) := by
  rw [tailMap_normalized (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.kanDiagramLeftHomCutSimplex F G σ s t) i j
    (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.kanDiagramLeftHomCutSimplex_obj_zero F G σ s t i hi)
    (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.kanDiagramLeftHomCutSimplex_obj_one F G σ s t j hj)]
  have h := congrArg (fun f => (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.pathPositiveShiftIso i j).inv ≫ f)
    (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.kanDiagramLeftHomCutSimplex_mixedHom_eq_tail F G σ s t i j hij hi hj)
  calc
    _ = (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.pathPositiveShiftIso i j).inv ≫ (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.pathPositiveShiftFunctor i j) ≫ _) := h
    _ = _ := by
      change (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.pathPositiveShiftIso i j).inv ≫ ((_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.pathPositiveShiftIso i j).hom ≫ _) = _
      rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

end SerrePositivity.InfinityCategories.Project.SetWeightedTensors
