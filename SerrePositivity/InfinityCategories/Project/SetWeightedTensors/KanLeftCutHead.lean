module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.ConeTailExtension
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.ConeHeadSimplex
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.KanDiagramLeftHomCutTail
public import SerrePositivity.InfinityCategories.Project.SetWeightedTensors.KanConeCutHomComposition

/-!
概要：実際の左区間の対角単体に、元の weighted 係数を始点固定の head として与える。
方針：時刻零では元の係数、時刻一では変換の切断評価を使い、対象の厳密な等式で戻す。
規約：head の射を明示し、逆同値の選択や自然性の追加仮定を使わない。
使われ方：weighted pointed prism の各単体を、cone の豊穣関手へ組み立てる。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory
  SimplicialThickening SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.SetWeightedTensors


/-- 元の weighted 係数から、左区間の共同評価の各正頂点への実際の head を作る。 -/
def weightedKanLeftCutHead {I : Type u} [SmallCategory I]
    (F G : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramObject I) (x : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) {n : ℕ} (σ : (nerve I) _⦋n⦌)
    (τ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixWeight n ⟶ σ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F.val x ⋙ SSet.opFunctor)
    (s : (SimplicialCategory.sHom F G).op _⦋n⦌)
    (t : (Δ[1] : SSet.{u + 1}) _⦋n⦌) (j : Fin (n + 1)) :
    nerve (Path (ULift.up 0 : ULift.{u} (Fin (n + 2))) (ULift.up j.succ)) ⟶
      SimplicialCategory.sHom x ((_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.kanDiagramLeftHomCutSimplex F G σ s t).obj ⟨ULift.up j⟩) :=
  if hj : (stdSimplex.objEquiv t).toOrderHom j = 0 then
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedCoherentCoefficient τ j ≫ eqToHom (congrArg (SimplicialCategory.sHom x)
      (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.kanDiagramLeftHomCutSimplex_obj_zero F G σ s t j hj).symm)
  else
    let hj' : (stdSimplex.objEquiv t).toOrderHom j = 1 := by
      apply Fin.ext
      have h : ((stdSimplex.objEquiv t).toOrderHom j).val < 2 :=
        ((stdSimplex.objEquiv t).toOrderHom j).isLt
      have hn : ((stdSimplex.objEquiv t).toOrderHom j).val ≠ 0 := fun h => hj (Fin.ext h)
      change ((stdSimplex.objEquiv t).toOrderHom j).val = 1
      omega
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.weightedConeCutCoefficient x (F.val.obj (σ.obj j)) (G.val.obj (σ.obj j))
      (stdSimplex.objEquiv t).toOrderHom j hj' (τ.app j)
      (SSet.yonedaEquiv.symm s ≫ SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingComponent
        (F.val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) (G.val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) (σ.obj j))) ≫
      eqToHom (congrArg (SimplicialCategory.sHom x)
        (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.kanDiagramLeftHomCutSimplex_obj_one F G σ s t j hj').symm)

/-- 時刻零の head は、標準対象へ戻すと元の weighted 係数そのもの。 -/
lemma weightedKanLeftCutHead_zero {I : Type u} [SmallCategory I]
    (F G : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramObject I) (x : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) {n : ℕ} (σ : (nerve I) _⦋n⦌)
    (τ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixWeight n ⟶ σ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F.val x ⋙ SSet.opFunctor)
    (s : (SimplicialCategory.sHom F G).op _⦋n⦌)
    (t : (Δ[1] : SSet.{u + 1}) _⦋n⦌) (j : Fin (n + 1))
    (hj : (stdSimplex.objEquiv t).toOrderHom j = 0) :
    weightedKanLeftCutHead F G x σ τ s t j ≫ eqToHom (congrArg (SimplicialCategory.sHom x)
      (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.kanDiagramLeftHomCutSimplex_obj_zero F G σ s t j hj)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedCoherentCoefficient τ j := by
  simp only [weightedKanLeftCutHead, dite_eq_left hj, Category.assoc, eqToHom_trans,
    eqToHom_refl, Category.comp_id]

/-- 時刻一の head は、標準対象へ戻すと同じ切断後の変換の係数そのもの。 -/
lemma weightedKanLeftCutHead_one {I : Type u} [SmallCategory I]
    (F G : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramObject I) (x : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) {n : ℕ} (σ : (nerve I) _⦋n⦌)
    (τ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixWeight n ⟶ σ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F.val x ⋙ SSet.opFunctor)
    (s : (SimplicialCategory.sHom F G).op _⦋n⦌)
    (t : (Δ[1] : SSet.{u + 1}) _⦋n⦌) (j : Fin (n + 1))
    (hj : (stdSimplex.objEquiv t).toOrderHom j = 1) :
    weightedKanLeftCutHead F G x σ τ s t j ≫ eqToHom (congrArg (SimplicialCategory.sHom x)
      (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.kanDiagramLeftHomCutSimplex_obj_one F G σ s t j hj)) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.weightedConeCutCoefficient x (F.val.obj (σ.obj j)) (G.val.obj (σ.obj j))
      (stdSimplex.objEquiv t).toOrderHom j hj (τ.app j)
      (SSet.yonedaEquiv.symm s ≫ SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingComponent
        (F.val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) (G.val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) (σ.obj j))) := by
  have hn : (stdSimplex.objEquiv t).toOrderHom j ≠ 0 := by rw [hj]; decide
  simp only [weightedKanLeftCutHead, dite_eq_right hn, Category.assoc, eqToHom_trans,
    eqToHom_refl, Category.comp_id]

/-- strict Kan 図式の tail Hom は、底の同じ射の閉構造の頂点を定値にしたもの。 -/
lemma weightedKanConeTailHom_eq_curry {I : Type u} [SmallCategory I]
    (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) {n : ℕ} (σ : (nerve I) _⦋n⦌)
    (i j : Fin (n + 1)) (hij : i ≤ j) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeTailHom (σ ⋙ F) i j = SemiCartesianMonoidalCategory.toUnit _ ≫
      curry' (show (F.obj (σ.obj i)).obj ⟶ (F.obj (σ.obj j)).obj from
        F.map (σ.map (homOfLE hij))) := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  intro P
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (SimplicialCategory.homEquiv' _ _
    (F.map (σ.map (homOfLE hij)))) d =
      (eHomEquiv SSet (F.map (σ.map (homOfLE hij)))).app (Opposite.op ⦋d⦌) PUnit.unit
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.unitHom_app_constant (eHomEquiv SSet (F.map (σ.map (homOfLE hij)))) d).symm

end SerrePositivity.InfinityCategories.Project.SetWeightedTensors
