module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConeCutHomComposition
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.StrictDiagramOppositeHom
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanPointHomNaturality

/-!
概要：strict Kan 図式の変換に対する、時刻一側の cone 係数の合成則。
方針：変換の実際の全次数の自然性と切断の最小点の前半の式を豊穣合成へ移す。
規約：比較の自然性は追加仮定にせず、元の strict 変換の条件から証明する。
使われ方：weighted pointed prism の初点から時刻一の正頂点への Hom の合成則。
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


private lemma strictKanDiagramMappingSimplex_square {I : Type u} [SmallCategory I]
    (F G : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) {d : SimplexCategoryᵒᵖ}
    (θ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingSimplex (F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) (G ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) d)
    {i j : I} (f : i ⟶ j) :
    (eComp SSet (F.obj i) (F.obj j) (G.obj j)).app d
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (SimplicialCategory.homEquiv' _ _ (F.map f)) d.unop.len, θ.val j) =
    (eComp SSet (F.obj i) (G.obj i) (G.obj j)).app d
      (θ.val i, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (SimplicialCategory.homEquiv' _ _ (G.map f)) d.unop.len) := by
  rcases d with ⟨⟨d⟩⟩
  have hF : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (SimplicialCategory.homEquiv' _ _ (F.map f)) d =
      (eHomEquiv SSet (F.map f)).app (Opposite.op ⦋d⦌) PUnit.unit :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.unitHom_app_constant (eHomEquiv SSet (F.map f)) d).symm
  have hG : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (SimplicialCategory.homEquiv' _ _ (G.map f)) d =
      (eHomEquiv SSet (G.map f)).app (Opposite.op ⦋d⦌) PUnit.unit :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.unitHom_app_constant (eHomEquiv SSet (G.map f)) d).symm
  rw [hF, hG]
  have hpre : (eComp SSet (F.obj i) (F.obj j) (G.obj j)).app (Opposite.op ⦋d⦌)
      ((eHomEquiv SSet (F.map f)).app (Opposite.op ⦋d⦌) PUnit.unit, θ.val j) =
      ((pre (show (F.obj i).obj ⟶ (F.obj j).obj from F.map f)).app (G.obj j).obj).app
        (Opposite.op ⦋d⦌) (θ.val j) := by
    exact congrArg (fun h => h.app (Opposite.op ⦋d⦌) (PUnit.unit, θ.val j))
      (curry'_whiskerRight_comp (C := SSet.{u})
        (Z := (G.obj j).obj) (show (F.obj i).obj ⟶ (F.obj j).obj from F.map f))
  have hpost : (eComp SSet (F.obj i) (G.obj i) (G.obj j)).app (Opposite.op ⦋d⦌)
      (θ.val i, (eHomEquiv SSet (G.map f)).app (Opposite.op ⦋d⦌) PUnit.unit) =
      ((ihom (F.obj i).obj).map (show (G.obj i).obj ⟶ (G.obj j).obj from G.map f)).app
        (Opposite.op ⦋d⦌) (θ.val i) := by
    exact congrArg (fun h => h.app (Opposite.op ⦋d⦌) (θ.val i, PUnit.unit))
      (whiskerLeft_curry'_comp (C := SSet.{u})
        (X := (F.obj i).obj) (show (G.obj i).obj ⟶ (G.obj j).obj from G.map f))
  rw [hpre, hpost]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.strictDiagramMappingSimplex_post_pre θ f).symm

/-- 中間点が時刻一なら、同じ strict 変換の自然性から cone の係数の合成則が従う。 -/
lemma weightedKanConeCutCoefficient_comp_one {I : Type u} [SmallCategory I]
    (F G : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) (x : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) {n : ℕ}
    {σ : ComposableArrows I n}
    (τ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixWeight n ⟶ σ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F x ⋙ SSet.opFunctor)
    (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingSpace (F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) (G ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget)).op _⦋n⦌)
    (t : Fin (n + 1) →o Fin 2) (i j : Fin (n + 1)) (hi : t i = 1) (hj : t j = 1) :
    eComp SSet (⟨ULift.up 0⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2))))
      ⟨ULift.up i.succ⟩ ⟨ULift.up j.succ⟩ ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.weightedConeCutCoefficient x (F.obj (σ.obj j)) (G.obj (σ.obj j)) t j hj (τ.app j)
        (SSet.yonedaEquiv.symm s ≫ SSet.opFunctor.map
          (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingComponent (F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) (G ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) (σ.obj j))) =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.weightedConeCutCoefficient x (F.obj (σ.obj i)) (G.obj (σ.obj i)) t i hi (τ.app i)
        (SSet.yonedaEquiv.symm s ≫ SSet.opFunctor.map
          (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingComponent (F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) (G ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) (σ.obj i))) ⊗ₘ
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeTailHom (σ ⋙ G) i j) ≫ eComp SSet x (G.obj (σ.obj i)) (G.obj (σ.obj j)) := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  rintro ⟨P, Q⟩
  have hij : i ≤ j := Fin.succ_le_succ_iff.mp
    (show i.succ ≤ j.succ from Path.le (J := ULift.{u} (Fin (n + 2))) (Q.obj 0))
  let r := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedSimplexMap (SSet.yonedaEquiv.symm s)
  let θ := r.app d ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMinimumMap t hi).app d P)
  have hc := congrArg (fun f => f.app d (P, Q))
    (congrArg (fun f => f ≫ r) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMinimumMap_comp_one t 0 i j hi hj))
  change r.app d ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMinimumMap t hj).app d
      ((eComp SSet (⟨ULift.up 0⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2))))
        ⟨ULift.up i.succ⟩ ⟨ULift.up j.succ⟩).app d (P, Q))) = θ at hc
  change (eComp SSet x (F.obj (σ.obj j)) (G.obj (σ.obj j))).app d
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedCoherentCoefficient τ j).app d
      ((eComp SSet (⟨ULift.up 0⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2))))
        ⟨ULift.up i.succ⟩ ⟨ULift.up j.succ⟩).app d (P, Q)),
      (r.app d ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMinimumMap t hj).app d
        ((eComp SSet (⟨ULift.up 0⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2))))
          ⟨ULift.up i.succ⟩ ⟨ULift.up j.succ⟩).app d (P, Q)))).val (σ.obj j)) =
    (eComp SSet x (G.obj (σ.obj i)) (G.obj (σ.obj j))).app d
      ((eComp SSet x (F.obj (σ.obj i)) (G.obj (σ.obj i))).app d
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedCoherentCoefficient τ i).app d P, θ.val (σ.obj i)),
          (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeTailHom (σ ⋙ G) i j).app d Q)
  rw [hc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedRepresentableCoefficient_comp F x τ i j hij d P Q,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.simplicialHom_assoc_elements]
  have hs := strictKanDiagramMappingSimplex_square F G θ (σ.map (homOfLE hij))
  rw [hs]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.simplicialHom_assoc_elements x (F.obj (σ.obj i)) (G.obj (σ.obj i))
    (G.obj (σ.obj j)) d ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedCoherentCoefficient τ i).app d P)
      (θ.val (σ.obj i)) ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeTailHom (σ ⋙ G) i j).app d Q)).symm

end SerrePositivity.InfinityCategories.Project.SetWeightedTensors
