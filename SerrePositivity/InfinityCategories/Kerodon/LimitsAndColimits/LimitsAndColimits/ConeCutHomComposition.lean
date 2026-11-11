module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConeCutComposition
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.WeightedConeSimplex
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConeInitialParameter

/-!
概要：weighted cone の切断係数と、正頂点間の混合 Hom の合成則。
方針：元の weighted 係数の合成則と切断後の最小点の合成則を、豊穣合成の結合則で結ぶ。
規約：中間点が時刻零の合成を扱い、全体の prism の存在はまだ主張しない。
使われ方：weighted pointed prism を与える始点固定 cone の豊穣関手の合成則。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SimplicialThickening SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits


variable {I : Type u} [SmallCategory I] {C : Type v} [Category.{u} C]
  [SimplicialCategory C]

/-- 時刻零から一への混合 Hom は、元の底の射に続く同じ切断後の変換の評価。 -/
def weightedConeCutTailHom (F : I ⥤ C) {n : ℕ} (σ : ComposableArrows I n)
    (t : Fin (n + 1) →o Fin 2) (i j : Fin (n + 1)) (hj : t j = 1) (z : C)
    (η : (Δ[n] : SSet.{u}) ⟶ (SimplicialCategory.sHom (F.obj (σ.obj j)) z).op) :
    nerve (Path (ULift.up i.succ : ULift.{u} (Fin (n + 2))) (ULift.up j.succ)) ⟶
      SimplicialCategory.sHom (F.obj (σ.obj i)) z :=
  lift (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeTailHom (σ ⋙ F) i j)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMinimumMap t hj ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedSimplexMap η) ≫
      eComp SSet (F.obj (σ.obj i)) (F.obj (σ.obj j)) z

/-- 中間点が時刻零のとき、初点からの切断係数は混合 Hom との豊穣合成を保つ。 -/
lemma weightedConeCutCoefficient_comp_zero (F : I ⥤ C) (x : C) {n : ℕ}
    {σ : ComposableArrows I n}
    (τ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixWeight n ⟶ σ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F x ⋙ SSet.opFunctor)
    (t : Fin (n + 1) →o Fin 2) (i j : Fin (n + 1)) (hi : t i = 0) (hj : t j = 1)
    (z : C) (η : (Δ[n] : SSet.{u}) ⟶ (SimplicialCategory.sHom (F.obj (σ.obj j)) z).op) :
    eComp SSet (⟨ULift.up 0⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2))))
      ⟨ULift.up i.succ⟩ ⟨ULift.up j.succ⟩ ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.weightedConeCutCoefficient x (F.obj (σ.obj j)) z t j hj (τ.app j) η =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedCoherentCoefficient τ i ⊗ₘ weightedConeCutTailHom F σ t i j hj z η) ≫
      eComp SSet x (F.obj (σ.obj i)) z := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  rintro ⟨P, Q⟩
  have hij : i ≤ j := Fin.succ_le_succ_iff.mp
    (show i.succ ≤ j.succ from Path.le (J := ULift.{u} (Fin (n + 2))) (Q.obj 0))
  have hc := congrArg (fun f => f.app d (P, Q))
    (congrArg (fun f => f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedSimplexMap η)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMinimumMap_comp_zero t 0 i j hi hj))
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedSimplexMap η).app d
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMinimumMap t hj).app d
        ((eComp SSet (⟨ULift.up 0⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2))))
          ⟨ULift.up i.succ⟩ ⟨ULift.up j.succ⟩).app d (P, Q))) =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedSimplexMap η).app d ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMinimumMap t hj).app d Q) at hc
  change (eComp SSet x (F.obj (σ.obj j)) z).app d
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedCoherentCoefficient τ j).app d
      ((eComp SSet (⟨ULift.up 0⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2))))
        ⟨ULift.up i.succ⟩ ⟨ULift.up j.succ⟩).app d (P, Q)),
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedSimplexMap η).app d ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMinimumMap t hj).app d
        ((eComp SSet (⟨ULift.up 0⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2))))
          ⟨ULift.up i.succ⟩ ⟨ULift.up j.succ⟩).app d (P, Q)))) =
    (eComp SSet x (F.obj (σ.obj i)) z).app d
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedCoherentCoefficient τ i).app d P,
        (eComp SSet (F.obj (σ.obj i)) (F.obj (σ.obj j)) z).app d
          ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeTailHom (σ ⋙ F) i j).app d Q,
            (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedSimplexMap η).app d ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMinimumMap t hj).app d Q)))
  rw [hc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedRepresentableCoefficient_comp F x τ i j hij d P Q]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.simplicialHom_assoc_elements x (F.obj (σ.obj i)) (F.obj (σ.obj j)) z d
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedCoherentCoefficient τ i).app d P)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeTailHom (σ ⋙ F) i j).app d Q)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedSimplexMap η).app d ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMinimumMap t hj).app d Q))

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
