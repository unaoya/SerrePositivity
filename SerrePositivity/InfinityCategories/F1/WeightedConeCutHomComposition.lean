module

public import SerrePositivity.InfinityCategories.F1.WeightedConeCutComposition
public import SerrePositivity.InfinityCategories.HomotopyLimits.WeightedConeSimplex
public import SerrePositivity.InfinityCategories.HomotopyLimits.ConeInitialParameter

/-!
概要：weighted cone の切断係数と、正頂点間の混合 Hom の合成則。
方針：元の weighted 係数の合成則と切断後の最小点の合成則を、豊穣合成の結合則で結ぶ。
規約：中間点が時刻零の合成を扱い、全体の prism の存在はまだ主張しない。
使われ方：weighted pointed prism を与える始点固定 cone の豊穣関手の合成則。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SimplicialThickening SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
open HomotopyLimits

variable {I : Type u} [SmallCategory I] {C : Type v} [Category.{u} C]
  [SimplicialCategory C]

/-- 時刻零から一への混合 Hom は、元の底の射に続く同じ切断後の変換の評価。 -/
def weightedConeCutTailHom (F : I ⥤ C) {n : ℕ} (σ : ComposableArrows I n)
    (t : Fin (n + 1) →o Fin 2) (i j : Fin (n + 1)) (hj : t j = 1) (z : C)
    (η : (Δ[n] : SSet.{u}) ⟶ (SimplicialCategory.sHom (F.obj (σ.obj j)) z).op) :
    nerve (Path (ULift.up i.succ : ULift.{u} (Fin (n + 2))) (ULift.up j.succ)) ⟶
      SimplicialCategory.sHom (F.obj (σ.obj i)) z :=
  lift (weightedConeTailHom (σ ⋙ F) i j)
    (pathCutMinimumMap t hj ≫ reflectedSimplexMap η) ≫
      eComp SSet (F.obj (σ.obj i)) (F.obj (σ.obj j)) z

/-- 中間点が時刻零のとき、初点からの切断係数は混合 Hom との豊穣合成を保つ。 -/
lemma weightedConeCutCoefficient_comp_zero (F : I ⥤ C) (x : C) {n : ℕ}
    {σ : ComposableArrows I n}
    (τ : simplexPrefixWeight n ⟶ σ ⋙ simplicialHomDiagram F x ⋙ SSet.opFunctor)
    (t : Fin (n + 1) →o Fin 2) (i j : Fin (n + 1)) (hi : t i = 0) (hj : t j = 1)
    (z : C) (η : (Δ[n] : SSet.{u}) ⟶ (SimplicialCategory.sHom (F.obj (σ.obj j)) z).op) :
    eComp SSet (⟨ULift.up 0⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2))))
      ⟨ULift.up i.succ⟩ ⟨ULift.up j.succ⟩ ≫
      weightedConeCutCoefficient x (F.obj (σ.obj j)) z t j hj (τ.app j) η =
    (weightedCoherentCoefficient τ i ⊗ₘ weightedConeCutTailHom F σ t i j hj z η) ≫
      eComp SSet x (F.obj (σ.obj i)) z := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  rintro ⟨P, Q⟩
  have hij : i ≤ j := Fin.succ_le_succ_iff.mp
    (show i.succ ≤ j.succ from Path.le (J := ULift.{u} (Fin (n + 2))) (Q.obj 0))
  have hc := congrArg (fun f => f.app d (P, Q))
    (congrArg (fun f => f ≫ reflectedSimplexMap η)
      (pathCutMinimumMap_comp_zero t 0 i j hi hj))
  change (reflectedSimplexMap η).app d
      ((pathCutMinimumMap t hj).app d
        ((eComp SSet (⟨ULift.up 0⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2))))
          ⟨ULift.up i.succ⟩ ⟨ULift.up j.succ⟩).app d (P, Q))) =
    (reflectedSimplexMap η).app d ((pathCutMinimumMap t hj).app d Q) at hc
  change (eComp SSet x (F.obj (σ.obj j)) z).app d
    ((weightedCoherentCoefficient τ j).app d
      ((eComp SSet (⟨ULift.up 0⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2))))
        ⟨ULift.up i.succ⟩ ⟨ULift.up j.succ⟩).app d (P, Q)),
      (reflectedSimplexMap η).app d ((pathCutMinimumMap t hj).app d
        ((eComp SSet (⟨ULift.up 0⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2))))
          ⟨ULift.up i.succ⟩ ⟨ULift.up j.succ⟩).app d (P, Q)))) =
    (eComp SSet x (F.obj (σ.obj i)) z).app d
      ((weightedCoherentCoefficient τ i).app d P,
        (eComp SSet (F.obj (σ.obj i)) (F.obj (σ.obj j)) z).app d
          ((weightedConeTailHom (σ ⋙ F) i j).app d Q,
            (reflectedSimplexMap η).app d ((pathCutMinimumMap t hj).app d Q)))
  rw [hc, weightedRepresentableCoefficient_comp F x τ i j hij d P Q]
  exact simplicialHom_assoc_elements x (F.obj (σ.obj i)) (F.obj (σ.obj j)) z d
    ((weightedCoherentCoefficient τ i).app d P)
    ((weightedConeTailHom (σ ⋙ F) i j).app d Q)
    ((reflectedSimplexMap η).app d ((pathCutMinimumMap t hj).app d Q))

end SerrePositivity.InfinityCategories
