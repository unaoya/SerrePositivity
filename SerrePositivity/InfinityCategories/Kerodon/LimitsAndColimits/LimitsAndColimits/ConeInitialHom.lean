module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConeInitialParameter
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.WeightedConeSimplex

/-!
概要：任意の coherent simplex の最初の対象を、反転した Hom の全パラメータで取り替える。
方針：正頂点間の Hom は元の simplex を保ち、初点からの Hom を豊穣合成で定める。
規約：tail が通常の圏の strict 図式から来ることを要求しない。
使われ方：HTT 4.2.4.1 の構成済みの錐の図式全体上の族の Hom データ。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SimplicialThickening MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
noncomputable section
variable {C : Type v} [Category.{u} C] [SimplicialCategory C]

/-- 最初の対象を x に置き換え、残りの対象は元の coherent simplex から取る。 -/
def coneInitialObj (x : C) {n : ℕ} (T : (SimplicialNerve C) _⦋n + 1⦌)
    (i : Fin (n + 2)) : C :=
  Fin.cases x (fun j ↦ T.obj ⟨ULift.up j.succ⟩) i

/-- 初点から正頂点への Hom はパラメータと元の Hom の豊穣合成。 -/
def coneInitialHead (x : C) {n : ℕ} (T : (SimplicialNerve C) _⦋n + 1⦌)
    (p : Δ[n] ⟶ (SimplicialCategory.sHom x (T.obj ⟨ULift.up 0⟩)).op)
    (j : Fin (n + 1)) :
    nerve (Path (ULift.up 0 : ULift.{u} (Fin (n + 2))) (ULift.up j.succ)) ⟶
      SimplicialCategory.sHom x (T.obj ⟨ULift.up j.succ⟩) :=
  lift (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.pathFirstParameterMap j ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedSimplexMap p)
    (T.map ⟨ULift.up 0⟩ ⟨ULift.up j.succ⟩) ≫
      eComp SSet x (T.obj ⟨ULift.up 0⟩) (T.obj ⟨ULift.up j.succ⟩)

/-- 新しい初点からの Hom の合成則は、座標の合成則と元の simplex の合成則から従う。 -/
lemma coneInitialHead_comp (x : C) {n : ℕ} (T : (SimplicialNerve C) _⦋n + 1⦌)
    (p : Δ[n] ⟶ (SimplicialCategory.sHom x (T.obj ⟨ULift.up 0⟩)).op)
    (i j : Fin (n + 1)) :
    eComp SSet
        (⟨ULift.up 0⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2))))
        ⟨ULift.up i.succ⟩ ⟨ULift.up j.succ⟩ ≫ coneInitialHead x T p j =
      (coneInitialHead x T p i ⊗ₘ T.map ⟨ULift.up i.succ⟩ ⟨ULift.up j.succ⟩) ≫
        eComp SSet x (T.obj ⟨ULift.up i.succ⟩) (T.obj ⟨ULift.up j.succ⟩) := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  rintro ⟨P, Q⟩
  have hij : i ≤ j := Fin.succ_le_succ_iff.mp
    (show i.succ ≤ j.succ from Path.le
      (J := ULift.{u} (Fin (n + 2))) (Q.obj 0))
  let L := SimplicialThickening (ULift.{u} (Fin (n + 2)))
  have hp := congrArg
    (fun f : SimplicialCategory.sHom (⟨ULift.up 0⟩ : L) ⟨ULift.up i.succ⟩ ⊗
        SimplicialCategory.sHom (⟨ULift.up i.succ⟩ : L) ⟨ULift.up j.succ⟩ ⟶
          (Δ[n] : SSet.{u}).op ↦ f.app d (P, Q))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.pathFirstParameterMap_comp i j hij)
  have ht := congrArg
    (fun f : SimplicialCategory.sHom (⟨ULift.up 0⟩ : L) ⟨ULift.up i.succ⟩ ⊗
        SimplicialCategory.sHom (⟨ULift.up i.succ⟩ : L) ⟨ULift.up j.succ⟩ ⟶
          SimplicialCategory.sHom (T.obj ⟨ULift.up 0⟩) (T.obj ⟨ULift.up j.succ⟩) ↦
            f.app d (P, Q))
    (T.map_comp ⟨ULift.up 0⟩ ⟨ULift.up i.succ⟩ ⟨ULift.up j.succ⟩)
  change (eComp SSet x (T.obj ⟨ULift.up 0⟩) (T.obj ⟨ULift.up j.succ⟩)).app d
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedSimplexMap p).app d
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.pathFirstParameterMap j).app d
          ((eComp SSet
            (⟨ULift.up 0⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2))))
            ⟨ULift.up i.succ⟩ ⟨ULift.up j.succ⟩).app d (P, Q))),
        (T.map ⟨ULift.up 0⟩ ⟨ULift.up j.succ⟩).app d
          ((eComp SSet
            (⟨ULift.up 0⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2))))
            ⟨ULift.up i.succ⟩ ⟨ULift.up j.succ⟩).app d (P, Q))) = _
  erw [hp, ht]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.simplicialHom_assoc_elements x (T.obj ⟨ULift.up 0⟩)
    (T.obj ⟨ULift.up i.succ⟩) (T.obj ⟨ULift.up j.succ⟩) d _ _ _).symm

/-- 初点の自己 Hom・新しい head・空の逆向き Hom・元の tail からなる Hom データ。 -/
def coneInitialHom (x : C) {n : ℕ} (T : (SimplicialNerve C) _⦋n + 1⦌)
    (p : Δ[n] ⟶ (SimplicialCategory.sHom x (T.obj ⟨ULift.up 0⟩)).op)
    (i j : Fin (n + 2)) :
    SimplicialCategory.sHom
      (⟨ULift.up i⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2)))) ⟨ULift.up j⟩ ⟶
        SimplicialCategory.sHom (coneInitialObj x T i) (coneInitialObj x T j) := by
  induction i using Fin.cases with
  | zero =>
    induction j using Fin.cases with
    | zero => exact toUnit _ ≫ eId SSet x
    | succ j => exact coneInitialHead x T p j
  | succ i =>
    induction j using Fin.cases with
    | zero => exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeEmptyMap i _
    | succ j => exact T.map ⟨ULift.up i.succ⟩ ⟨ULift.up j.succ⟩

end
end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
