module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.LeftFiberKan
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.VertexFiber
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.VertexFiberMap
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.ContinuousKanSequence
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyWhiskering
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.RelativeModelKanComparison

/-!
概要：元の境界輸送の像を保持して、Kan 入力を元の fiber の射へ戻す。
方針：指定された模型輸送を Kan 反映と境界固定で合成する。
規約：境界射と全円柱を同時に保持。使われ方：二入力の相対有限検出の反映段。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

/-- 概要：元の境界の像を厳密な制限として持つ fiber 射と比較円柱を構成する。
方針：元の境界円柱の像を指定模型比較へ渡す。
規約：有限性不要。使われ方：二入力の比較を同一の境界輸送に揃える。 -/
lemma continuousKanReplacement_mapped_boundary_comparison {K M R E B : SSet.{u}}
    (p : R ⟶ B) (q : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q] (c : R ⟶ E) (hc : c ≫ q = p)
    (A : K.Subcomplex) (a : (A : SSet.{u}) ⟶ R) (b : B _⦋0⦌)
    (t : (A : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b) (L : SSet.Homotopy a (t ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b))
    (m : (A : SSet.{u}) ⟶ M) (f : M ⟶ E) (hf : m ≫ f = a ≫ c)
    (s : M ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber q b) (hs : m ≫ s = t ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap p q c hc b)
    (G : SSet.Homotopy f (s ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι q b))
    (hG : (m ▷ (Δ[1] : SSet.{u})) ≫ G.h = L.h ≫ c)
    (z : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj M)
    (hz : A.ι ≫ z = m ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app M)
    (u : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj E)
    (U : SSet.Homotopy u (z ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map f))
    (hU : (A.ι ▷ (Δ[1] : SSet.{u})) ≫ U.h =
      fst (A : SSet.{u}) (Δ[1] : SSet.{u}) ≫ a ≫ c ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app E) :
    ∃ v : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber q b, A.ι ≫ v = t ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap p q c hc b ∧
      ∃ T : SSet.Homotopy u (v ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι q b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app E),
        (A.ι ▷ (Δ[1] : SSet.{u})) ≫ T.h = L.h ≫ c ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app E := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_kanComplex_of_leftFibration q b
  let H : SSet.Homotopy (a ≫ c) ((t ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap p q c hc b) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι q b) :=
    { h := L.h ≫ c
      h₀ := by
        change SSet.ι₀ ≫ L.h ≫ c = a ≫ c
        rw [← Category.assoc, L.h₀]
      h₁ := by
        change SSet.ι₁ ≫ L.h ≫ c =
          (t ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap p q c hc b) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι q b
        rw [← Category.assoc, L.h₁]
        simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap_ι]
      rel := (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp L c).rel }
  have hU' : (A.ι ▷ (Δ[1] : SSet.{u})) ≫ U.h =
      fst (A : SSet.{u}) (Δ[1] : SSet.{u}) ≫ A.ι ≫ z ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map f := by
    rw [hU, ← Category.assoc A.ι, hz, Category.assoc,
      ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.naturality, Functor.id_map]
    simpa only [Category.assoc] using congrArg
      (fun v ↦ fst (A : SSet.{u}) (Δ[1] : SSet.{u}) ≫ v ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app E) hf.symm
  obtain ⟨v, hv, T, hT⟩ := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.continuousKanReplacement_relative_model_comparison A
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι q b) (a ≫ c) (t ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap p q c hc b) m f s hs H G hG z hz u U hU'
  exact ⟨v, hv, T, hT⟩

end SerrePositivity.InfinityCategories.Project.FilteredExchange
