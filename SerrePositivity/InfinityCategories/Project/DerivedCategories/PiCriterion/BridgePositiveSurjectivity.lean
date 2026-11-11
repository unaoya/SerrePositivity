module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.PathVertexEdge
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.PiPathSphereComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.PathMapSurjectivity
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.PairValueRepresentatives

/-!
概要：D の全ての指定辺に対する全射性から、比較射の正次数全射性を導く。
方針：段階の輸送を始域で戻し、元の脚の移送を合成して同じ辺で D と比較する。
規約：D の positive_surjective の全称量化を、構成した同じ辺に適用する。
使われ方：有限検出と合わせた全空間比較の Whitehead 判定。
-/

@[expose] public section
noncomputable section
universe u w
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion
open KST.Spectra

private lemma transport_symm_piPathRelated {X : SSet.{w}} [KanComplex X]
    (n : ℕ) {x y : X _⦋0⦌} (e : X.Edge x y) (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup X n y) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.PiPathRelated n ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.bridgePiTransportEquiv n e).symm a) a := by
  apply (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.piPathRelated_iff_exists_transport n _ _).mpr
  exact ⟨e, (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.bridge_transport_iff_equiv n e _ _).mpr
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.bridgePiTransportEquiv n e).apply_symm_apply a)⟩

/-- D の全指定辺全射性により、各段階の像を基点とする比較射は全射。 -/
lemma bridge_positive_surjective_at_stage {I : Type u} [PartialOrder I]
    (X : I → _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{w}) (A T : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{w})
    (τ : ∀ {i j : I}, i ≤ j → ((X i).obj ⟶ (X j).obj))
    (l : ∀ i : I, (X i).obj ⟶ A.obj)
    (h : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.DGBarCompactSpacePiData X A τ l)
    (s : ∀ i : I, (X i).obj ⟶ T.obj) (q : T.obj ⟶ A.obj)
    (hcomm : ∀ i : I, Nonempty (Homotopy (l i) (s i ≫ q)))
    (hstage : ∀ (i j : I) (hij : i ≤ j), Nonempty (Homotopy (s i) (τ hij ≫ s j)))
    (n : ℕ) (i : I) (y : (X i).obj _⦋0⦌) :
    Function.Surjective (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (n := n) q (x := (s i).app _ y) rfl) := by
  intro a
  obtain ⟨Hi⟩ := hcomm i
  let ei := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge Hi y
  let E := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.bridgePiTransportEquiv n ei
  let ai := E.symm a
  obtain ⟨j, hij, b, hall⟩ := h.positive_surjective n i y ai
  obtain ⟨Hs⟩ := hstage i j hij
  let d := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge Hs y
  let bT := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (s j) rfl b
  let α := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.bridgePiTransportEquiv n d).symm bT
  let ai' := E.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map q rfl α)
  have hsrel : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.PiPathRelated n α bT := transport_symm_piPathRelated n d bT
  obtain ⟨Hj⟩ := hcomm j
  have hjrel : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.PiPathRelated n (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactPiMap n (l j) ((τ hij).app _ y) b)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map q rfl bT) := by
    have hr := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.piPathRelated_of_homotopy Hj n ((τ hij).app _ y) b
    have hm := DFunLike.congr_fun
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map_comp (s j) rfl q rfl rfl) b
    exact (congrArg (fun c ↦ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.PiPathRelated n
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactPiMap n (l j) ((τ hij).app _ y) b) c) hm).mp hr
  have hirel : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.PiPathRelated n ai' (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map q rfl α) :=
    transport_symm_piPathRelated n ei (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map q rfl α)
  have hr := (hjrel.trans (hsrel.map q).symm).trans hirel.symm
  obtain ⟨e, he⟩ := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.piPathRelated_iff_exists_transport n _ _).mp hr
  have hai : ai' = ai := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.bridge_transport_right_unique n e he (hall e)
  have heq := congrArg E hai
  change E (E.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map q rfl α)) = E (E.symm a) at heq
  rw [E.apply_symm_apply, E.apply_symm_apply] at heq
  exact ⟨α, heq⟩

/-- 有限検出で始域の全基点を段階の像へ結べるなら、D の条件から正次数で全射。 -/
lemma bridge_positive_surjective {I : Type u} [PartialOrder I]
    (X : I → _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{w}) (A T : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{w})
    (τ : ∀ {i j : I}, i ≤ j → ((X i).obj ⟶ (X j).obj))
    (l : ∀ i : I, (X i).obj ⟶ A.obj)
    (h : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.DGBarCompactSpacePiData X A τ l)
    (s : ∀ i : I, (X i).obj ⟶ T.obj) (q : T.obj ⟶ A.obj)
    (hcomm : ∀ i : I, Nonempty (Homotopy (l i) (s i ≫ q)))
    (hstage : ∀ (i j : I) (hij : i ≤ j), Nonempty (Homotopy (s i) (τ hij ≫ s j)))
    (hfinite : ∀ {K : SSet.{w}} [K.Finite] (f : K ⟶ T.obj),
      ∃ i : I, ∃ g : K ⟶ (X i).obj, Nonempty (Homotopy f (g ≫ s i)))
    (n : ℕ) (x : T.obj _⦋0⦌) :
    Function.Surjective (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (n := n) q (x := x) rfl) := by
  obtain ⟨i, y, _, z, h₀, h₁, _, _⟩ :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.finite_positive_pair_representative X T.obj s hfinite n x ![1, 1]
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.path_map_surjective_iff q n z h₀ h₁).mpr
    (bridge_positive_surjective_at_stage X A T τ l h s q hcomm hstage n i y)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion
