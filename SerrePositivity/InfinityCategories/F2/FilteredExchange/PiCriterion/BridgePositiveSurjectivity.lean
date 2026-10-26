module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.PiCriterion.PathVertexEdge
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.PiCriterion.PiPathSphereComparison
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.PiCriterion.PathMapSurjectivity
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.PiCriterion.PairValueRepresentatives

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
namespace SerrePositivity.InfinityCategories.F2.PiCriterion
open KST.Spectra

private lemma transport_symm_piPathRelated {X : SSet.{w}} [KanComplex X]
    (n : ℕ) {x y : X _⦋0⦌} (e : X.Edge x y) (a : KanHomotopyGroup X n y) :
    PiPathRelated n ((bridgePiTransportEquiv n e).symm a) a := by
  apply (piPathRelated_iff_exists_transport n _ _).mpr
  exact ⟨e, (bridge_transport_iff_equiv n e _ _).mpr
    ((bridgePiTransportEquiv n e).apply_symm_apply a)⟩

/-- D の全指定辺全射性により、各段階の像を基点とする比較射は全射。 -/
lemma bridge_positive_surjective_at_stage {I : Type u} [PartialOrder I]
    (X : I → KanObject.{w}) (A T : KanObject.{w})
    (τ : ∀ {i j : I}, i ≤ j → ((X i).obj ⟶ (X j).obj))
    (l : ∀ i : I, (X i).obj ⟶ A.obj)
    (h : DGBarCompactSpacePiData X A τ l)
    (s : ∀ i : I, (X i).obj ⟶ T.obj) (q : T.obj ⟶ A.obj)
    (hcomm : ∀ i : I, Nonempty (Homotopy (l i) (s i ≫ q)))
    (hstage : ∀ (i j : I) (hij : i ≤ j), Nonempty (Homotopy (s i) (τ hij ≫ s j)))
    (n : ℕ) (i : I) (y : (X i).obj _⦋0⦌) :
    Function.Surjective (KanHomotopyGroup.map (n := n) q (x := (s i).app _ y) rfl) := by
  intro a
  obtain ⟨Hi⟩ := hcomm i
  let ei := simplicialHomotopyVertexEdge Hi y
  let E := bridgePiTransportEquiv n ei
  let ai := E.symm a
  obtain ⟨j, hij, b, hall⟩ := h.positive_surjective n i y ai
  obtain ⟨Hs⟩ := hstage i j hij
  let d := simplicialHomotopyVertexEdge Hs y
  let bT := KanHomotopyGroup.map (s j) rfl b
  let α := (bridgePiTransportEquiv n d).symm bT
  let ai' := E.symm (KanHomotopyGroup.map q rfl α)
  have hsrel : PiPathRelated n α bT := transport_symm_piPathRelated n d bT
  obtain ⟨Hj⟩ := hcomm j
  have hjrel : PiPathRelated n (dgBarCompactPiMap n (l j) ((τ hij).app _ y) b)
      (KanHomotopyGroup.map q rfl bT) := by
    have hr := piPathRelated_of_homotopy Hj n ((τ hij).app _ y) b
    have hm := DFunLike.congr_fun
      (KanHomotopyGroup.map_comp (s j) rfl q rfl rfl) b
    exact (congrArg (fun c ↦ PiPathRelated n
      (dgBarCompactPiMap n (l j) ((τ hij).app _ y) b) c) hm).mp hr
  have hirel : PiPathRelated n ai' (KanHomotopyGroup.map q rfl α) :=
    transport_symm_piPathRelated n ei (KanHomotopyGroup.map q rfl α)
  have hr := (hjrel.trans (hsrel.map q).symm).trans hirel.symm
  obtain ⟨e, he⟩ := (piPathRelated_iff_exists_transport n _ _).mp hr
  have hai : ai' = ai := bridge_transport_right_unique n e he (hall e)
  have heq := congrArg E hai
  change E (E.symm (KanHomotopyGroup.map q rfl α)) = E (E.symm a) at heq
  rw [E.apply_symm_apply, E.apply_symm_apply] at heq
  exact ⟨α, heq⟩

/-- 有限検出で始域の全基点を段階の像へ結べるなら、D の条件から正次数で全射。 -/
lemma bridge_positive_surjective {I : Type u} [PartialOrder I]
    (X : I → KanObject.{w}) (A T : KanObject.{w})
    (τ : ∀ {i j : I}, i ≤ j → ((X i).obj ⟶ (X j).obj))
    (l : ∀ i : I, (X i).obj ⟶ A.obj)
    (h : DGBarCompactSpacePiData X A τ l)
    (s : ∀ i : I, (X i).obj ⟶ T.obj) (q : T.obj ⟶ A.obj)
    (hcomm : ∀ i : I, Nonempty (Homotopy (l i) (s i ≫ q)))
    (hstage : ∀ (i j : I) (hij : i ≤ j), Nonempty (Homotopy (s i) (τ hij ≫ s j)))
    (hfinite : ∀ {K : SSet.{w}} [K.Finite] (f : K ⟶ T.obj),
      ∃ i : I, ∃ g : K ⟶ (X i).obj, Nonempty (Homotopy f (g ≫ s i)))
    (n : ℕ) (x : T.obj _⦋0⦌) :
    Function.Surjective (KanHomotopyGroup.map (n := n) q (x := x) rfl) := by
  obtain ⟨i, y, _, z, h₀, h₁, _, _⟩ :=
    finite_positive_pair_representative X T.obj s hfinite n x ![1, 1]
  exact (path_map_surjective_iff q n z h₀ h₁).mpr
    (bridge_positive_surjective_at_stage X A T τ l h s q hcomm hstage n i y)

end SerrePositivity.InfinityCategories.F2.PiCriterion
