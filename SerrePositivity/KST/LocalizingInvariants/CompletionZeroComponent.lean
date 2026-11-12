module

public import SerrePositivity.KST.LocalizingInvariants.CompletionNullDenominator
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberCompositionEdges
public import Mathlib.AlgebraicTopology.SimplicialSet.PiZero
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.QuasicategoryCore

/-!
概要：元の wide 部分圏の同じ成分では、一つの零分母の始域を共用できる。
方針：実合成二単体の二対三性で零分母条件を両方向へ運び、π₀ の生成関係に沿う。
規約：本質像と元の全辺条件を保ち、成分の同定を K₀ の商に置き換えない。
使われ方：Sp-7 の各成分で、全図式の零ホモトピーを wide 内へ持ち上げる。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
variable {C D : SSet.{u}} [Quasicategory C] [Quasicategory D] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable D]
  (f : C ⟶ D) [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor f]
local instance : Preadditive D.HomotopyCategory := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.preadditive_ho (X := D)

/-- 概要：指定始域からの零射が、元の本質像の cofiber 分母であるという条件。
方針：実合成二単体の二対三性で零分母条件を両方向へ運び、π₀ の生成関係に沿う。
規約：本質像と元の全辺条件を保ち、成分の同定を K₀ の商に置き換えない。
使われ方：Sp-7 の各成分で、全図式の零ホモトピーを wide 内へ持ち上げる。 -/
def completionZeroTarget (z y : D _⦋0⦌) : Prop :=
  (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHoClosure (completionEssentialImage f)).trW
    (0 : (HomotopyCategory.mk z : hoFunctor.obj D) ⟶ HomotopyCategory.mk y)

variable (h : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f)
include h

/-- 概要：元の本質像の分母には全ての退化辺が属する。
方針：実合成二単体の二対三性で零分母条件を両方向へ運び、π₀ の生成関係に沿う。
規約：本質像と元の全辺条件を保ち、成分の同定を K₀ の商に置き換えない。
使われ方：Sp-7 の各成分で、全図式の零ホモトピーを wide 内へ持ち上げる。 -/
lemma completionCofiber_degenerate (z : D _⦋0⦌) :
    D.σ 0 z ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberLocalizingEdges (completionEssentialImage f) := by
  rw [← stableClosure_completionEssentialImage f h.2.1]
  exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberStableEdges_of_isInvertible _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_degenerate z)

/-- 概要：元の wide 部分複体は周囲の全頂点を含む。
方針：実合成二単体の二対三性で零分母条件を両方向へ運び、π₀ の生成関係に沿う。
規約：本質像と元の全辺条件を保ち、成分の同定を K₀ の商に置き換えない。
使われ方：Sp-7 の各成分で、全図式の零ホモトピーを wide 内へ持ち上げる。 -/
lemma completionCofiberWide_vertex (z : D _⦋0⦌) :
    z ∈ (completionCofiberWide f).obj (Opposite.op ⦋0⦌) := by
  intro θ
  have ht : θ = SimplexCategory.σ (0 : Fin 1) := Subsingleton.elim _ _
  subst θ
  exact completionCofiber_degenerate f h z

/-- 概要：元の分母辺は、両端の退化を含めて同じ wide 部分複体の一単体になる。
方針：実合成二単体の二対三性で零分母条件を両方向へ運び、π₀ の生成関係に沿う。
規約：本質像と元の全辺条件を保ち、成分の同定を K₀ の商に置き換えない。
使われ方：Sp-7 の各成分で、全図式の零ホモトピーを wide 内へ持ち上げる。 -/
lemma completionCofiberWide_edge (e : D _⦋1⦌)
    (he : e ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberLocalizingEdges (completionEssentialImage f)) :
    e ∈ (completionCofiberWide f).obj (Opposite.op ⦋1⦌) := by
  intro θ
  rcases _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.intervalEndomorphism_cases θ with ht | ht | ht
  · have hc : SimplexCategory.const ⦋1⦌ ⦋1⦌ 0 =
        SimplexCategory.σ (0 : Fin 1) ≫ SimplexCategory.δ (1 : Fin 2) := by decide
    rw [ht, hc, op_comp, D.map_comp]
    exact completionCofiber_degenerate f h _
  · simpa [ht] using he
  · have hc : SimplexCategory.const ⦋1⦌ ⦋1⦌ 1 =
        SimplexCategory.σ (0 : Fin 1) ≫ SimplexCategory.δ (0 : Fin 2) := by decide
    rw [ht, hc, op_comp, D.map_comp]
    exact completionCofiber_degenerate f h _

/-- 概要：元の分母辺の両端で、同じ零分母の始域を使う条件は同値。
方針：実合成二単体の二対三性で零分母条件を両方向へ運び、π₀ の生成関係に沿う。
規約：本質像と元の全辺条件を保ち、成分の同定を K₀ の商に置き換えない。
使われ方：Sp-7 の各成分で、全図式の零ホモトピーを wide 内へ持ち上げる。 -/
lemma completionZeroTarget_edge_iff (z : D _⦋0⦌) {x y : D _⦋0⦌}
    (e : Truncated.Edge (X := (truncation 2).obj D) x y)
    (he : e.edge ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberLocalizingEdges (completionEssentialImage f)) :
    completionZeroTarget f z x ↔ completionZeroTarget f z y := by
  obtain ⟨a, ha⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective z x
    (0 : (HomotopyCategory.mk z : hoFunctor.obj D) ⟶ HomotopyCategory.mk x)
  obtain ⟨b, hb⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective z y
    (0 : (HomotopyCategory.mk z : hoFunctor.obj D) ⟶ HomotopyCategory.mk y)
  obtain ⟨s⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.compStruct_nonempty_of_homMk_fac
    (show Truncated.HomotopyCategory.homMk a ≫ Truncated.HomotopyCategory.homMk e =
      Truncated.HomotopyCategory.homMk b by rw [ha, hb, zero_comp])
  have he' : e.edge ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberLocalizingEdges
      {v | _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure (completionEssentialImage f) v} := by
    rwa [stableClosure_completionEssentialImage f h.2.1]
  have hax : completionZeroTarget f z x ↔ a.edge ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberLocalizingEdges
      {v | _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure (completionEssentialImage f) v} := by
    rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberStableEdges_iff_trW, ha]
    rfl
  have hby : completionZeroTarget f z y ↔ b.edge ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberLocalizingEdges
      {v | _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure (completionEssentialImage f) v} := by
    rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberStableEdges_iff_trW, hb]
    rfl
  have ht := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberStableEdges_compStruct_twoOfThree (completionEssentialImage f) s
  exact hax.trans ((Iff.intro (fun hw => ht.1 hw he') (fun hw => ht.2.2 he' hw)).trans hby.symm)

/-- 概要：同じ元の wide 成分の全頂点に対して、一つの零分母条件を輸送する。
方針：実合成二単体の二対三性で零分母条件を両方向へ運び、π₀ の生成関係に沿う。
規約：本質像と元の全辺条件を保ち、成分の同定を K₀ の商に置き換えない。
使われ方：Sp-7 の各成分で、全図式の零ホモトピーを wide 内へ持ち上げる。 -/
lemma completionZeroTarget_component (z : D _⦋0⦌)
    (x y : (completionCofiberWide f : SSet.{u}) _⦋0⦌)
    (he : SSet.π₀.mk x = SSet.π₀.mk y) :
    completionZeroTarget f z x.val ↔ completionZeroTarget f z y.val := by
  have hp := (SSet.π₀.mk_eq_mk_iff x y).1 he
  clear he
  induction hp with
  | rel a b hab =>
    obtain ⟨e⟩ := hab
    apply completionZeroTarget_edge_iff f h z (e.map (completionCofiberWide f).ι).toTruncated
    simpa using e.edge.property (𝟙 ⦋1⦌)
  | refl => exact Iff.rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- 概要：元の各成分の指定頂点には、同じ成分の全対象へ零分母を持つ始域がある。
方針：実合成二単体の二対三性で零分母条件を両方向へ運び、π₀ の生成関係に沿う。
規約：本質像と元の全辺条件を保ち、成分の同定を K₀ の商に置き換えない。
使われ方：Sp-7 の各成分で、全図式の零ホモトピーを wide 内へ持ち上げる。 -/
lemma exists_completionComponentZeroSource
    (x : (completionCofiberWide f : SSet.{u}) _⦋0⦌) :
    ∃ z : D _⦋0⦌, ∀ y : (completionCofiberWide f : SSet.{u}) _⦋0⦌,
      SSet.π₀.mk x = SSet.π₀.mk y → completionZeroTarget f z y.val := by
  obtain ⟨z, t, ht, hz⟩ := exists_completionNullDenominator f h x.val
  have hw : t.edge ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberLocalizingEdges
      {v | _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure (completionEssentialImage f) v} := by
    rwa [stableClosure_completionEssentialImage f h.2.1]
  have hx : completionZeroTarget f z x.val := by
    have hh := (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberStableEdges_iff_trW (completionEssentialImage f) t).1 hw
    rwa [hz] at hh
  exact ⟨z, fun y hy => (completionZeroTarget_component f h z x y hy).1 hx⟩

/-- 概要：各成分の零分母始域を、元の wide 部分複体の同じ成分の頂点として回収する。
方針：実合成二単体の二対三性で零分母条件を両方向へ運び、π₀ の生成関係に沿う。
規約：本質像と元の全辺条件を保ち、成分の同定を K₀ の商に置き換えない。
使われ方：Sp-7 の各成分で、全図式の零ホモトピーを wide 内へ持ち上げる。 -/
lemma exists_completionComponentZeroVertex
    (x : (completionCofiberWide f : SSet.{u}) _⦋0⦌) :
    ∃ z : (completionCofiberWide f : SSet.{u}) _⦋0⦌,
      SSet.π₀.mk z = SSet.π₀.mk x ∧
      ∀ y : (completionCofiberWide f : SSet.{u}) _⦋0⦌,
        SSet.π₀.mk x = SSet.π₀.mk y → completionZeroTarget f z.val y.val := by
  obtain ⟨z, t, ht, hz⟩ := exists_completionNullDenominator f h x.val
  let zv : (completionCofiberWide f : SSet.{u}) _⦋0⦌ :=
    ⟨z, completionCofiberWide_vertex f h z⟩
  let e : SSet.Edge zv x := SSet.Edge.mk
    ⟨t.edge, completionCofiberWide_edge f h t.edge ht⟩
      (Subtype.ext t.src_eq) (Subtype.ext t.tgt_eq)
  have hw : t.edge ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberLocalizingEdges
      {v | _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure (completionEssentialImage f) v} := by
    rwa [stableClosure_completionEssentialImage f h.2.1]
  have hx : completionZeroTarget f z x.val := by
    have hh := (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberStableEdges_iff_trW (completionEssentialImage f) t).1 hw
    rwa [hz] at hh
  exact ⟨zv, SSet.π₀.sound e,
    fun y hy => (completionZeroTarget_component f h z x y hy).1 hx⟩

end SerrePositivity.KST.LocalizingInvariants
