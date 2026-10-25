module

public import SerrePositivity.KST.LocalizingInvariants.CompletionNullDenominator
public import SerrePositivity.InfinityCategories.Stable.CofiberCompositionEdges
public import Mathlib.AlgebraicTopology.SimplicialSet.PiZero
public import SerrePositivity.InfinityCategories.F1.Categories.QuasicategoryCore

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
variable {C D : SSet.{u}} [Quasicategory C] [Quasicategory D] [IsStable C] [IsStable D]
  (f : C ⟶ D) [IsExactFunctor f]
local instance : Preadditive D.HomotopyCategory := preadditive_ho (X := D)

/-- 指定始域からの零射が、元の本質像の cofiber 分母であるという条件。 -/
def completionZeroTarget (z y : D _⦋0⦌) : Prop :=
  (stableHoClosure (completionEssentialImage f)).trW
    (0 : (HomotopyCategory.mk z : hoFunctor.obj D) ⟶ HomotopyCategory.mk y)

variable (h : F2.Idempotent.IsIdempotentCompletion f)
include h

/-- 元の本質像の分母には全ての退化辺が属する。 -/
lemma completionCofiber_degenerate (z : D _⦋0⦌) :
    D.σ 0 z ∈ cofiberLocalizingEdges (completionEssentialImage f) := by
  rw [← stableClosure_completionEssentialImage f h.2.1]
  exact cofiberStableEdges_of_isInvertible _ (isInvertibleEdge_degenerate z)

/-- 元の wide 部分複体は周囲の全頂点を含む。 -/
lemma completionCofiberWide_vertex (z : D _⦋0⦌) :
    z ∈ (completionCofiberWide f).obj (Opposite.op ⦋0⦌) := by
  intro θ
  have ht : θ = SimplexCategory.σ (0 : Fin 1) := Subsingleton.elim _ _
  subst θ
  exact completionCofiber_degenerate f h z

/-- 元の分母辺は、両端の退化を含めて同じ wide 部分複体の一単体になる。 -/
lemma completionCofiberWide_edge (e : D _⦋1⦌)
    (he : e ∈ cofiberLocalizingEdges (completionEssentialImage f)) :
    e ∈ (completionCofiberWide f).obj (Opposite.op ⦋1⦌) := by
  intro θ
  rcases intervalEndomorphism_cases θ with ht | ht | ht
  · have hc : SimplexCategory.const ⦋1⦌ ⦋1⦌ 0 =
        SimplexCategory.σ (0 : Fin 1) ≫ SimplexCategory.δ (1 : Fin 2) := by decide
    rw [ht, hc, op_comp, D.map_comp]
    exact completionCofiber_degenerate f h _
  · simpa [ht] using he
  · have hc : SimplexCategory.const ⦋1⦌ ⦋1⦌ 1 =
        SimplexCategory.σ (0 : Fin 1) ≫ SimplexCategory.δ (0 : Fin 2) := by decide
    rw [ht, hc, op_comp, D.map_comp]
    exact completionCofiber_degenerate f h _

/-- 元の分母辺の両端で、同じ零分母の始域を使う条件は同値。 -/
lemma completionZeroTarget_edge_iff (z : D _⦋0⦌) {x y : D _⦋0⦌}
    (e : Truncated.Edge (X := (truncation 2).obj D) x y)
    (he : e.edge ∈ cofiberLocalizingEdges (completionEssentialImage f)) :
    completionZeroTarget f z x ↔ completionZeroTarget f z y := by
  obtain ⟨a, ha⟩ := homotopyCategory_homMk_surjective z x
    (0 : (HomotopyCategory.mk z : hoFunctor.obj D) ⟶ HomotopyCategory.mk x)
  obtain ⟨b, hb⟩ := homotopyCategory_homMk_surjective z y
    (0 : (HomotopyCategory.mk z : hoFunctor.obj D) ⟶ HomotopyCategory.mk y)
  obtain ⟨s⟩ := compStruct_nonempty_of_homMk_fac
    (show Truncated.HomotopyCategory.homMk a ≫ Truncated.HomotopyCategory.homMk e =
      Truncated.HomotopyCategory.homMk b by rw [ha, hb, zero_comp])
  have he' : e.edge ∈ cofiberLocalizingEdges
      {v | StableVertexClosure (completionEssentialImage f) v} := by
    rwa [stableClosure_completionEssentialImage f h.2.1]
  have hax : completionZeroTarget f z x ↔ a.edge ∈ cofiberLocalizingEdges
      {v | StableVertexClosure (completionEssentialImage f) v} := by
    rw [cofiberStableEdges_iff_trW, ha]
    rfl
  have hby : completionZeroTarget f z y ↔ b.edge ∈ cofiberLocalizingEdges
      {v | StableVertexClosure (completionEssentialImage f) v} := by
    rw [cofiberStableEdges_iff_trW, hb]
    rfl
  have ht := cofiberStableEdges_compStruct_twoOfThree (completionEssentialImage f) s
  exact hax.trans ((Iff.intro (fun hw => ht.1 hw he') (fun hw => ht.2.2 he' hw)).trans hby.symm)

/-- 同じ元の wide 成分の全頂点に対して、一つの零分母条件を輸送する。 -/
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

/-- 元の各成分の指定頂点には、同じ成分の全対象へ零分母を持つ始域がある。 -/
lemma exists_completionComponentZeroSource
    (x : (completionCofiberWide f : SSet.{u}) _⦋0⦌) :
    ∃ z : D _⦋0⦌, ∀ y : (completionCofiberWide f : SSet.{u}) _⦋0⦌,
      SSet.π₀.mk x = SSet.π₀.mk y → completionZeroTarget f z y.val := by
  obtain ⟨z, t, ht, hz⟩ := exists_completionNullDenominator f h x.val
  have hw : t.edge ∈ cofiberLocalizingEdges
      {v | StableVertexClosure (completionEssentialImage f) v} := by
    rwa [stableClosure_completionEssentialImage f h.2.1]
  have hx : completionZeroTarget f z x.val := by
    have hh := (cofiberStableEdges_iff_trW (completionEssentialImage f) t).1 hw
    rwa [hz] at hh
  exact ⟨z, fun y hy => (completionZeroTarget_component f h z x y hy).1 hx⟩

/-- 各成分の零分母始域を、元の wide 部分複体の同じ成分の頂点として回収する。 -/
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
  have hw : t.edge ∈ cofiberLocalizingEdges
      {v | StableVertexClosure (completionEssentialImage f) v} := by
    rwa [stableClosure_completionEssentialImage f h.2.1]
  have hx : completionZeroTarget f z x.val := by
    have hh := (cofiberStableEdges_iff_trW (completionEssentialImage f) t).1 hw
    rwa [hz] at hh
  exact ⟨zv, SSet.π₀.sound e,
    fun y hy => (completionZeroTarget_component f h z x y hy).1 hx⟩

end SerrePositivity.KST.LocalizingInvariants
