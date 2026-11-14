module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierFiniteSpanRecovery
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.AnchoredFiniteFactorization
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.AnodyneHomotopyExtension

/-!
概要：指定実境界を、同じ実輸送円柱とともに完成分母族から回収する。
方針：境界付き有限台を共通実分母へ輸送し、Kan fiber への延長と指定円柱の延長を使う。
規約：境界上の比較は同型類でなく、元の実円柱の単位像と厳密に一致する。
使われ方：c5 の共有経路を保つ第一行単体比較の貼合せ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open HomotopicalAlgebra SSet.modelCategoryQuillen
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Fibration
namespace SerrePositivity.KST.LocalizingInvariants

/-- 指定実境界の輸送円柱を、完成族の比較円柱への厳密な制限として回収する。 -/
lemma verdierDenominatorSpan_relative_finite_recovery
    {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}
    (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) (x y : B.obj _⦋0⦌)
    {S K : SSet.{u}} [S.Finite] [K.Finite] (j : S ⟶ K)
    (a : S ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierDenominatorSpanFamily i x y)
    (f : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierDenominatorSpanFamily i x y))
    (ha : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierDenominatorSpanFamily i x y) = j ≫ f) :
    ∃ d : (verdierDenominatorOver i x : SSet.{u}) _⦋0⦌,
      ∃ g : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierDenominatorSpanProjection i x y) d,
        ∃ L : SSet.Homotopy
          (j ≫ g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierDenominatorSpanProjection i x y) d) a,
        ∃ G : SSet.Homotopy
          (g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierDenominatorSpanProjection i x y) d ≫
            _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierDenominatorSpanFamily i x y)) f,
          (j ▷ (Δ[1] : SSet.{u})) ≫ G.h = L.h ≫
            _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierDenominatorSpanFamily i x y) := by
  let E := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierDenominatorSpanFamily i x y
  let p := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierDenominatorSpanProjection i x y
  obtain ⟨J, a', r, ha', hjr, hrf⟩ :=
    _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.continuousKanReplacement_anchored_finite_factorization j a f ha
  obtain ⟨d, g₀, ⟨H⟩⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierDenominatorSpan_finite_fiber_detection h x y J.val.ι
  let V := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p d
  have : KanComplex V := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_kanComplex p d
  have hη := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit_anodyne (J.val : SSet.{u})
  have := hη (terminal.from V)
    (by rw [← HomotopicalAlgebra.fibration_iff]; infer_instance)
  have sq : CommSq g₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app J.val)
      (terminal.from V) (terminal.from (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj J.val)) :=
    ⟨terminalIsTerminal.hom_ext _ _⟩
  let R := sq.lift
  have hR : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app J.val ≫ R = g₀ := sq.fac_left
  let g := r ≫ R
  have hjg : j ≫ g = a' ≫ g₀ := by
    dsimp only [g]
    rw [← Category.assoc, hjr, Category.assoc, hR]
  let L : SSet.Homotopy (j ≫ g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p d) a := {
    h := (a' ▷ (Δ[1] : SSet.{u})) ≫ H.h
    h₀ := by
      rw [SSet.ι₀_comp_assoc, H.h₀, ← Category.assoc, ← hjg]
      exact Category.assoc _ _ _
    h₁ := by
      rw [SSet.ι₁_comp_assoc, H.h₁]
      exact ha'
    rel := by
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro z
      exact False.elim z.1.property }
  let u := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app E
  let F := R ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p d ≫ u
  let D := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map J.val.ι
  let H₀ : SSet.Homotopy
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app J.val ≫ F)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app J.val ≫ D) := {
    h := H.h ≫ u
    h₀ := by
      rw [← Category.assoc, H.h₀]
      dsimp only [F]
      rw [← Category.assoc, ← Category.assoc, hR, Category.assoc]
      rfl
    h₁ := by
      rw [← Category.assoc, H.h₁]
      exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.naturality J.val.ι
    rel := by
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro z
      exact False.elim z.1.property }
  obtain ⟨G₀, hG₀⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.anodyne_homotopy_extension
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app J.val) hη F D H₀
  let G : SSet.Homotopy (g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p d ≫ u) f := {
    h := (r ▷ (Δ[1] : SSet.{u})) ≫ G₀.h
    h₀ := by
      rw [SSet.ι₀_comp_assoc, G₀.h₀]
      dsimp only [g, F]
      simp only [Category.assoc]
      rfl
    h₁ := by
      rw [SSet.ι₁_comp_assoc, G₀.h₁]
      exact hrf
    rel := by
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro z
      exact False.elim z.1.property }
  refine ⟨d, g, L, G, ?_⟩
  change (j ▷ (Δ[1] : SSet.{u})) ≫ (r ▷ (Δ[1] : SSet.{u})) ≫ G₀.h = _
  rw [← comp_whiskerRight_assoc, hjr, comp_whiskerRight, Category.assoc, hG₀]
  rfl

end SerrePositivity.KST.LocalizingInvariants
