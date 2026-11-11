module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.FunctorTerminal
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.RelativeTerminalExtension

/-!
概要：関手単体集合での点ごとの相対境界充填。
方針：uncurry した境界を指定された標的の射の上で相対的に延長する。
規約：厳密な可換正方形の持ち上げとして定式化する。
使われ方：HTT 5.1.2.2、Kerodon §7.1.8（Tag 02X8） の相対極限の準備。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 概要：射の上の点ごとの終点境界充填は関手単体集合でも成り立つ。
方針：境界とパラメーターの直積で、各新しいセルの終点の充填条件を適用する。
規約：単体集合の quasicategory 性や射の fibration 性を必要としない。
使われ方：Kerodon Proposition 7.1.8.10（Tag 02XK） の空図式の場合の相対版への準備。 -/
lemma terminalBoundaryLifting_ihom_of_pointwise {K X Y : SSet.{u}}
    (p : X ⟶ Y) (f : K ⟶ X)
    (hf : ∀ k : K _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TerminalBoundaryLifting p (f.app (Opposite.op ⦋0⦌) k)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TerminalBoundaryLifting ((ihom K).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f) := by
  intro n b β hb sq
  let A : (K ⊗ (Δ[n + 1] : SSet.{u})).Subcomplex :=
    (⊤ : K.Subcomplex).prod (boundary (n + 1))
  let e : (A : SSet.{u}) ≅ K ⊗ (boundary (n + 1) : SSet.{u}) :=
    Subcomplex.prodIso ⊤ (boundary (n + 1)) ≪≫
      whiskerRightIso (Subcomplex.topIso K) (boundary (n + 1) : SSet.{u})
  let a : (A : SSet.{u}) ⟶ X := e.hom ≫ uncurry b
  have hA : ∀ v : (K ⊗ (Δ[n + 1] : SSet.{u})) _⦋0⦌,
      v ∈ A.obj (Opposite.op ⦋0⦌) := by
    intro v
    refine ⟨by trivial, ?_⟩
    have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.vertex_mem_boundary.{u} n (stdSimplex.obj₀Equiv.{u} v.2)
    rw [Equiv.symm_apply_apply] at h
    exact h
  have hblast : b.app (Opposite.op ⦋0⦌)
      ⟨stdSimplex.obj₀Equiv.symm (Fin.last (n + 1)), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.vertex_mem_boundary n _⟩ = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f := by
    apply SSet.yonedaEquiv.symm.injective
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex, SSet.yonedaEquiv_symm_comp] using hb
  have ht : ∀ (m : ℕ) (s : (K ⊗ (Δ[n + 1] : SSet.{u})) _⦋m + 1⦌),
      s ∉ A.obj (Opposite.op ⦋m + 1⦌) →
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TerminalBoundaryLifting p (a.app (Opposite.op ⦋0⦌) ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.simplexLastVertex s, hA _⟩) := by
    intro m s hs
    have hs₂ : s.2 ∉ (boundary (n + 1)).obj (Opposite.op ⦋m + 1⦌) :=
      fun h ↦ hs ⟨by trivial, h⟩
    have he₂ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.simplexLastVertex_stdSimplex_of_notMem_boundary s.2 hs₂
    have ha : a.app (Opposite.op ⦋0⦌) ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.simplexLastVertex s, hA _⟩ =
        f.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.simplexLastVertex s.1) := by
      change (uncurry b).app (Opposite.op ⦋0⦌)
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.simplexLastVertex s).1, ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.simplexLastVertex s).2, _⟩) = _
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.simplexLastVertex_prod]
      simp only [he₂]
      change (b.app (Opposite.op ⦋0⦌)
        ⟨stdSimplex.obj₀Equiv.symm (Fin.last (n + 1)), _⟩).app
          (Opposite.op ⦋0⦌) (𝟙 _) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.simplexLastVertex s.1) = _
      rw [hblast]
      rfl
    rw [ha]
    exact hf _
  have hehom : e.hom ≫ (K ◁ (boundary (n + 1)).ι) = A.ι := by
    apply SSet.hom_ext
    rintro ⟨⟨d⟩⟩
    apply ConcreteCategory.hom_ext
    intro x
    rfl
  have hβ : a ≫ p = A.ι ≫ uncurry β := by
    have h := congrArg (fun q ↦ uncurry q) sq.w
    rw [uncurry_natural_right, uncurry_natural_left] at h
    change (e.hom ≫ uncurry b) ≫ p = _
    rw [Category.assoc, h, ← Category.assoc, hehom]
  obtain ⟨F, hF, hFp⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.exists_lift_of_terminal_last_vertices A hA p a (uncurry β) hβ ht
  refine ⟨curry F, ?_, ?_⟩
  · apply uncurry_injective
    rw [uncurry_natural_left, uncurry_curry]
    have he : e.inv ≫ A.ι = K ◁ (boundary (n + 1)).ι := by
      apply SSet.hom_ext
      rintro ⟨⟨d⟩⟩
      apply ConcreteCategory.hom_ext
      intro x
      rfl
    rw [← he, Category.assoc, hF]
    simp only [a, Iso.inv_hom_id_assoc]
  · apply uncurry_injective
    rw [uncurry_natural_right, uncurry_curry]
    exact hFp

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
