module
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.KSTSConstructionRelativeInitialExtension
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.InitialPrismBoundary
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.FunctorRelativeTerminal

/-! # 関手圏の点ごとの相対始点境界充填
概要：各点での相対始対象の普遍性を関手単体集合へ移す。
方針：境界とパラメーターの積を相対骨格で延長する。
規約：quasicategory 性・fibration 性を仮定しない。
使われ方：HTT 5.1.2.2 の余極限側と点ごとの押し出し。

対応節は Kerodon 7.1（Tag 02H1）。
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：標準単体の境界外の単体の始点は最初の標準頂点。
方針：単調写像の全射性から最小値が零と分かる。
規約：単体の次数は任意。使われ方：始点の相対境界充填の積への移送。 -/
lemma simplexFirstVertex_stdSimplex_of_notMem_boundary {n m : ℕ}
    (s : (Δ[n] : SSet.{u}) _⦋m⦌) (hs : s ∉ (boundary n).obj (Opposite.op ⦋m⦌)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexFirstVertex s = stdSimplex.obj₀Equiv.symm (0 : Fin (n + 1)) := by
  have hsurj : Function.Surjective (stdSimplex.asOrderHom s) := not_not.mp hs
  obtain ⟨j, hj⟩ := hsurj 0
  apply stdSimplex.obj₀Equiv.injective
  change s 0 = 0
  apply le_antisymm
  · rw [← hj]
    exact (stdSimplex.asOrderHom s).monotone (Fin.zero_le j)
  · exact Fin.zero_le _

/-- 概要：射の上の点ごとの始点境界充填は関手単体集合でも成り立つ。
方針：境界とパラメーターの直積で、各新しいセルの始点の充填条件を適用する。
規約：単体集合の quasicategory 性や射の fibration 性を必要としない。
使われ方：Kerodon Proposition 7.1.8.10（Tag 02XK） の空図式の場合の相対版への準備。 -/
lemma initialBoundaryLifting_ihom_of_pointwise {K X Y : SSet.{u}}
    (p : X ⟶ Y) (f : K ⟶ X)
    (hf : ∀ k : K _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialBoundaryLifting p (f.app (Opposite.op ⦋0⦌) k)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialBoundaryLifting ((ihom K).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f) := by
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
  have hbfirst : b.app (Opposite.op ⦋0⦌)
      ⟨stdSimplex.obj₀Equiv.symm (0), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.vertex_mem_boundary n _⟩ = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f := by
    apply SSet.yonedaEquiv.symm.injective
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex, SSet.yonedaEquiv_symm_comp] using hb
  have ht : ∀ (m : ℕ) (s : (K ⊗ (Δ[n + 1] : SSet.{u})) _⦋m + 1⦌),
      s ∉ A.obj (Opposite.op ⦋m + 1⦌) →
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialBoundaryLifting p (a.app (Opposite.op ⦋0⦌) ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexFirstVertex s, hA _⟩) := by
    intro m s hs
    have hs₂ : s.2 ∉ (boundary (n + 1)).obj (Opposite.op ⦋m + 1⦌) :=
      fun h ↦ hs ⟨by trivial, h⟩
    have he₂ := simplexFirstVertex_stdSimplex_of_notMem_boundary s.2 hs₂
    have ha : a.app (Opposite.op ⦋0⦌) ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexFirstVertex s, hA _⟩ =
        f.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexFirstVertex s.1) := by
      change (uncurry b).app (Opposite.op ⦋0⦌)
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexFirstVertex s).1, ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexFirstVertex s).2, _⟩) = _
      rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stable_simplexFirstVertex_prod]
      simp only [he₂]
      change (b.app (Opposite.op ⦋0⦌)
        ⟨stdSimplex.obj₀Equiv.symm (0), _⟩).app
          (Opposite.op ⦋0⦌) (𝟙 _) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexFirstVertex s.1) = _
      rw [hbfirst]
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
  obtain ⟨F, hF, hFp⟩ := exists_lift_of_initial_first_vertices A hA p a (uncurry β) hβ ht
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
