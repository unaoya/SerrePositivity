module
public import SerrePositivity.KST.SConstruction.STwoCofiberRestriction
public import SerrePositivity.KST.SConstruction.FirstRowCofiberData

/-! # 中央の cofiber 正方形を保つ S₂ の相対補完
概要：正次元の境界で指定した S₂ 図式を保ち、中央の cofiber 正方形の族を延長する。
方針：中央部分複体とパラメーター境界を貼り、外側の零対角の始・終対象性で充填する。
規約：入力正方形を厳密に保持する。使われ方：S₂ と正方形表示の trivial Kan fibration。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

private lemma middle_pre_iso (C : SSet.{u}) :
    (pre arTwoMiddleSquare).app C ≫ (pre arTwoMiddleIso.inv).app C =
      (pre arTwoMiddle.ι).app C := by
  rw [← NatTrans.comp_app, ← pre_map, ← arTwoMiddleIso_ι, Iso.inv_hom_id_assoc]

/-- 概要：中央の正方形への制限は正次元の全境界を持ち上げる。
方針：中央正方形と境界を積で貼り、新しい単体の外側の零対角を使って延長する。
規約：C の安定性は不要。使われ方：正方形表示との厳密な相対比較。 -/
lemma sTwoCofiberRestriction_hasLiftingProperty_boundary (n : ℕ) (C : SSet.{u}) :
    HasLiftingProperty (boundary (n + 1)).ι (sTwoCofiberRestriction C) := by
  constructor
  intro a b sq
  let j := (gappedSubcomplex 2 C).ι
  let k : cofiberDiagrams C ⟶ (ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj C :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι
  let H := uncurry (a ≫ j)
  let G := uncurry (b ≫ k ≫ (pre arTwoMiddleIso.inv).app C)
  have h₀ : (a ≫ j) ≫ (pre arTwoMiddleSquare).app C = (boundary (n + 1)).ι ≫ (b ≫ k) := by
    calc
      _ = a ≫ sTwoCofiberRestriction C ≫ k := by
        rw [sTwoCofiberRestriction_ι]
        exact Category.assoc _ _ _
      _ = _ := by rw [← Category.assoc, sq.w, Category.assoc]
  have hs : (a ≫ j) ≫ (pre arTwoMiddle.ι).app C =
      (boundary (n + 1)).ι ≫ (b ≫ k ≫ (pre arTwoMiddleIso.inv).app C) := by
    rw [← middle_pre_iso]
    simpa only [Category.assoc] using congrArg (fun f => f ≫ (pre arTwoMiddleIso.inv).app C) h₀
  have hw : (arTwoMiddle.ι ▷ (boundary (n + 1) : SSet.{u})) ≫ H =
      ((arTwoMiddle : SSet.{u}) ◁ (boundary (n + 1)).ι) ≫ G := by
    have hh := congrArg uncurry hs
    rw [uncurry_pre_app, uncurry_natural_left] at hh
    exact hh
  obtain ⟨F, hFa, hFm⟩ := frame_extend_boundary arTwoMiddle n H G hw (by
    intro m s hsm
    rcases arTwoMiddle_missing_endpoint s hsm with he | he
    · left
      intro v
      let V := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (arNerve 2) C).symm ((a ≫ j).app (Opposite.op ⦋0⦌) v)
      have hV : IsGapped V := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex (a.app (Opposite.op ⦋0⦌) v)
      have hv : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex V = (a ≫ j).app (Opposite.op ⦋0⦌) v :=
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ C).apply_symm_apply _
      have he₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexFirstVertex s = ComposableArrows.mk₀ (arObj 0 0 le_rfl) := by
        exact (ComposableArrows.ext₀ rfl).trans (congrArg ComposableArrows.mk₀ he)
      change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex (((a ≫ j).app (Opposite.op ⦋0⦌) v).app
        (Opposite.op ⦋0⦌) (𝟙 _) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexFirstVertex s))
      rw [← hv, he₀]
      exact (hV.1 0).1
    · right
      intro v
      let V := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (arNerve 2) C).symm ((a ≫ j).app (Opposite.op ⦋0⦌) v)
      have hV : IsGapped V := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex (a.app (Opposite.op ⦋0⦌) v)
      have hv : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex V = (a ≫ j).app (Opposite.op ⦋0⦌) v :=
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ C).apply_symm_apply _
      have he₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.simplexLastVertex s = ComposableArrows.mk₀ (arObj 2 2 le_rfl) := by
        exact (ComposableArrows.ext₀ rfl).trans (congrArg ComposableArrows.mk₀ he)
      change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex (((a ≫ j).app (Opposite.op ⦋0⦌) v).app
        (Opposite.op ⦋0⦌) (𝟙 _) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.simplexLastVertex s))
      rw [← hv, he₁]
      exact (hV.1 2).2)
  let f := curry F
  have ha : (boundary (n + 1)).ι ≫ f = a ≫ j := by
    apply uncurry_injective
    rw [uncurry_natural_left, uncurry_curry]
    exact hFa
  have hm : f ≫ (pre arTwoMiddle.ι).app C = b ≫ k ≫ (pre arTwoMiddleIso.inv).app C := by
    apply uncurry_injective
    rw [uncurry_pre_app, uncurry_curry]
    exact hFm
  have hmid : f ≫ (pre arTwoMiddleSquare).app C = b ≫ k := by
    apply (cancel_mono ((pre arTwoMiddleIso.inv).app C)).1
    rw [Category.assoc, middle_pre_iso]
    exact hm
  have hv : ∀ v : (Δ[n + 1] : SSet.{u}) _⦋0⦌,
      IsGapped ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (arNerve 2) C).symm (f.app (Opposite.op ⦋0⦌) v)) := by
    intro v
    obtain ⟨w, hw⟩ := boundary_vertex_surjective n v
    have he := ConcreteCategory.congr_hom (NatTrans.congr_app ha (Opposite.op ⦋0⦌)) w
    change f.app (Opposite.op ⦋0⦌) ((boundary (n + 1)).ι.app (Opposite.op ⦋0⦌) w) =
      (a.app (Opposite.op ⦋0⦌) w).val at he
    rw [hw] at he
    rw [he]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex (a.app (Opposite.op ⦋0⦌) w)
  let l : (Δ[n + 1] : SSet.{u}) ⟶ sConstruction 2 C :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift (fun v => IsGapped ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (arNerve 2) C).symm v)) f hv
  have hl : l ≫ j = f := rfl
  exact CommSq.HasLift.mk' {
    l := l
    fac_left := by
      apply (cancel_mono j).1
      rw [Category.assoc, hl]
      exact ha
    fac_right := by
      apply (cancel_mono k).1
      rw [Category.assoc, sTwoCofiberRestriction_ι, ← Category.assoc, hl]
      exact hmid }

/-- 概要：S₂ から中央の cofiber 正方形への制限は trivial Kan fibration。
方針：零次元は cofiber 正方形の外側の零対角を補い、正次元は相対境界補完を使う。
規約：C は quasicategory のみ。使われ方：McCarthy の正方形表示と S₂ の比較。 -/
instance sTwoCofiberRestriction_trivialKanFibration (C : SSet.{u}) [Quasicategory C] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (sTwoCofiberRestriction C) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibration_iff_boundary _).2
  intro n
  cases n with
  | zero =>
    constructor
    intro a b sq
    obtain ⟨v, hv⟩ := sTwoCofiberRestriction_vertex_surjective C (SSet.yonedaEquiv b)
    refine CommSq.HasLift.mk' {
      l := SSet.yonedaEquiv.symm v
      fac_left := boundary.hom_ext₀
      fac_right := ?_ }
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
    exact hv
  | succ n => exact sTwoCofiberRestriction_hasLiftingProperty_boundary n C

end SerrePositivity.KST.SConstruction
