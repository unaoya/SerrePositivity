module
public import SerrePositivity.KST.SConstruction.ArTwoMiddleBoundary
public import SerrePositivity.KST.SConstruction.GappedTriples

/-! # cofiber 正方形の Ar[2] 図式への延長
概要：一つの cofiber 正方形に最初と最後の零対角を補い、gapped Ar[2] 図式を作る。
方針：中央の部分図式を保ち、残りを始対象・終対象の充填で延長する。
規約：実際の正方形を厳密に保つ。使われ方：BGT Lemma 7.3 の次数2の存在。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：任意の正方形の図式に零の両端を補って Ar[2] 図式を作れる。
方針：中央以外の単体の始点または終点の零対象性で延長する。
規約：C の quasicategory 性は不要。使われ方：選んだ cofiber の厳密な配置。 -/
lemma exists_arTwo_extension_with_zero_endpoints {C : SSet.{u}}
    (T : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ C) (z : C _⦋0⦌) (hz : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex z) :
    ∃ F : arNerve 2 ⟶ C, arTwoMiddleSquare ≫ F = T ∧
      F.app (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ (arObj 0 0 le_rfl)) = z ∧
      F.app (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ (arObj 2 2 le_rfl)) = z := by
  classical
  let a : (arTwoMiddle : SSet.{u}) ⟶ C := arTwoMiddleIso.inv ≫ T
  let x : (arNerve.{u} 2) _⦋0⦌ → C _⦋0⦌ := fun v =>
    if h : v ∈ arTwoMiddle.obj (Opposite.op ⦋0⦌) then a.app (Opposite.op ⦋0⦌) ⟨v, h⟩ else z
  have hx (v : (arTwoMiddle : SSet.{u}) _⦋0⦌) : x v.val = a.app (Opposite.op ⦋0⦌) v := by
    dsimp only [x]
    rw [dif_pos v.property]
    rfl
  obtain ⟨F, hF, hv⟩ := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.exists_extension_with_vertices arTwoMiddle a x hx (by
    intro n s hs
    rcases arTwoMiddle_missing_endpoint s hs with he | he
    · left
      have he₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexFirstVertex s = ComposableArrows.mk₀ (s.obj 0) :=
        ComposableArrows.ext₀ rfl
      rw [he₀, he]
      change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex (if h : _ ∈ arTwoMiddle.obj (Opposite.op ⦋0⦌) then _ else z)
      rw [dif_neg arTwoMiddle_notMem_first]
      exact hz.1
    · right
      have he₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.simplexLastVertex s = ComposableArrows.mk₀ (s.obj (Fin.last (n + 1))) :=
        ComposableArrows.ext₀ rfl
      rw [he₁, he]
      change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex (if h : _ ∈ arTwoMiddle.obj (Opposite.op ⦋0⦌) then _ else z)
      rw [dif_neg arTwoMiddle_notMem_last]
      exact hz.2)
  refine ⟨F, ?_, ?_, ?_⟩
  · rw [← arTwoMiddleIso_ι, Category.assoc, hF]
    dsimp only [a]
    rw [Iso.hom_inv_id_assoc]
  · rw [hv]
    exact dif_neg arTwoMiddle_notMem_first
  · rw [hv]
    exact dif_neg arTwoMiddle_notMem_last

/-- 概要：中央が cofiber 正方形で両端が零なら Ar[2] 図式は gapped。
方針：唯一の非退化三つ組は (0,1,2) であり、その正方形は指定されたもの。
規約：C は quasicategory。使われ方：次数2の第一行制限の存在。 -/
lemma isGapped_two_of_cofiber_middle {C : SSet.{u}} [Quasicategory C]
    (F : arNerve 2 ⟶ C) (T : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle C) (hT : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsCofiberSequence T)
    (hF : arTwoMiddleSquare ≫ F = T.square)
    (h₀ : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (F.app (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ (arObj 0 0 le_rfl))))
    (h₂ : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (F.app (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ (arObj 2 2 le_rfl)))) :
    IsGapped F := by
  apply (isGapped_iff_triples F).2
  constructor
  · intro j
    fin_cases j
    · exact h₀
    · have he := congrArg (fun f : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ C => _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex f 0 1) hF
      change F.app (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ (arObj 1 1 le_rfl)) =
        _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex T.square 0 1 at he
      exact he.symm ▸ T.zero_corner
    · exact h₂
  · intro i j k hij hjk
    by_cases h : i = j
    · exact arSquare_isPushout_of_repeated_endpoints F i j j k hij le_rfl hjk (Or.inl h)
    by_cases h' : j = k
    · exact arSquare_isPushout_of_repeated_endpoints F i j j k hij le_rfl hjk (Or.inr h')
    have hne : i.val ≠ j.val := fun he => h (Fin.ext he)
    have hne' : j.val ≠ k.val := fun he => h' (Fin.ext he)
    have hijNat : i.val ≤ j.val := hij
    have hjkNat : j.val ≤ k.val := hjk
    have hklt := k.isLt
    have hi : i = 0 := by apply Fin.ext; change i.val = 0; omega
    have hj : j = 1 := by apply Fin.ext; change j.val = 1; omega
    have hk : k = 2 := by apply Fin.ext; change k.val = 2; omega
    subst i
    subst j
    subst k
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (arTwoMiddleSquare ≫ F)
    rw [hF]
    exact hT

/-- 概要：任意の cofiber 正方形は gapped Ar[2] 図式の中央に厳密に配置できる。
方針：その零角を両端の零頂点にも使って延長し、三つ組の判定を使う。
規約：安定性は不要で実際の cofiber を入力する。
使われ方：次数2の第一行からの構成。 -/
lemma exists_gapped_arTwo_of_cofiber {C : SSet.{u}} [Quasicategory C]
    (T : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle C) (hT : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsCofiberSequence T) :
    ∃ F : arNerve 2 ⟶ C, IsGapped F ∧ arTwoMiddleSquare ≫ F = T.square := by
  obtain ⟨F, hF, h₀, h₂⟩ := exists_arTwo_extension_with_zero_endpoints T.square
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex T.square 0 1) T.zero_corner
  refine ⟨F, isGapped_two_of_cofiber_middle F T hT hF ?_ ?_, hF⟩
  · rw [h₀]
    exact T.zero_corner
  · rw [h₂]
    exact T.zero_corner

end SerrePositivity.KST.SConstruction
