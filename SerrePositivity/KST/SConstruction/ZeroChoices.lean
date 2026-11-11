module
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Pointed
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.FullSubcomplexFibration

/-! # 零対象の選択空間
概要：全ての零対象の全部分複体は、非空なら可縮な Kan 複体となる。
方針：正次元の境界は終対象性で埋め、頂点条件を境界から回収する。
規約：零対象は固定しない。使われ方：BGT Lemma 7.3 の零対角の選択。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：全ての零対象が張る充満部分複体。
方針：α-S の IsZeroVertex を頂点条件に取る。
規約：零対象がない場合も定義する。使われ方：S• の零対角の族。 -/
def zeroChoices (C : SSet.{u}) : C.Subcomplex := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices C _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex

/-- 概要：零対象の選択空間は可縮な Kan 複体。
方針：零次元は存在、正次元は終対象性で境界を充填する。
規約：周囲 C の quasicategory 性は不要。使われ方：第一行制限の零対角。 -/
lemma zeroChoices_isContractibleKan (C : SSet.{u}) [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HasZeroVertex C] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (zeroChoices C : SSet.{u}) := by
  intro n b
  cases n with
  | zero =>
    let z := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.chosenZeroVertex C
    let v : (zeroChoices C : SSet.{u}) _⦋0⦌ := ⟨z.vertex, by
      intro α
      have hα : α = 𝟙 ⦋0⦌ := Subsingleton.elim _ _
      simpa only [hα, op_id, CategoryTheory.Functor.map_id_apply] using z.isZero⟩
    exact ⟨SSet.const v, boundary.hom_ext₀⟩
  | succ n =>
    let b' := b ≫ (zeroChoices C).ι
    let x := SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n (Fin.last (n + 1)) ≫ b)
    have hx : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex x.val := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex x
    have he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n (Fin.last (n + 1)) ≫ b' =
        SSet.yonedaEquiv.symm x.val := by
      apply SSet.yonedaEquiv.injective
      rw [Equiv.apply_symm_apply]
      rfl
    obtain ⟨F, hF⟩ := hx.2 n b' he
    have hv (v : ⦋0⦌ ⟶ ⦋n + 1⦌) :
        _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (SSet.yonedaEquiv (stdSimplex.map v ≫ F)) := by
      have hι : stdSimplex.map v =
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n (v.toOrderHom 0) ≫ (boundary (n + 1)).ι := by
        rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex_ι]
        apply SSet.yonedaEquiv.injective
        rw [Equiv.apply_symm_apply]
        apply stdSimplex.ext
        intro i
        fin_cases i
        rfl
      rw [hι, Category.assoc, hF]
      exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex
        (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n (v.toOrderHom 0) ≫ b))
    refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLiftSimplex _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex F hv, ?_⟩
    apply (cancel_mono (zeroChoices C).ι).1
    change (boundary (n + 1)).ι ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLiftSimplex _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex F hv ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices C _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex).ι = b'
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLiftSimplex_ι]
    exact hF

/-- 概要：零対象の全部分複体は Kan 複体。
方針：全境界の充填からホーンの充填を得る。
規約：HasZeroVertex のみを要求する。使われ方：零対角の core。 -/
instance zeroChoices_kanComplex (C : SSet.{u}) [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HasZeroVertex C] :
    KanComplex (zeroChoices C : SSet.{u}) := (zeroChoices_isContractibleKan C).kanComplex

/-- 概要：零対象の族は任意の単射に沿って相対的に延長できる。
方針：可縮な Kan 複体から点への trivial Kan fibration を使う。
規約：既存の族への制限は厳密に等しい。使われ方：第一行の零対角の補完。 -/
lemma exists_zeroChoices_extension {A B C : SSet.{u}} [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HasZeroVertex C]
    (i : A ⟶ B) [Mono i] (f : A ⟶ (zeroChoices C : SSet.{u})) :
    ∃ F : B ⟶ (zeroChoices C : SSet.{u}), i ≫ F = f := by
  have ht := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.isContractibleKan_iff_trivialKanFibration _).1 (zeroChoices_isContractibleKan C)
  have := ht.mem i inferInstance
  have sq : CommSq f i (CategoryTheory.Limits.terminal.from (zeroChoices C : SSet.{u}))
      (CategoryTheory.Limits.terminal.from B) := ⟨CategoryTheory.Limits.terminal.hom_ext _ _⟩
  exact ⟨sq.lift, sq.fac_left⟩

end SerrePositivity.KST.SConstruction
