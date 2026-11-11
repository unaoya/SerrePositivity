module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.FixedVertexCoconeLift

/-!
概要：一つの余錐を固定した始域の忘却は filtered 余極限を保存する。
方針：反復 coslice 同型で一点 coslice の射影へ同定する。
規約：元の余錐全体と元の固定図式を保持する。
使われ方：入力図式の下の正規化表示の余極限性の回収。

対応節は Kerodon 9.4（Tag 06GT）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility


/-- 概要：固定した全余錐の下から、元の図式の下へ忘却する射。
方針：元の左包含へ制限し、余錐の固定条件で図式を戻す。
規約：元の可変終点を保つ。
使われ方：正規化した表示を元の入力図式の下へ戻す。 -/
def coneSourceForget {K C : SSet.{u}} {q : K ⟶ C} (w : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone q) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder w.val ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder q :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict w.val (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K Δ[0]) ≫
    (eqToIso (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder w.property)).hom

/-- 概要：固定余錐の忘却の全単体値は元の図式への制限。
方針：等号輸送の値を消去する。
規約：全次数での厳密な等式。
使われ方：元の入力と指定終点の回収。 -/
lemma coneSourceForget_val {K C : SSet.{u}} {q : K ⟶ C} (w : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone q)
    {n : ℕ} (σ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder w.val) _⦋n⦌) :
    ((coneSourceForget w).app (Opposite.op ⦋n⦌) σ).val =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K Δ[0]) (𝟙 Δ[n]) ≫ σ.val := by
  change ((eqToIso (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder w.property)).hom.app (Opposite.op ⦋n⦌)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict w.val (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K Δ[0])).app (Opposite.op ⦋n⦌) σ)).val = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.sliceUnder_eqToIso_val w.property]
  rfl

/-- 概要：反復 coslice の元の図式への制限は各単体でも同じ全制限。
方針：元の全族の展開公式を Yoneda 族へ適用する。
規約：全次数の等式。
使われ方：固定余錐の忘却と一点 coslice 射影の比較。 -/
lemma uncurriedSourceRestriction_val {K L C : SSet.{u}} {p : K ⟶ C}
    (q : L ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p) {n : ℕ} (σ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry q)) _⦋n⦌) :
    ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.uncurriedSliceUnderRestriction q).app (Opposite.op ⦋n⦌) σ).val =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K L) (𝟙 Δ[n]) ≫ σ.val := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.uncurriedSliceUnderRestriction_uncurry q (SSet.yonedaEquiv.symm σ)
  rw [SSet.yonedaEquiv_symm_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceUnderUncurry_yoneda,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceUnderUncurry_yoneda] at h
  exact h

/-- 概要：固定余錐の忘却は反復 coslice 同型を通した元の制限。
方針：全単体値の等式を使う。
規約：元の全図式を厳密に保持する。
使われ方：一点 coslice 射影の filtered 保存性への帰着。 -/
lemma coneSourceForget_eq {K C : SSet.{u}} {q : K ⟶ C} (w : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone q) :
    coneSourceForget w =
      (eqToIso (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceUnderUncurry_yoneda 0 w).symm)).hom ≫
        _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.uncurriedSliceUnderRestriction (SSet.yonedaEquiv.symm w) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro σ
  apply Subtype.ext
  rw [coneSourceForget_val]
  change _ = ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.uncurriedSliceUnderRestriction (SSet.yonedaEquiv.symm w)).app n
    ((eqToIso (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceUnderUncurry_yoneda 0 w).symm)).hom.app n σ)).val
  rw [uncurriedSourceRestriction_val,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.sliceUnder_eqToIso_val (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceUnderUncurry_yoneda 0 w).symm]

/-- 概要：固定した余錐の忘却は元の底への可変終点射影を保つ。
方針：等号輸送の射影と固定始域制限の射影を合成する。
規約：元の全射影の等式。
使われ方：正規化した表示の compact 成分の回収。 -/
lemma coneSourceForget_projection {K C : SSet.{u}} {q : K ⟶ C} (w : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone q) :
    coneSourceForget w ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection q = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection w.val := by
  have hep {A X : SSet.{u}} {f g : A ⟶ X} (h : f = g) :
      (eqToIso (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder h)).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection g =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection f := by
    subst g
    rfl
  rw [coneSourceForget, Category.assoc, hep w.property, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.sliceUnderRestrict_projection]

/-- 概要：固定した全余錐の忘却は同じ正則濃度の filtered 余極限を保存する。
方針：二つの実同型と一点 coslice の射影に分解する。
規約：元の圏の余極限存在や全余完備性は不要。
使われ方：元の入力を固定する filtered 表示の余極限性。 -/
lemma coneSourceForget_isKappaAccessibleFunctor {μ : Cardinal.{u}} (hμ : μ.IsRegular)
    {K C : SSet.{u + 1}} [Quasicategory C] {q : K ⟶ C} (w : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone q) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor μ (coneSourceForget w) := by
  rw [coneSourceForget_eq]
  let e := eqToIso (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceUnderUncurry_yoneda 0 w).symm)
  let v : (Δ[0] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder q := SSet.yonedaEquiv.symm w
  have h : _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.uncurriedSliceUnderRestriction v =
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.iteratedSliceUnderIso v).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection v := by
    rw [← _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.iteratedSliceUnderIso_restriction v, ← Category.assoc,
      Iso.inv_hom_id, Category.id_comp]
  rw [h]
  have hvp : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor μ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection v) := by
    dsimp only [v]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sourceCosliceProjection_isKappaAccessibleFunctor (C := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder q) hμ
      (show (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder q) _⦋0⦌ from w)
  exact (_root_.SerrePositivity.InfinityCategories.HTT.AccessibleInfinityCategories.equivalence_preservesSmallKappaFilteredColimits μ
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso e).isQCatEquivalence).comp
      ((_root_.SerrePositivity.InfinityCategories.HTT.AccessibleInfinityCategories.equivalence_preservesSmallKappaFilteredColimits μ
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.iteratedSliceUnderIso v).symm).isQCatEquivalence).comp
          hvp)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility
