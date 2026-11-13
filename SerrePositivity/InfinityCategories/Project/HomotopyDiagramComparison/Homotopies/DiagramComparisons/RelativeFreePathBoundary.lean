module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.DiagramComparisons.MappingPathNaturality

/-!
概要：自由 path の両端点と底への合成を保つ相対ホーン充填。
方針：境界からの Hom の積表示で両端点をまとめ、相対 Hom 充填へ渡す。
規約：path の端点零と端点一を別々に指定し、対象の Kan 性は仮定しない。
使われ方：Goerss–Jardine I §7、HTT A.3.3、Sp の塔の標的側の相対比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open SerrePositivity.KST.Spectra
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section

/-- 概要：底の path と両端点を指定して自由 path のホーンを充填できる。
方針：両端点を境界の Hom へ持ち上げ、単射な境界包含の相対ホーン充填を使う。
規約：p の fibration 性と j がホーンであることだけを要求する。
使われ方：mapping path の標的射影の相対比較の fibration 性。 -/
lemma relativeFreePath_boundaryHornLift {Y Z : PointedSimplicialSet.{u}}
    (p : Y ⟶ Z) [Fibration p.right] {T U : SSet.{u}} (j : T ⟶ U) (hj : J j)
    (a : T ⟶ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathSpace Y).right) (b₀ b₁ : U ⟶ Y.right)
    (c : U ⟶ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathSpace Z).right)
    (hc₀ : j ≫ b₀ = a ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoint Y 0).right)
    (hc₁ : j ≫ b₁ = a ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoint Y 1).right)
    (he : a ≫ (PointedObject.basedHomMap _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.freeInterval.{u} p).right = j ≫ c)
    (ha₀ : b₀ ≫ p.right = c ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoint Z 0).right)
    (ha₁ : b₁ ≫ p.right = c ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoint Z 1).right) :
    ∃ l : U ⟶ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathSpace Y).right,
      j ≫ l = a ∧ l ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoint Y 0).right = b₀ ∧
        l ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoint Y 1).right = b₁ ∧
          l ≫ (PointedObject.basedHomMap _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.freeInterval.{u} p).right = c := by
  let eY := _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryEvaluationIso Y
  let eZ := _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryEvaluationIso Z
  let b := prod.lift b₀ b₁ ≫ eY.inv
  have hnEnd : (PointedObject.basedHomMap _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeIntervalBoundary.{u} p).right ≫
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryHomEnd Z).right = (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryHomEnd Y).right ≫ p.right := by
    have h : PointedObject.basedHomMap _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeIntervalBoundary.{u} p ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryHomEnd Z =
        _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryHomEnd Y ≫ p := by
      simp only [_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryHomEnd, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre, Category.assoc]
      change (ihom _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeIntervalBoundary.{u}).map p ≫
        (MonoidalClosed.pre _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryEnd.{u}).app Z ≫
          (unitNatIso (C := PointedSimplicialSet.{u})).inv.app Z = _
      rw [← Category.assoc, (MonoidalClosed.pre _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryEnd.{u}).naturality p,
        Category.assoc, (unitNatIso (C := PointedSimplicialSet.{u})).inv.naturality p,
        ← Category.assoc]
      rfl
    exact congrArg Under.Hom.right h
  have hnStart : (PointedObject.basedHomMap _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeIntervalBoundary.{u} p).right ≫
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryHomStart Z).right = (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryHomStart Y).right ≫ p.right := by
    have h : PointedObject.basedHomMap _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeIntervalBoundary.{u} p ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryHomStart Z =
        _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryHomStart Y ≫ p := by
      simp only [_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryHomStart, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre, Category.assoc]
      change (ihom _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeIntervalBoundary.{u}).map p ≫
        (MonoidalClosed.pre _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryStart.{u}).app Z ≫
          (unitNatIso (C := PointedSimplicialSet.{u})).inv.app Z = _
      rw [← Category.assoc, (MonoidalClosed.pre _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryStart.{u}).naturality p,
        Category.assoc, (unitNatIso (C := PointedSimplicialSet.{u})).inv.naturality p,
        ← Category.assoc]
      rfl
    exact congrArg Under.Hom.right h
  have hb₀ : b ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryHomEnd Y).right = b₀ := by
    rw [← _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryEvaluationIso_fst, ← Category.assoc]
    simp only [b, eY, Category.assoc, Iso.inv_hom_id_assoc, prod.lift_fst]
  have hb₁ : b ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryHomStart Y).right = b₁ := by
    rw [← _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryEvaluationIso_snd, ← Category.assoc]
    simp only [b, eY, Category.assoc, Iso.inv_hom_id_assoc, prod.lift_snd]
  have hrEnd (V : PointedSimplicialSet.{u}) :
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryInclusion.{u} V ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryHomEnd V).right =
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoint V 0).right := by
    simpa only [_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoints, Category.assoc, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryEvaluationIso_fst] using
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoints_fst V
  have hrStart (V : PointedSimplicialSet.{u}) :
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryInclusion.{u} V ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryHomStart V).right =
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoint V 1).right := by
    simpa only [_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoints, Category.assoc, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryEvaluationIso_snd] using
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoints_snd V
  have hc : j ≫ b = a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryInclusion.{u} Y := by
    apply (cancel_mono eY.hom).mp
    apply prod.hom_ext
    · simp only [eY, Category.assoc, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryEvaluationIso_fst, hrEnd]
      rw [hb₀]
      exact hc₀
    · simp only [eY, Category.assoc, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryEvaluationIso_snd, hrStart]
      rw [hb₁]
      exact hc₁
  have ha : b ≫ (PointedObject.basedHomMap _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeIntervalBoundary.{u} p).right =
      c ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryInclusion.{u} Z := by
    apply (cancel_mono eZ.hom).mp
    apply prod.hom_ext
    · simp only [eZ, Category.assoc, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryEvaluationIso_fst, hnEnd, hrEnd]
      rw [← Category.assoc, hb₀]
      exact ha₀
    · simp only [eZ, Category.assoc, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryEvaluationIso_snd, hnStart, hrStart]
      rw [← Category.assoc, hb₁]
      exact ha₁
  obtain ⟨l, hl, hpre, hp⟩ := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.relativePointedHom_hornLift
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryInclusion.{u} p j hj a b c hc he ha
  refine ⟨l, hl, ?_, ?_, hp⟩
  · rw [← hrEnd Y, ← Category.assoc, hpre]
    exact hb₀
  · rw [← hrStart Y, ← Category.assoc, hpre]
    exact hb₁

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
