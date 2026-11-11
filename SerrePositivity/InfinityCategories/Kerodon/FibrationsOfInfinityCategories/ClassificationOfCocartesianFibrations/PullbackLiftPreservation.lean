module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.ComparisonTriangleProjection
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Pullbacks.PullbackComparisonTriangle
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.OverPullbackEdges

/-!
概要：任意の部分底で、指定した同じ始点の lift の保存から全 cocartesian 辺の保存を反映する。
方針：元の比較三角形を部分底へ戻し、固定 fiber 内の可逆な第二辺を写す。
規約：部分底とその上の全空間の quasicategory 性を要求しない。
使われ方：境界上の元の全 Hom の scaffold 制限の指定辺条件。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 部分底で同じ始点と底を持つ cocartesian lift を保てば、全ての指定辺を保つ。 -/
lemma preservesCocartesianPullbackEdges_of_matching_lifts
    {E F B : SSet.{u}} [Quasicategory B] (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p]
    (q : F ⟶ B) [InnerFibration q] (a : Over B) (H : pullback a.hom p ⟶ F)
    (hl : ∀ e : (pullback a.hom p) _⦋1⦌, ∃ h : (pullback a.hom p) _⦋1⦌,
      (pullback a.hom p).δ 1 h = (pullback a.hom p).δ 1 e ∧
      (pullback.fst a.hom p).app (Opposite.op ⦋1⦌) h =
        (pullback.fst a.hom p).app (Opposite.op ⦋1⦌) e ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge (pullback.fst a.hom p) h ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge q (H.app (Opposite.op ⦋1⦌) h)) :
    ∀ e, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge (pullback.fst a.hom p) e →
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge q (H.app (Opposite.op ⦋1⦌) e) := by
  letI : Quasicategory E := quasicategory_of_innerFibration p
  letI : Quasicategory F := quasicategory_of_innerFibration q
  intro e he
  obtain ⟨h, hs, hb, hh, hH⟩ := hl e
  have hs' : E.δ 1 ((pullback.snd a.hom p).app (Opposite.op ⦋1⦌) h) =
      E.δ 1 ((pullback.snd a.hom p).app (Opposite.op ⦋1⦌) e) := by
    rw [← δ_naturality_apply, ← δ_naturality_apply, hs]
  have hp' : p.app (Opposite.op ⦋1⦌) ((pullback.snd a.hom p).app (Opposite.op ⦋1⦌) h) =
      p.app (Opposite.op ⦋1⦌) ((pullback.snd a.hom p).app (Opposite.op ⦋1⦌) e) := by
    have hc (x : (pullback a.hom p) _⦋1⦌) := congrArg
      (fun m ↦ m.app (Opposite.op ⦋1⦌) x) (pullback.condition (f := a.hom) (g := p))
    exact (hc h).symm.trans ((congrArg (a.hom.app (Opposite.op ⦋1⦌)) hb).trans (hc e))
  obtain ⟨t, htp, ht₂, ht₁, hi⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.exists_cocartesianComparisonTriangle_over p
    ((pullback.snd a.hom p).app (Opposite.op ⦋1⦌) e)
    ((pullback.snd a.hom p).app (Opposite.op ⦋1⦌) h)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.isCocartesianEdge_overPullback_iff p a e).mp he)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.isCocartesianEdge_overPullback_iff p a h).mp hh) hs' hp'
  let β := SSet.yonedaEquiv.symm e ≫ pullback.fst a.hom p
  have hβ : β ≫ a.hom = SSet.yonedaEquiv.symm
      (p.app (Opposite.op ⦋1⦌) ((pullback.snd a.hom p).app (Opposite.op ⦋1⦌) e)) := by
    dsimp only [β]
    rw [Category.assoc, pullback.condition, ← Category.assoc,
      SSet.yonedaEquiv_symm_comp, SSet.yonedaEquiv_symm_comp]
  have ht : t ≫ p = stdSimplex.σ 1 ≫ β ≫ a.hom :=
    htp.trans (congrArg (fun m ↦ stdSimplex.σ 1 ≫ m) hβ.symm)
  let T := _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Pullbacks.pullbackComparisonTriangle p a β t ht
  have hb' : SSet.yonedaEquiv.symm h ≫ pullback.fst a.hom p = β := by
    rw [SSet.yonedaEquiv_symm_comp, hb]
    exact (SSet.yonedaEquiv_symm_comp e (pullback.fst a.hom p)).symm
  have hT₂ : stdSimplex.δ 2 ≫ T = SSet.yonedaEquiv.symm h :=
    _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Pullbacks.pullbackComparisonTriangle_face p a β t ht 2 (Or.inr rfl) h hb'
      (ht₂.trans (SSet.yonedaEquiv_symm_comp h (pullback.snd a.hom p)).symm)
  have hT₁ : stdSimplex.δ 1 ≫ T = SSet.yonedaEquiv.symm e :=
    _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Pullbacks.pullbackComparisonTriangle_face p a β t ht 1 (Or.inl rfl) e rfl
      (ht₁.trans (SSet.yonedaEquiv_symm_comp e (pullback.snd a.hom p)).symm)
  have hInv := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isInvertibleEdge_partialPullback_map_of_vertical p a H
    (SSet.yonedaEquiv (stdSimplex.δ 0 ≫ T))
    (β.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
    (by rw [Equiv.symm_apply_apply]; exact _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Pullbacks.pullbackComparisonTriangle_vertical p a β t ht)
    (by rw [← SSet.yonedaEquiv_comp, Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Pullbacks.pullbackComparisonTriangle_snd]; exact hi)
  have hfirst : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge q (SSet.yonedaEquiv (stdSimplex.δ 2 ≫ (T ≫ H))) := by
    rw [← Category.assoc, hT₂, SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
    exact hH
  have hsecond : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge q
      (H.app (Opposite.op ⦋1⦌) (SSet.yonedaEquiv (stdSimplex.δ 0 ≫ T))) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isCocartesianEdge_of_isInvertibleEdge q _ hInv
  have hlong := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isCocartesianEdge_triangle_longEdge (T ≫ H) q hfirst
    (by simpa only [← SSet.yonedaEquiv_comp, Category.assoc] using hsecond)
  rw [← Category.assoc, hT₁, SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] at hlong
  exact hlong

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
