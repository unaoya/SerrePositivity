module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGLastHornGeneralRefinementFiller
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGLastHornGeneralFiniteRefinement

/-! # 任意次元の実最後外ホーン有限族の一つの分母後の同時実充填

概要：共通化した全原始元を、その各次数の実細分ホーンの充填へ同時に渡す。
方針：各型付き二未知解の延長を使い、全零面の保存を記録する。
規約：空族を含み、次元は異なってよい。使われ方：有限非退化単体上の帰納。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable {P : Set D} {a : D} {m : ℕ} {d : Fin m → ℕ}
variable {σ : ∀ i, (Λ[d i + 2, Fin.last (d i + 2)] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D}
variable (T : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGGeneralLastHornFiniteRefinement P a σ)

/-- 各次元の同じ細分ホーンを延長する、実際の全単体写像。 -/
def DGGeneralLastHornFiniteRefinement.filler (i : Fin m) : Δ[d i + 2] ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D :=
  (T.residuals i).solution.extension

/-- 全指定面を同時に保つ、各実ホーン全体の延長式。 -/
lemma DGGeneralLastHornFiniteRefinement.filler_fac (i : Fin m) :
    (horn (d i + 2) (Fin.last (d i + 2))).ι ≫ T.filler i =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornSourceRefinement (σ i) (T.residuals i).q (T.residuals i).s :=
  (T.residuals i).solution.fac

/-- 全実充填の零面は、それぞれ元の同じ指定零面である。 -/
lemma DGGeneralLastHornFiniteRefinement.filler_face0 (i : Fin m) :
    SSet.stdSimplex.δ (0 : Fin (d i + 3)) ≫ T.filler i =
      horn.ι (Fin.last (d i + 2)) 0 (by simp) ≫ σ i :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornSourceRefinement_filler_face0 (T.residuals i) (T.filler i) (T.filler_fac i)

/-- 共通始対象と実最後分母を持つ有限族は、一つの追加実分母後に全て実充填できる。 -/
theorem dgGeneralLastHornFinite_exists_sourceRefinement_fillers [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]
    (P : Set D) (a : D) {m : ℕ} {d : Fin m → ℕ}
    (σ : ∀ i, (Λ[d i + 2, Fin.last (d i + 2)] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)
    (hsource : ∀ i, (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData (σ i)).obj 0 = a)
    (hW : ∀ i, (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornFinalClosed (σ i))).edge ∈
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P) :
    ∃ T : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGGeneralLastHornFiniteRefinement P a σ, ∀ i, ∃ F : Δ[d i + 2] ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D,
      (horn (d i + 2) (Fin.last (d i + 2))).ι ≫ F =
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornSourceRefinement (σ i) (T.residuals i).q (T.residuals i).s ∧
      SSet.stdSimplex.δ (0 : Fin (d i + 3)) ≫ F =
        horn.ι (Fin.last (d i + 2)) 0 (by simp) ≫ σ i := by
  obtain ⟨T⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornFiniteRefinement_nonempty P a σ hsource hW
  exact ⟨T, fun i => ⟨T.filler i, T.filler_fac i, T.filler_face0 i⟩⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories
