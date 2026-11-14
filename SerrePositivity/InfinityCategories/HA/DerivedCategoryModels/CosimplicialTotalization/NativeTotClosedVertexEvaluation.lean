module

public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NativeTotWeightedApexFamily

/-!
概要：複体の閉零セルの全族評価を通常の閉nerveの包含と照合する。
方針：全射列で同じ頂点を比較し、零次は単位則、高次は零成分を使う。
規約：対象ごとでなく全HA成分の等式で述べる。
使われ方：IS-W2 D02、同じTot頂点関手の全パラメータ照合。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet CartesianMonoidalCategory MonoidalCategory SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
open SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization
open SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
variable (A : Type u) [CommRing A]

variable {C : Type (u + 1)} [Category.{u} C]

/-- C2の局所計算：一点の閉零セルの引き戻しの同じ斉次成分。 -/
lemma nativeTotClosedVertex_pullback_hom (M : ClosedCategory A (Complex A)) {n : ℕ}
    (α : Fin (n + 1) →o Fin 1) (T : Finset (Fin (n + 1)))
    (a b : Fin (n + 1)) (k : ℤ) (hT : 2 ≤ T.card)
    (ha : a = T.min' (Index.nonempty hT)) (hb : b = T.max' (Index.nonempty hT))
    (hk : k = 2 - (T.card : ℤ)) :
    ((closedNerveSimplex (A := A) (D := Complex A)
      ((Functor.const (Fin 1)).obj M)).pullback α).hom T a b k hT ha hb hk =
        closedNerveHom (𝟙 M) k := by
  have h := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.closedNerveSimplex_pullback (A := A) (D := Complex A)
    ((Functor.const (Fin 1)).obj M) α
  have hh := SimplexData.data_hom_heq_of_eq (congrArg Simplex.toSimplexData h)
    T a b k hT ha hb hk
  change HEq (closedNerveHom (𝟙 M) k) _ at hh
  exact (eq_of_heq hh).symm

/-- C2の証明分割：閉零セルの全評価は元の通常nerveの同じ包含。 -/
lemma nativeTotClosedVertexEvaluation (G : C ⥤ ClosedCategory A (Complex A)) :
    lift (𝟙 (nerve C)) (SSet.stdSimplex.isTerminalObj₀.from (nerve C)) ≫
      strictSimplexFunctorEvaluation A (Complex A)
        (G ⋙ nativeTotClosedVertexFunctor A) =
      nerveMap G ≫ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.closedNerveInclusion A (Complex A) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro d
  change (Fin (n + 1) ⥤ C) at d
  apply Simplex.ext
  apply SimplexData.ext
  · rfl
  · apply heq_of_eq
    funext T a b k hT ha hb hk
    change compose A (closedHomEquiv A (Complex A) _ _
      (G.map (d.map (homOfLE (show a ≤ b by
        rw [ha, hb]
        exact (T.isLeast_min' _).2 (T.max'_mem _)))))).val
      (((closedNerveSimplex (A := A) (D := Complex A)
        ((Functor.const (Fin 1)).obj (G.obj (d.obj a)))).pullback _).hom
          T a b k hT ha hb hk) (add_zero k) = _
    rw [nativeTotClosedVertex_pullback_hom]
    change compose A _ (closedNerveHom (𝟙 _) k) (add_zero k) =
      closedNerveHom (G.map (d.map (homOfLE (show a ≤ b by
        rw [ha, hb]
        exact (T.isLeast_min' _).2 (T.max'_mem _))))) k
    by_cases hk0 : k = 0
    · subst hk0
      simp only [closedNerveHom_zero, closedHom_id]
      exact compose_unit (D := Complex A) A _
    · rw [closedNerveHom_of_ne _ _ hk0, closedNerveHom_of_ne _ _ hk0, compose_zero]

/-- 同じ閉零頂点の全族は、第一射影と通常閉nerve包含の合成。 -/
theorem nativeTotClosedVertexEvaluation_full (G : C ⥤ ClosedCategory A (Complex A)) :
    strictSimplexFunctorEvaluation A (Complex A) (G ⋙ nativeTotClosedVertexFunctor A) =
      fst (nerve C) (Δ[0] : SSet.{u+1}) ≫ nerveMap G ≫
        _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.closedNerveInclusion A (Complex A) := by
  have h := nativeTotClosedVertexEvaluation A G
  have hi : lift (𝟙 (nerve C)) (SSet.stdSimplex.isTerminalObj₀.from (nerve C)) =
      inv (fst (nerve C) (Δ[0] : SSet.{u+1})) := by
    apply (cancel_mono (fst (nerve C) (Δ[0] : SSet.{u+1}))).1
    rw [lift_fst, IsIso.inv_hom_id]
  rw [hi] at h
  apply (cancel_epi (inv (fst (nerve C) (Δ[0] : SSet.{u+1})))).1
  rw [← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
  exact h

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
