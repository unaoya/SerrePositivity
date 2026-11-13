module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictBarNativeCellApex

/-!
概要：閉零セルの全族評価を通常の閉nerveの包含と照合する。
方針：全射列で同じ頂点を比較し、零次は単位則、高次は零成分を使う。
規約：対象ごとでなく全HA成分の等式で述べる。
使われ方：3b-3 R6の照合C2の証明分割、計算済みapexの比較。
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
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (A : Type u) [CommRing A]

variable {C : Type (u + 1)} [Category.{u} C]

/-- C2の局所計算：一点の閉零セルの引き戻しの同じ斉次成分。 -/
lemma closedVertex_pullback_hom (M : ModuleCategory A PUnit.{1}) {n : ℕ}
    (α : Fin (n + 1) →o Fin 1) (T : Finset (Fin (n + 1)))
    (a b : Fin (n + 1)) (k : ℤ) (hT : 2 ≤ T.card)
    (ha : a = T.min' (Index.nonempty hT)) (hb : b = T.max' (Index.nonempty hT))
    (hk : k = 2 - (T.card : ℤ)) :
    ((closedNerveSimplex (A := A) (D := RightModule A PUnit.{1})
      ((Functor.const (Fin 1)).obj M)).pullback α).hom T a b k hT ha hb hk =
        closedNerveHom (𝟙 M) k := by
  have h := closedNerveSimplex_pullback (A := A) (D := RightModule A PUnit.{1})
    ((Functor.const (Fin 1)).obj M) α
  have hh := SimplexData.data_hom_heq_of_eq (congrArg Simplex.toSimplexData h)
    T a b k hT ha hb hk
  change HEq (closedNerveHom (𝟙 M) k) _ at hh
  exact (eq_of_heq hh).symm

/-- C2の証明分割：閉零セルの全評価は元の通常nerveの同じ包含。 -/
lemma strictClosedVertexEvaluation (G : C ⥤ ModuleCategory A PUnit.{1}) :
    lift (𝟙 (nerve C)) (SSet.stdSimplex.isTerminalObj₀.from (nerve C)) ≫
      strictSimplexFunctorEvaluation A (RightModule A PUnit.{1})
        (G ⋙ strictBarClosedVertexFunctor A) =
      nerveMap G ≫ closedNerveInclusion A (RightModule A PUnit.{1}) := by
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
    change compose A (closedHomEquiv A (RightModule A PUnit.{1}) _ _
      (G.map (d.map (homOfLE (show a ≤ b by
        rw [ha, hb]
        exact (T.isLeast_min' _).2 (T.max'_mem _)))))).val
      (((closedNerveSimplex (A := A) (D := RightModule A PUnit.{1})
        ((Functor.const (Fin 1)).obj (G.obj (d.obj a)))).pullback _).hom
          T a b k hT ha hb hk) (add_zero k) = _
    rw [closedVertex_pullback_hom]
    change compose A _ (closedNerveHom (𝟙 _) k) (add_zero k) =
      closedNerveHom (G.map (d.map (homOfLE (show a ≤ b by
        rw [ha, hb]
        exact (T.isLeast_min' _).2 (T.max'_mem _))))) k
    by_cases hk0 : k = 0
    · subst hk0
      simp only [closedNerveHom_zero, closedHom_id]
      exact compose_unit (D := RightModule A PUnit.{1}) A _
    · rw [closedNerveHom_of_ne _ _ hk0, closedNerveHom_of_ne _ _ hk0, compose_zero]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
