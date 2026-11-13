module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictCoherentFamilyEvaluation
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.SmallStrictBarDiagram

/-!
概要：元の strict 加群図式と自然変換の全族を、同じ HA 単体の厳密な族へ接続する。
方針：閉零圏の実自然変換を全 HA 写像へ移し、恒等・合成・引き戻しを照合する。
規約：元の全射列・同じ閉零成分・高次零成分を保つ。
使われ方：3b-3 R6、native 余錐族の下方図式の厳密な同定。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison

/-- 表示の等式と同じ全頂点成分に沿う、厳密 HA 写像の異種外延性。 -/
lemma StrictSimplexMap.hext {A : Type u} [CommRing A] {E : Type v} [DGCategory A E]
    {n : ℕ} {s t s' t' : SimplexData A E n}
    {η : StrictSimplexMap A E s t} {θ : StrictSimplexMap A E s' t'}
    (hs : s = s') (ht : t = t') (ha : ∀ i, HEq (η.app i) (θ.app i)) : HEq η θ := by
  cases hs
  cases ht
  exact heq_of_eq (StrictSimplexMap.ext (fun i => eq_of_heq (ha i)))

/-- 元の閉零自然変換を、同じ全 HA 成分に可換する写像として読む。 -/
def strictClosedSimplexMap {A : Type u} [CommRing A] {E : Type v} [DGCategory A E]
    {n : ℕ} {F G : Fin (n + 1) ⥤ ClosedCategory A E} (η : F ⟶ G) :
    StrictSimplexMap A E (closedNerveData F) (closedNerveData G) where
  app i := closedHomEquiv A E (F.obj i) (G.obj i) (η.app i)
  naturality I a b k hI ha hb hk := by
    by_cases hk0 : k = 0
    · subst hk0
      simp only [closedNerveData, closedNerveHom_zero]
      have hab : a ≤ b := by
        rw [ha, hb]
        exact (I.isLeast_min' _).2 (I.max'_mem _)
      rw [← closedHom_comp (A := A) (D := E) (F.map (homOfLE hab)) (η.app b),
        ← closedHom_comp (A := A) (D := E) (η.app a) (G.map (homOfLE hab)), η.naturality]
    · simp only [closedNerveData, closedNerveHom_of_ne _ _ hk0, compose_zero, zero_compose]

variable (A : Type u) [CommRing A] (J : Type) [SmallCategory J]
  {C : Type (u + 1)} [Category.{u} C]

/-- 元の strict 加群図式の通常関手から作る、同じ全 HA 成分の厳密な族。 -/
def strictModuleCoherentFamily (T : C ⥤ (J ⥤ ModuleCategory A PUnit.{1})) :
    StrictCoherentFamily A (RightModule A PUnit.{1})
      ((SSet.uliftFunctor.{u, 0}).obj (nerve J)) C where
  obj c := smallStrictBarDiagram A (T.obj c)
  map {c d} f {n} s := strictClosedSimplexMap (Functor.whiskerLeft s.down (T.map f))
  map_id c {n} s := by
    apply StrictSimplexMap.ext
    intro i
    change closedHomEquiv A (RightModule A PUnit.{1}) _ _
      ((T.map (𝟙 c)).app (s.down.obj i)) = _
    rw [T.map_id]
    exact closedHom_id _
  map_comp {c d e} f g {n} s := by
    apply StrictSimplexMap.ext
    intro i
    apply Subtype.ext
    change (closedHomEquiv A (RightModule A PUnit.{1}) _ _
        ((T.map (f ≫ g)).app (s.down.obj i))).val =
      compose A (closedHomEquiv A (RightModule A PUnit.{1}) _ _
        ((T.map g).app (s.down.obj i))).val
        (closedHomEquiv A (RightModule A PUnit.{1}) _ _
          ((T.map f).app (s.down.obj i))).val (zero_add 0)
    rw [T.map_comp, NatTrans.comp_app, closedHom_comp]
  map_pullback {c d} f {m n} α s := by
    apply StrictSimplexMap.hext
    · exact congrArg Simplex.toSimplexData
        (coherentDiagramSimplex_map (smallStrictBarDiagram A (T.obj c)) α s)
    · exact congrArg Simplex.toSimplexData
        (coherentDiagramSimplex_map (smallStrictBarDiagram A (T.obj d)) α s)
    · intro i
      rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
