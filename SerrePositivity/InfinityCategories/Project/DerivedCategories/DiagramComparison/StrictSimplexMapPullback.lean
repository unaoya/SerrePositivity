module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictSimplexMap

/-!
概要：全高次成分に厳密に可換する写像を、面・退化に沿って引き戻す。
方針：単射・潰れた辺・零の高次成分の三分岐で、元の HA 引き戻しを使う。
規約：潰れた辺は元の dg 単位のまま保持する。
使われ方：3b-3 R6、指定余錐の全族の面・退化との整合性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
namespace StrictSimplexMap
variable {A : Type u} [CommRing A] {E : Type v} [DGCategory A E]
  {m n : ℕ} {s t r : SimplexData A E n}

/-- 厳密な HA 写像の引き戻し。元の頂点成分を同じ単調写像で評価する。 -/
def pullback (η : StrictSimplexMap A E s t) (α : Fin (m + 1) →o Fin (n + 1)) :
    StrictSimplexMap A E (s.pullback α) (t.pullback α) where
  app i := η.app (α i)
  naturality I a b k hI ha hb hk := by
    change compose A (η.app (α b)).val ((s.pullback α).hom I a b k hI ha hb hk)
        (add_zero k) =
      compose A ((t.pullback α).hom I a b k hI ha hb hk) (η.app (α a)).val (zero_add k)
    by_cases hi : Set.InjOn α (I : Set (Fin (m + 1)))
    · rw [Reindex.pullback_hom_of_inj _ _ _ _ _ _ _ _ _ _ hi,
        Reindex.pullback_hom_of_inj _ _ _ _ _ _ _ _ _ _ hi]
      exact η.naturality _ _ _ _ _ _ _ _
    · by_cases hc : I.card = 2
      · have hk0 : k = 0 := by omega
        subst hk0
        have hab : α a = α b := Index.collapse_two hi hc
          (by rw [ha]; exact I.isLeast_min' _) (by rw [hb]; exact I.isGreatest_max' _)
        have hl := compose_unit_of_heq (η.app (α b)).val
          ((s.pullback α).hom I a b 0 hI ha hb hk) (add_zero 0)
          (congrArg s.obj hab) rfl
          (s.pullback_hom_of_collapsed_pair α I a b 0 hI ha hb hk hi hc)
        have hr := unit_compose_of_heq
          ((t.pullback α).hom I a b 0 hI ha hb hk) (η.app (α a)).val (zero_add 0)
          (congrArg t.obj hab) rfl
          (t.pullback_hom_of_collapsed_pair α I a b 0 hI ha hb hk hi hc)
        have he : HEq (η.app (α a)).val (η.app (α b)).val := by rw [hab]
        exact eq_of_heq (hl.trans (he.symm.trans hr.symm))
      · rw [Reindex.pullback_hom_of_not_inj _ _ _ _ _ _ _ _ _ _ hi hc,
          Reindex.pullback_hom_of_not_inj _ _ _ _ _ _ _ _ _ _ hi hc]
        rw [compose_zero, zero_compose]

/-- 同じ引き戻しは元の厳密恒等成分を保つ。 -/
lemma pullback_id (s : SimplexData A E n) (α : Fin (m + 1) →o Fin (n + 1)) :
    (id s).pullback α = id (s.pullback α) := by
  apply ext
  intro i
  rfl

/-- 同じ引き戻しは元の厳密合成成分を保つ。 -/
lemma pullback_comp (η : StrictSimplexMap A E s t) (θ : StrictSimplexMap A E t r)
    (α : Fin (m + 1) →o Fin (n + 1)) :
    (η.comp θ).pullback α = (η.pullback α).comp (θ.pullback α) := by
  apply ext
  intro i
  rfl

end StrictSimplexMap
end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
