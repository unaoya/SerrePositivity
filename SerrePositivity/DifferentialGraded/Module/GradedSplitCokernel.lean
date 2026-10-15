module
public import SerrePositivity.DifferentialGraded.Module.GradedSplit

/-! # 次数付き分裂拡大の商の普遍性

各評価のcokernelを全dg自然な加群のcokernelへ接続する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable {M N P T : ModuleCategory A D} {f : M ⟶ N} {g : N ⟶ P}

/-- 各評価複体のcokernelからの延長。 -/
def moduleGradedSplitDescFamily (s : ModuleGradedSplit A D f g) (q : N ⟶ T)
    (h : f ≫ q = 0) (x : Dᵒᵖ) :
    (moduleEvaluation A D x.unop).obj P ⟶ (moduleEvaluation A D x.unop).obj T :=
  (s.evaluationCokernel x.unop).desc (CokernelCofork.ofπ
    ((moduleEvaluation A D x.unop).map q) (by
      rw [← CategoryTheory.Functor.map_comp, h, CategoryTheory.Functor.map_zero]))

lemma moduleGradedSplitDescFamily_fac (s : ModuleGradedSplit A D f g) (q : N ⟶ T)
    (h : f ≫ q = 0) (x : Dᵒᵖ) :
    (moduleEvaluation A D x.unop).map g ≫ moduleGradedSplitDescFamily A D s q h x =
      (moduleEvaluation A D x.unop).map q :=
  Cofork.IsColimit.π_desc (s.evaluationCokernel x.unop)

lemma moduleGradedSplitDescFamily_naturality (s : ModuleGradedSplit A D f g) (q : N ⟶ T)
    (h : f ≫ q = 0) (x y : Dᵒᵖ) :
    (ForgetEnrichment.to (Complex A) P).map x y ≫
      homPostcompose ((ForgetEnrichment.to (Complex A) P).obj x)
        (moduleGradedSplitDescFamily A D s q h y) =
    (ForgetEnrichment.to (Complex A) T).map x y ≫
      homPrecompose (moduleGradedSplitDescFamily A D s q h x)
        ((ForgetEnrichment.to (Complex A) T).obj y) := by
  apply closedFamily_of_action A (moduleGradedSplitDescFamily A D s q h)
  intro x y p i j hij a v
  obtain ⟨w, hw⟩ := (ModuleCat.epi_iff_surjective _).1 (s.degreewiseEpi x.unop i) v
  have hg := closedFamily_action A
    (closedTransApp A (moduleClosedHomEquiv A D N P g))
    (closedTransApp_naturality A (moduleClosedHomEquiv A D N P g)) x y p i j hij a w
  have hq := closedFamily_action A
    (closedTransApp A (moduleClosedHomEquiv A D N T q))
    (closedTransApp_naturality A (moduleClosedHomEquiv A D N T q)) x y p i j hij a w
  have hx := congrArg (fun b => b.f i w) (moduleGradedSplitDescFamily_fac A D s q h x)
  have hy := congrArg (fun b => b.f j
    (moduleAction A (ForgetEnrichment.to (Complex A) N) a w hij))
    (moduleGradedSplitDescFamily_fac A D s q h y)
  change (moduleGradedSplitDescFamily A D s q h x).f i
    (((moduleEvaluation A D x.unop).map g).f i w) =
      ((moduleEvaluation A D x.unop).map q).f i w at hx
  change (moduleGradedSplitDescFamily A D s q h y).f j
    (((moduleEvaluation A D y.unop).map g).f j
      (moduleAction A (ForgetEnrichment.to (Complex A) N) a w hij)) =
    ((moduleEvaluation A D y.unop).map q).f j
      (moduleAction A (ForgetEnrichment.to (Complex A) N) a w hij) at hy
  rw [← hw]
  exact (congrArg ((moduleGradedSplitDescFamily A D s q h y).f j) hg.symm).trans
    (hy.trans (hq.trans (congrArg (fun z =>
      moduleAction A (ForgetEnrichment.to (Complex A) T) a z hij) hx.symm)))

def moduleGradedSplitDesc (s : ModuleGradedSplit A D f g) (q : N ⟶ T) (h : f ≫ q = 0) :
    P ⟶ T :=
  moduleMorphismMk A D (M := ForgetEnrichment.to (Complex A) P)
    (N := ForgetEnrichment.to (Complex A) T) (moduleGradedSplitDescFamily A D s q h)
    (moduleGradedSplitDescFamily_naturality A D s q h)

@[reassoc] lemma moduleGradedSplitDesc_fac (s : ModuleGradedSplit A D f g)
    (q : N ⟶ T) (h : f ≫ q = 0) : g ≫ moduleGradedSplitDesc A D s q h = q := by
  apply moduleMorphism_ext
  intro x
  rw [CategoryTheory.Functor.map_comp]
  unfold moduleGradedSplitDesc
  rw [moduleMorphismMk_eval]
  exact moduleGradedSplitDescFamily_fac A D s q h (op x)

/-- 次数付き分裂拡大の第三対象は主dg加群圏での真のcokernel。 -/
def moduleGradedSplitCokernel (s : ModuleGradedSplit A D f g) :
    IsColimit (CokernelCofork.ofπ g s.inclusion_projection) :=
  CokernelCofork.IsColimit.ofπ g s.inclusion_projection
    (fun q h => moduleGradedSplitDesc A D s q h)
    (fun q h => moduleGradedSplitDesc_fac A D s q h)
    (by
      intro T q h b hb
      let : Epi g := s.epi
      apply (cancel_epi g).1
      exact hb.trans (moduleGradedSplitDesc_fac A D s q h).symm)

end SerrePositivity.DifferentialGraded
