module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.CubeEvaluationChainNaturality
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.DoldKanClosedPrecomposition
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictSimplexMap
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.CoherentHomCoordinates

/-!
概要：同じcoherent単体の全豊穣Homに可換する閉零射を、全HA成分の厳密写像へ移す。
方針：立方体評価の係数自然性を各有限内部集合へ適用する。
規約：IS-W2 D01の既存coherent比較の自然性則。高次成分を落とさない。
使われ方：HA 1.3.1.16、既存StrictCoherentFamilyによる全錐族の構成。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
open CategoryTheory
open SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open scoped Simplicial
variable {R : Type u} [CommRing R] {D : Type v} [DGCategory R D]

/-- 同じ立方体の全豊穣Homでの可換式は、その符号付き評価にも成り立つ。 -/
theorem cubeEvaluation_closed_naturality {T : Type u} {m : ℕ} (e : Fin m ≃ T)
    {x y x' y' : D}
    (f : ForgetEnrichment.of (Complex R) x ⟶ ForgetEnrichment.of (Complex R) x')
    (g : ForgetEnrichment.of (Complex R) y ⟶ ForgetEnrichment.of (Complex R) y')
    (φ : SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cube T ⟶
      standardHomSpace (R := R) x y)
    (ψ : SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cube T ⟶
      standardHomSpace (R := R) x' y')
    (h : φ ≫ eHomWhiskerLeft SSet (ForgetEnrichment.of (Complex R) x) g =
      ψ ≫ eHomWhiskerRight SSet f (ForgetEnrichment.of (Complex R) y')) :
    compose R (closedHomEquiv R D _ _ g).val (cubeEvaluation e φ) (add_zero (-(m : ℤ))) =
      compose R (cubeEvaluation e ψ) (closedHomEquiv R D _ _ f).val
        (zero_add (-(m : ℤ))) := by
  have hc := congrArg (cubeEvaluation e) h
  rw [← standardChainMap_closedPostcomposition, ← standardChainMap_closedPrecomposition,
    cubeEvaluation_chainMap, cubeEvaluation_chainMap] at hc
  erw [dgClosedPostcomposition_f, Gluing.dgGluingHomWhiskerRight_f] at hc
  exact hc

/-- 同じ全coherent Homに可換する閉零成分は、同じ比較の全HA成分に可換する。 -/
def coherentComparisonStrictMap {n : ℕ}
    (s t : (doldKanCoherentNerve (R := R) (D := D)) _⦋n⦌)
    (f : ∀ i, s.obj i ⟶ t.obj i)
    (hf : ∀ i j, s.map i j ≫ eHomWhiskerLeft SSet (s.obj i) (f j) =
      t.map i j ≫ eHomWhiskerRight SSet (f i) (t.obj j)) :
    StrictSimplexMap R D (coherentSimplexData s) (coherentSimplexData t) where
  app i := closedHomEquiv R D _ _ (f (.mk (ULift.up i)))
  naturality I a b k hI ha hb hk := by
    have hamin : IsLeast (I : Set _) a := by rw [ha]; exact I.isLeast_min' _
    have hbmax : IsGreatest (I : Set _) b := by rw [hb]; exact I.isGreatest_max' _
    have hab : a < b := by
      have h := I.min'_lt_max'_of_card hI
      simpa only [← ha, ← hb] using h
    have hc := coherentVertexInterior_card.{u} hamin hbmax hab
    have hdeg : k = -((coherentVertexInterior.{u} I a b).card : ℤ) := by omega
    rw [coherentSimplexData_hom_eq_componentAt s I a b k hI ha hb hk hab hdeg,
      coherentSimplexData_hom_eq_componentAt t I a b k hI ha hb hk hab hdeg]
    cases hdeg
    apply cubeEvaluation_closed_naturality
    have h := congrArg (fun q => pathCubeMap (show ULift.up a < ULift.up b from hab)
      (coherentVertexInterior.{u} I a b) ≫ q) (hf (.mk (ULift.up a)) (.mk (ULift.up b)))
    simp only [Category.assoc] at h
    exact h

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
