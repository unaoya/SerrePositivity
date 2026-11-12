module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.SignedShiftBlockHomology
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.HomTargetTransportPostcomposition

/-!
概要：標的の等号輸送つき符号つき一次 shift ブロックのホモロジー比較。
方針：等号消去で同じ実ブロックへ戻し、実等号射との後合成を保持する。
規約：面の始点の等号と実加群射を省略しない。
使われ方：正の番号の面ブロックのホモロジー係数。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
open CategoryTheory Limits DifferentialGraded HomologicalComplex CochainComplex HomComplex
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  (M N N' : RightModule R D) (h : N = N')
  (f : (moduleHom R D M N).X 0) (hf : (moduleHom R D M N).d 0 1 f = 0)

def dgBarTransportSignedShiftCochain (n : ℤ) (x : D) :
    Cochain ((M.obj (Opposite.op x))⟦n + 1⟧) ((N'.obj (Opposite.op x))⟦n⟧) 1 :=
  (n + 1).negOnePow •
    (moduleHomπ R D (shiftModule (n + 1) M) (shiftModule n N') x).f 1
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleHomTargetTransport R D (shiftModule (n + 1) M) (shiftModule n N)
        (shiftModule n N') (congrArg (shiftModule n) h) 1
          (moduleHomShiftBlock R D (n + 1) n f (by omega))).val

include hf in
lemma dgBarTransportSignedShiftCochain_closed (n : ℤ) (x : D) :
    δ 1 2 (dgBarTransportSignedShiftCochain R D M N N' h f n x) = 0 := by
  cases h
  exact _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgBarSignedShiftCochain_closed R D
    (M := ForgetEnrichment.of (Complex R) M) (N := ForgetEnrichment.of (Complex R) N) f hf n x

lemma dgBarTransportSignedShiftHomology (n q : ℤ) (x : D) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgDegreeOneHomologyMap R (dgBarTransportSignedShiftCochain R D M N N' h f n x)
      (dgBarTransportSignedShiftCochain_closed R D M N N' h f hf n x) q ≫
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgComplexShiftHomologyIso R (N'.obj (Opposite.op x)) n
        (q + 1) (q + (n + 1)) (by omega)).hom =
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgComplexShiftHomologyIso R (M.obj (Opposite.op x)) (n + 1)
      q (q + (n + 1)) (by omega)).hom ≫
      HomologicalComplex.homologyMap ((moduleEvaluation R D x).map
        (moduleMorphismOfCycle R D (M := ForgetEnrichment.of (Complex R) M)
          (N := ForgetEnrichment.of (Complex R) N) f hf ≫
            eqToHom (congrArg (ForgetEnrichment.of (Complex R)) h))) (q + (n + 1)) := by
  cases h
  simpa only [eqToHom_refl, Category.comp_id] using! _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgBarSignedShiftHomology R D
    (M := ForgetEnrichment.of (Complex R) M) (N := ForgetEnrichment.of (Complex R) N) f hf n q x

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
