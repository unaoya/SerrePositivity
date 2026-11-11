module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.TransportedShiftBlockHomology
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentFirstClosed

/-!
概要：元の coherent bar の正の番号の面ブロックのホモロジー係数。
方針：実符号つきブロックを、同じ始点加群の等号射のホモロジーへ送る。
規約：元の面の端点輸送を保持する。
使われ方：実一次微分と非退化 bar の面射の一致。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
open CategoryTheory Limits DifferentialGraded SSet
open HomologicalComplex CochainComplex HomComplex
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (G : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))

def dgCoherentBarSignedFaceCochain {n : ℕ} (s : I _⦋n + 1⦌) (i : Fin (n + 1)) (x : D) :
    Cochain ((moduleEvaluation R D x).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D G ⟨n + 1, s⟩))
      ((moduleEvaluation R D x).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D G (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFace s i.succ))) 1 :=
  ((n : ℤ) + 1).negOnePow • (_root_.SerrePositivity.DifferentialGraded.moduleHomπ R D
    (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D G ⟨n + 1, s⟩))
    (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D G (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFace s i.succ))) x).f 1
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFaceBlock R D G s i)

lemma dgCoherentBarSignedFaceCochain_closed {n : ℕ} (s : I _⦋n + 1⦌)
    (i : Fin (n + 1)) (x : D) :
    δ 1 2 (dgCoherentBarSignedFaceCochain R D G s i x) = 0 := by
  simpa only [dgCoherentBarSignedFaceCochain, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgBarTransportSignedShiftCochain,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFaceBlock, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFace, Nat.cast_add, Nat.cast_one] using!
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgBarTransportSignedShiftCochain_closed R D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D G ⟨n + 1, s⟩)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D G ⟨n + 1, s⟩)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D G (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFace s i.succ))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource_face_succ R D G s i).symm
      (unitElement R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D G ⟨n + 1, s⟩)).val
      (unitElement R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D G ⟨n + 1, s⟩)).property (n : ℤ) x

lemma dgCoherentBarSignedFaceHomology {n : ℕ} (s : I _⦋n + 1⦌)
    (i : Fin (n + 1)) (x : D) (q : ℤ) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgDegreeOneHomologyMap R (dgCoherentBarSignedFaceCochain R D G s i x)
      (dgCoherentBarSignedFaceCochain_closed R D G s i x) q ≫
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgComplexShiftHomologyIso R
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D G (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFace s i.succ)).obj (Opposite.op x))
        (n : ℤ) (q + 1) (q + ((n : ℤ) + 1)) (by omega)).hom =
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgComplexShiftHomologyIso R
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D G ⟨n + 1, s⟩).obj (Opposite.op x))
      ((n : ℤ) + 1) q (q + ((n : ℤ) + 1)) (by omega)).hom ≫
      HomologicalComplex.homologyMap ((_root_.SerrePositivity.DifferentialGraded.moduleEvaluation R D x).map
        (eqToHom (congrArg (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R))
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource_face_succ R D G s i).symm))) (q + ((n : ℤ) + 1)) := by
  have h := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgBarTransportSignedShiftHomology R D
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D G ⟨n + 1, s⟩) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D G ⟨n + 1, s⟩)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D G (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFace s i.succ))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource_face_succ R D G s i).symm
    (unitElement R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D G ⟨n + 1, s⟩)).val
    (unitElement R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D G ⟨n + 1, s⟩)).property (n : ℤ) q x
  rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgBarModuleMorphismOfCycle_unit, Category.id_comp] at h
  simpa only [dgCoherentBarSignedFaceCochain, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgBarTransportSignedShiftCochain,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFaceBlock, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFace, Nat.cast_add, Nat.cast_one] using! h

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
