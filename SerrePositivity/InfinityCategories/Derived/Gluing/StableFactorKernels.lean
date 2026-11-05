module
public import SerrePositivity.InfinityCategories.Derived.Gluing.StableObjects
public import SerrePositivity.InfinityCategories.Derived.Gluing.FactorZeroTransport
public import SerrePositivity.InfinityCategories.Derived.Gluing.FactorSubcategories
public import SerrePositivity.InfinityCategories.Derived.ContractingElementCriterion
/-!
概要：既存の二つの実 dg 因子は、安定 gluing の元射影の零対象核である。
方針：H⁰ の零性を同じ恒等射の収縮元へ移し、実 nerve の零性と宇宙輸送を使う。
規約：因子の対象条件と射影を変更しない。
使われ方：順序 ⟨D,C⟩ の半直交分解と K-8b の射影核の照合に用いる。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
lemma dgGluingFactorIsZero_iff_isZeroVertex (x : C) :
    dgGluingFactorIsZero R C x ↔ IsZeroVertex (X := dgNerve R C) (Simplex.vertex x) := by
  rw [dgGluingFactorIsZero_iff_boundary, dgNerve_isZeroVertex_iff_contractingElement]
  change Nonempty (_root_.Homotopy (eId (Complex R) x) 0) ↔ _
  simpa [unitElement, cycleFromUnit] using
    (unit_homotopy_boundary (homObject R C x x) (eId (Complex R) x) 0)
variable [Small.{u} C] (D : Type w) [DGCategory R D]
  (M : Bimodule R C D)
lemma dgGluingCFactor_iff_stableRightKernel (X : DGGluingObject R C D M) :
    dgGluingFactorIsZero R D X.right ↔
      IsZeroVertex ((dgGluingUniverseRightNerve R C D M).app (Opposite.op ⦋0⦌)
        (ULift.up (Simplex.vertex X))) := by
  rw [dgGluingFactorIsZero_iff_isZeroVertex]
  dsimp only [dgGluingUniverseRightNerve]
  rw [dgGluingUniverseNerveMap_vertex]
  change _ ↔ IsZeroVertex (X := (SSet.uliftFunctor.{max (u + 1) v w,max u w}).obj
    (dgNerve R D)) (ULift.up (Simplex.vertex X.right))
  exact isZeroVertex_iff_ulift _
lemma dgGluingDFactor_iff_stableLeftKernel (X : DGGluingObject R C D M) :
    dgGluingFactorIsZero R C X.left ↔
      IsZeroVertex ((dgGluingUniverseLeftNerve R C D M).app (Opposite.op ⦋0⦌)
        (ULift.up (Simplex.vertex X))) := by
  rw [dgGluingFactorIsZero_iff_isZeroVertex]
  dsimp only [dgGluingUniverseLeftNerve]
  rw [dgGluingUniverseNerveMap_vertex]
  change _ ↔ IsZeroVertex (X := (SSet.uliftFunctor.{max (u + 1) v w,max u v}).obj
    (dgNerve R C)) (ULift.up (Simplex.vertex X.left))
  exact isZeroVertex_iff_ulift _
end SerrePositivity.InfinityCategories
