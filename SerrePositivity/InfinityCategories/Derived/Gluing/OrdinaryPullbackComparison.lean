module
public import SerrePositivity.InfinityCategories.Derived.Gluing.OrdinaryPullbackObjects
public import SerrePositivity.InfinityCategories.F2.CatInfinity.LaxPullbackEquivalenceProjections
/-!
概要：元 dg gluing の可逆 augmentation 部分圏から、元の通常 pullback への正本比較を制限する。
方針：同じ包含と正本比較を合成し、同値矢印の全部分複体を経て通常 pullback へ送る。
規約：元の二射影と指定 augmentation の全単体族を保持する。
使われ方：G-1 f の dg 通常 pullback とその実完全包含の比較に用いる。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)
def dgGluingPullbackUniverseInclusion :
    (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
      (dgNerve R (DGGluingPullbackObject R C D M)) ⟶
    (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
      (dgNerve R (DGGluingObject R C D M)) :=
  dgGluingUniverseNerveMap.{u, max u v w, max u v w, max (u + 1) v w}
    (dgGluingPullbackInclusion R C D M)
def dgGluingPullbackToLax :=
  dgGluingPullbackUniverseInclusion R C D M ≫ dgGluingUniverseDerivedNerveLaxComparison R C D M
lemma dgGluingPullbackToLax_vertex
    (x : ((SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
      (dgNerve R (DGGluingPullbackObject R C D M))) _⦋0⦌) :
    F2.IsLaxEquivalenceVertex (dgGluingUniverseDerivedYoneda.{u, v, w} R C)
      (dgGluingUniverseDerivedCoefficient R C D M)
      ((dgGluingPullbackToLax R C D M).app (Opposite.op ⦋0⦌) x) := by
  obtain ⟨x⟩ := x
  obtain ⟨X, rfl⟩ := Simplex.vertexEquiv.symm.surjective x
  change F2.IsLaxEquivalenceVertex _ _
    ((dgGluingUniverseDerivedNerveLaxComparison R C D M).app (Opposite.op ⦋0⦌)
      ((dgGluingUniverseNerveMap.{u, max u v w, max u v w, max (u + 1) v w}
        (dgGluingPullbackInclusion R C D M)).app (Opposite.op ⦋0⦌)
          (ULift.up (Simplex.vertex X))))
  rw [dgGluingUniverseNerveMap_vertex]
  exact (dgGluingPullbackProperty_iff_laxVertex R C D M X.val).mp X.property

def dgGluingPullbackEquivalenceSubcomplexComparison :
    (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
      (dgNerve R (DGGluingPullbackObject R C D M)) ⟶
    (F2.laxPullbackEquivalenceSubcomplex (dgGluingUniverseDerivedYoneda.{u, v, w} R C)
      (dgGluingUniverseDerivedCoefficient R C D M) : SSet) :=
  fullSubcomplexLift _ (dgGluingPullbackToLax R C D M)
    (dgGluingPullbackToLax_vertex R C D M)
lemma dgGluingPullbackEquivalenceSubcomplexComparison_ι :
    dgGluingPullbackEquivalenceSubcomplexComparison R C D M ≫
      (F2.laxPullbackEquivalenceSubcomplex (dgGluingUniverseDerivedYoneda.{u, v, w} R C)
        (dgGluingUniverseDerivedCoefficient R C D M)).ι =
    dgGluingPullbackToLax R C D M := fullSubcomplexLift_ι _ _ _
def dgGluingOrdinaryPullbackComparison :=
  dgGluingPullbackEquivalenceSubcomplexComparison R C D M ≫
    (F2.catPullbackEquivalenceSubcomplexIso (dgGluingUniverseDerivedYoneda.{u, v, w} R C)
      (dgGluingUniverseDerivedCoefficient R C D M)).inv
lemma dgGluingOrdinaryPullbackComparison_toLax :
    dgGluingOrdinaryPullbackComparison R C D M ≫
      F2.catPullbackToLax (dgGluingUniverseDerivedYoneda.{u, v, w} R C)
        (dgGluingUniverseDerivedCoefficient R C D M) =
      dgGluingPullbackToLax R C D M := by
  rw [dgGluingOrdinaryPullbackComparison,
    ← F2.catPullbackEquivalenceSubcomplexIso_ι, ← Category.assoc,
    Category.assoc (dgGluingPullbackEquivalenceSubcomplexComparison R C D M),
    Iso.inv_hom_id, Category.comp_id, dgGluingPullbackEquivalenceSubcomplexComparison_ι]
end SerrePositivity.InfinityCategories
