module
public import SerrePositivity.InfinityCategories.Derived.Gluing.OrdinaryPullbackFullyFaithful
public import SerrePositivity.InfinityCategories.Derived.Gluing.CanonicalStableStructure
public import SerrePositivity.KST.LocalizingInvariants.LaxDifferenceFunctor
public import SerrePositivity.InfinityCategories.Core.PrecompositionEquivalence
/-!
概要：通常 pullback への正本制限比較の本質的全射性。
方針：指定矢印の可逆性を cofiber の零性で移し、充満部分複体へ同型を戻す。
規約：両脚の完全性には正本の公開証明を使う。
使われ方：dg 通常 pullback と元の ∞ 圏的通常 pullback の同値に用いる。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet KST.LocalizingInvariants
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (hC : IsDGPretriangulated R C) (hD : IsDGPretriangulated R D)
include hC hD
lemma dgGluingCanonicalLaxEquivalenceVertex_of_vertexIso
    {x y : (F2.laxPullback (dgGluingUniverseDerivedYoneda.{u, v, w} R C)
      (dgGluingUniverseDerivedCoefficient R C D M)) _⦋0⦌}
    (e : VertexIso x y)
    (hx : F2.IsLaxEquivalenceVertex (dgGluingUniverseDerivedYoneda.{u, v, w} R C)
      (dgGluingUniverseDerivedCoefficient R C D M) x) :
    F2.IsLaxEquivalenceVertex (dgGluingUniverseDerivedYoneda.{u, v, w} R C)
      (dgGluingUniverseDerivedCoefficient R C D M) y := by
  let p := dgGluingStableYonedaMap R C hC
    (dgGluingUniverseDerivedYoneda_isExactFunctor.{u, v, w} R C hC)
  let q := dgGluingStableCoefficientMap R C D M hD
    (dgGluingUniverseDerivedCoefficient_isExactFunctor R C D M hD)
  exact (laxDifference_zero_iff p q y).mp
    (((laxDifference_zero_iff p q x).mpr hx).of_vertexIso
      (VertexIso.map e (laxDifference p q)))
lemma dgGluingPullbackEquivalenceSubcomplexComparison_isEssentiallySurjective :
    IsEssentiallySurjective (dgGluingPullbackEquivalenceSubcomplexComparison R C D M) := by
  intro y
  obtain ⟨x, ⟨e⟩⟩ :=
    dgGluingUniverseDerivedNerveLaxComparison_isEssentiallySurjective R C D M y.val
  obtain ⟨x⟩ := x
  obtain ⟨X, rfl⟩ := Simplex.vertexEquiv.symm.surjective x
  have hX : dgGluingPullbackProperty R C D M X :=
    (dgGluingPullbackProperty_iff_laxVertex R C D M X).mpr
      (dgGluingCanonicalLaxEquivalenceVertex_of_vertexIso R C D M hC hD e.symm
        (fullSubcomplexOnVertices_vertex y))
  let z := ULift.up.{max (u + 1) v w}
    (Simplex.vertex (A := R) (⟨X, hX⟩ : DGGluingPullbackObject R C D M))
  refine ⟨z, ⟨?_⟩⟩
  apply (F2.laxPullbackEquivalenceSubcomplex_isFullyFaithful
    (dgGluingUniverseDerivedYoneda.{u, v, w} R C)
    (dgGluingUniverseDerivedCoefficient R C D M)).preimageVertexIso
  change VertexIso ((dgGluingPullbackEquivalenceSubcomplexComparison R C D M ≫
    (F2.laxPullbackEquivalenceSubcomplex (dgGluingUniverseDerivedYoneda.{u, v, w} R C)
      (dgGluingUniverseDerivedCoefficient R C D M)).ι).app (Opposite.op ⦋0⦌) z) y.val
  rw [dgGluingPullbackEquivalenceSubcomplexComparison_ι]
  change VertexIso ((dgGluingUniverseDerivedNerveLaxComparison R C D M).app
    (Opposite.op ⦋0⦌) ((dgGluingUniverseNerveMap.{u, max u v w, max u v w, max (u + 1) v w}
      (dgGluingPullbackInclusion R C D M)).app (Opposite.op ⦋0⦌) z)) y.val
  dsimp only [z]
  rw [dgGluingUniverseNerveMap_vertex]
  exact e
end SerrePositivity.InfinityCategories
