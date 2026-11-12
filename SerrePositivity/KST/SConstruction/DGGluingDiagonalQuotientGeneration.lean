module
public import SerrePositivity.KST.SConstruction.DGGluingDiagonalLeftGeneration
public import SerrePositivity.KST.SConstruction.DGPointedQuotientEnd
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparison.LocalFlatness

/-! # 指定 dg gluing 対角商の右軸生成性
概要：左成分の明示生成条件の下で、同じ実対角商の Perf は元の右軸像から生成される。
方針：D の既存対角代表零化を、実二軸・対角像の生成判定へ直接適用する。
規約：商・分数・局所化の API は新設しない。使われ方：K-10 c の具体的商 End 比較。
-/
@[expose] public section
noncomputable section
universe u v w t
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (zc : C) (hc : IsZero (ForgetEnrichment.of (Complex R) zc))
  (zd : D) (hd : IsZero (ForgetEnrichment.of (Complex R) zd))
  {A : Type t} [DGCategory R A] (j : DGFunctor R A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M))
local notation "G" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M
local notation "T" => PointedDGQuotientObject R j
local notation "q" => pointedDGQuotientProjection R j
local notation "Q" => moduleToDerived R T

include hc hd in
/-- 左成分の生成条件の下で、同じ実対角商の Perf の包含は右軸像から従う。 -/
lemma dgGluingDiagonalQuotient_perfect_le_of_right
    (hgen : modulePerfectOver R C (Set.range (fun a => (j.obj a).left)) = modulePerfect R C)
    (P : ObjectProperty (DerivedModuleCategory R T)) [P.IsTriangulated]
    [P.IsClosedUnderIsomorphisms] [P.IsStableUnderRetracts]
    (hR : ∀ d : D, P ((Q).obj (ForgetEnrichment.of (Complex R)
      (representable R ((q).obj (dgGluingRightAxisObject R C D M zc d)))))) :
    modulePerfect R T ≤ P := by
  have hJ (a : A) : P ((Q).obj (ForgetEnrichment.of (Complex R)
      (representable R ((q).obj (j.obj a))))) :=
    P.prop_of_isZero (DGQuotient.quotientRepresentable_derived_isZero R G
      (dgQuotientImage R j) ⟨j.obj a, ⟨a, rfl⟩⟩)
  have h := dgGluingPerfectOver_image_le_of_diagonal R C D M zc hc zd hd T (q) j
    hgen P hR hJ
  apply (modulePerfect_le_iff_generators R T P).mpr
  intro y
  obtain ⟨x, rfl⟩ := (DGQuotient.quotientObjectEquiv G (dgQuotientImage R j)).surjective y
  exact h _ (modulePerfectOver_representable R T _ ⟨x, rfl⟩)

include hc hd in
/-- 同じ明示左生成条件の下で、元の全右軸像が同じ実対角商の全 Perf を生成する。 -/
lemma dgGluingDiagonalQuotient_perfectOver_right_eq
    (hgen : modulePerfectOver R C (Set.range (fun a => (j.obj a).left)) = modulePerfect R C) :
    modulePerfectOver R T
      (Set.range (fun d => (q).obj (dgGluingRightAxisObject R C D M zc d))) =
      modulePerfect R T := by
  apply le_antisymm
  · exact modulePerfectOver_mono R T (Set.subset_univ _)
  · apply (dgGluingDiagonalQuotient_perfect_le_of_right R C D M zc hc zd hd j hgen
      (modulePerfectOver R T
        (Set.range (fun d => (q).obj (dgGluingRightAxisObject R C D M zc d)))))
    intro d
    exact modulePerfectOver_representable R T _ ⟨d, rfl⟩

end SerrePositivity.KST.SConstruction
