module

public import SerrePositivity.KST.LocalizingInvariants.VerdierFiniteMappingCoconeRecovery
public import SerrePositivity.KST.LocalizingInvariants.IntervalMappingCoconeExtension
public import SerrePositivity.KST.LocalizingInvariants.CoconeFamilyCoreCriterion
public import SerrePositivity.KST.LocalizingInvariants.CorePreimageComparisonPrism

/-!
概要：元の商 Hom 比較円柱を、終端で元の全商余錐を保持する全余錐 core 円柱へ戻す。
方針：同じ比較円柱を区間 Hom 延長へ代入し、境界＝実分数評価像の厳密式を回収する。
規約：元の商余錐・全 Hom 円柱・その境界を変更せず、共有始点を追加入力にしない。
使われ方：回収した実余錐円柱と元の商余錐との全境界比較を同じ二胞体で構成する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

variable {A B C : StableCategory.{u}} {i : ExactMap A B} {q : ExactMap B C}
  {h : IsVerdierSequence i q} {n : ℕ} {D : (Δ[n] : SSet.{u}) ⟶ B.obj}
  {z : B.obj _⦋0⦌} {K : SSet.{u}} {S : K.Subcomplex}
  {a : S.toSSet ⟶ verdierDenominatorSpanFamily i
    (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z}
  {f : K ⟶ intervalMappingSpace
    (q.hom.app (Opposite.op ⦋0⦌)
      (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))))
    (q.hom.app (Opposite.op ⦋0⦌) z)}

/-- 元の商 Hom 比較円柱と終端の全商余錐を保持する、同じ全余錐円柱。 -/
structure VerdierRecoveredQuotientCoconeCylinder
    (r : VerdierFiniteMappingCoconeRecovery h D z S a f)
    (G : K ⟶ (ihom (join (Δ[n] : SSet.{u}) Δ[0])).obj C.obj) where
  whole : K ⊗ (Δ[1] : SSet.{u}) ⟶ (ihom (join (Δ[n] : SSet.{u}) Δ[0])).obj C.obj
  endpoint : (SSet.ι₁ : K ⟶ K ⊗ (Δ[1] : SSet.{u})) ≫ whole = G
  fixedPrefix : whole ≫ (pre (joinInl (Δ[n] : SSet.{u}) Δ[0])).app C.obj =
    SSet.const (functorVertex (D ≫ q.hom))
  lastArrow : whole ≫ (pre (joinMap (simplexLastPoint n) (𝟙 Δ[0]))).app C.obj =
    r.comparison.h ≫ vertexFiberι ((pre (boundary 1).ι).app C.obj)
      (functorVertex (intervalMappingBoundary
        (q.hom.app (Opposite.op ⦋0⦌)
          (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))))
        (q.hom.app (Opposite.op ⦋0⦌) z))) ≫
      (pre (joinStdSimplexIso 0 0).hom).app C.obj
  fixedApex : whole ≫ evaluateFunctorAt ((joinInr (Δ[n] : SSet.{u}) Δ[0]).app (Opposite.op ⦋0⦌)
    (stdSimplex.obj₀Equiv.symm (0 : Fin 1))) = SSet.const (q.hom.app (Opposite.op ⦋0⦌) z)

lemma exists_verdierRecoveredQuotientCoconeCylinder
    (r : VerdierFiniteMappingCoconeRecovery h D z S a f)
    (G : K ⟶ (ihom (join (Δ[n] : SSet.{u}) Δ[0])).obj C.obj)
    (hG : G ≫ (pre (joinInl (Δ[n] : SSet.{u}) Δ[0])).app C.obj =
      SSet.const (functorVertex (D ≫ q.hom)))
    (hGe : G ≫ (pre (joinMap (simplexLastPoint n) (𝟙 Δ[0]))).app C.obj =
      f ≫ vertexFiberι ((pre (boundary 1).ι).app C.obj)
        (functorVertex (intervalMappingBoundary
          (q.hom.app (Opposite.op ⦋0⦌)
            (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))))
          (q.hom.app (Opposite.op ⦋0⦌) z))) ≫
        (pre (joinStdSimplexIso 0 0).hom).app C.obj) :
    Nonempty (VerdierRecoveredQuotientCoconeCylinder r G) := by
  obtain ⟨U, he, hp, hn, hz⟩ := exists_relative_intervalMappingCoconeFamily
    (D ≫ q.hom) (q.hom.app (Opposite.op ⦋0⦌) z) (SSet.ι₁ : K ⟶ K ⊗ Δ[1]) G
    r.comparison.h hG (by
      rw [← Category.assoc (SSet.ι₁ : K ⟶ K ⊗ Δ[1]) r.comparison.h,
        r.comparison.h₁]
      exact hGe.symm)
  exact ⟨⟨U, he, hp, hn, hz⟩⟩

namespace VerdierRecoveredQuotientCoconeCylinder
variable {r : VerdierFiniteMappingCoconeRecovery h D z S a f}
  {G : K ⟶ (ihom (join (Δ[n] : SSet.{u}) Δ[0])).obj C.obj}
  (U : VerdierRecoveredQuotientCoconeCylinder r G)

/-- 全余錐円柱の境界次辺は、元の同じ実境界円柱の分数評価像に厳密に一致する。 -/
lemma boundary_next : (S.ι ▷ (Δ[1] : SSet.{u})) ≫ U.whole ≫
    (pre (joinMap (simplexLastPoint n) (𝟙 Δ[0]))).app C.obj =
    r.boundary.h ≫ verdierDenominatorSpanCanonicalComparison i
      (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z ≫
    fixedFractionEvaluation q.hom (Fibration.weakEquivalences i) h.inverts
      (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z ≫
    vertexFiberι ((pre (boundary 1).ι).app C.obj)
      (functorVertex (intervalMappingBoundary
        (q.hom.app (Opposite.op ⦋0⦌)
          (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))))
        (q.hom.app (Opposite.op ⦋0⦌) z))) ≫
      (pre (joinStdSimplexIso 0 0).hom).app C.obj := by
  rw [U.lastArrow, ← Category.assoc (S.ι ▷ (Δ[1] : SSet.{u})) r.comparison.h,
    r.comparison_boundary]
  simp only [Category.assoc]

lemma invertsAllEdges : InvertsEdges U.whole Set.univ := by
  apply coconeFamily_invertsAllEdges_of_prefix_apex _ _ _ U.fixedApex
  rw [U.fixedPrefix]
  exact invertsEdges_const _ _ _ Set.univ

/-- 同じ商全余錐円柱を、全図式の元の core へそのまま戻す。 -/
def coreWhole : K ⊗ (Δ[1] : SSet.{u}) ⟶
    (quasicategoryCore ((ihom (join (Δ[n] : SSet.{u}) Δ[0])).obj C.obj) : SSet.{u}) :=
  allEdgesCoreLift U.whole U.invertsAllEdges

lemma coreWhole_ι : U.coreWhole ≫
    (quasicategoryCore ((ihom (join (Δ[n] : SSet.{u}) Δ[0])).obj C.obj)).ι = U.whole :=
  allEdgesCoreLift_ι _ _

end VerdierRecoveredQuotientCoconeCylinder
end SerrePositivity.KST.LocalizingInvariants
