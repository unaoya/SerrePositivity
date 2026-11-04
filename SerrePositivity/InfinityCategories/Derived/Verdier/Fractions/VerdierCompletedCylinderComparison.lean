module

public import SerrePositivity.InfinityCategories.Stable.Quasicategory.RelativeFunctorCoreRestriction
public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedCylinderImage

/-!
概要：実完成円柱の調整済み商像と元の商余錐円柱を、指定全境界比較を保持して結ぶ。
方針：同じ core 比較を標準単体へ移し、証明済み始面一致から Kan 円柱延長を実適用する。
規約：元の単位・商射・境界二胞体と始端比較を保持する。
使われ方：元の第一行亜群化評価の有限相対全余錐比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalClosed SSet
open CategoryTheory.CartesianMonoidalCategory
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Fibration
open SerrePositivity.SimplicialModel
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
  {G : K ⟶ (ihom (join (Δ[n] : SSet.{u}) Δ[0])).obj C.obj}
  {r : VerdierFiniteMappingCoconeRecovery h D z S a f}
  {U : VerdierRecoveredQuotientCoconeCylinder r G}

local notation "P" => S.toSSet ⊗ (Δ[1] : SSet)
local notation "J" => join (Δ[n] : SSet) Δ[0]

variable {c : VerdierRecoveredInitialComparison r U} {b : VerdierRecoveredBoundaryComparison r U}
namespace VerdierRelativeInitialComparison
variable (d : VerdierRelativeInitialComparison c b)

def simplexQuotientHomotopy : SSet.Homotopy
    (c.simplexFamily ≫ relativeFirstRowSimplexQuotient q (n + 1))
    ((SSet.ι₀ : K ⟶ K ⊗ (Δ[1] : SSet.{u})) ≫ U.coreWhole ≫
      quasicategoryCoreMap ((pre (joinStdSimplexIso n 0).inv).app C.obj)) := by
  let H := functorHomotopyPostcomp d.coreHomotopy
    (quasicategoryCoreMap ((pre (joinStdSimplexIso n 0).inv).app C.obj))
  have hs : (c.relativeFamily ≫ relativeFunctorCoreQuotient q.hom J) ≫
      quasicategoryCoreMap ((pre (joinStdSimplexIso n 0).inv).app C.obj) =
      c.simplexFamily ≫ relativeFirstRowSimplexQuotient q (n + 1) := by
    apply (cancel_mono (quasicategoryCore ((ihom (Δ[n + 1] : SSet.{u})).obj C.obj)).ι).mp
    rw [Category.assoc, quasicategoryCoreMap_ι]
    change (r.cylinder.whole ≫ (ihom J).map q.hom) ≫
      (pre (joinStdSimplexIso n 0).inv).app C.obj =
      (r.cylinder.whole ≫ (pre (joinStdSimplexIso n 0).inv).app B.obj) ≫
        (ihom (Δ[n + 1] : SSet.{u})).map q.hom
    rw [Category.assoc, (pre (joinStdSimplexIso n 0).inv).naturality q.hom, Category.assoc]
  exact { h := H.h, h₀ := H.h₀.trans hs, h₁ := H.h₁, rel := H.rel }

lemma simplexQuotientHomotopy_boundary :
    (S.ι ▷ (Δ[1] : SSet.{u})) ≫ d.simplexQuotientHomotopy.h =
      ((SSet.ι₀ : S.toSSet ⟶ P) ▷ (Δ[1] : SSet.{u})) ≫ b.simplexQuotientHomotopy.h := by
  change (S.ι ▷ (Δ[1] : SSet.{u})) ≫ (d.corePrism ≫ _) =
    ((SSet.ι₀ : S.toSSet ⟶ P) ▷ (Δ[1] : SSet.{u})) ≫ (b.coreHomotopy.h ≫ _)
  simpa only [Category.assoc] using congrArg
    (fun t => t ≫ quasicategoryCoreMap ((pre (joinStdSimplexIso n 0).inv).app C.obj))
    d.boundary_core_eq

end VerdierRelativeInitialComparison

/-- 同じ実完成円柱の商像を元の U と比較し、指定 S 比較と K 始端比較を厳密保持する。 -/
lemma exists_verdierCompletedCylinderComparison
    (d : VerdierRelativeInitialComparison c b) (X : VerdierRecoveredCompletedCylinder c)
    (Y : VerdierCompletedCylinderImage X) :
    ∃ H : SSet.Homotopy Y.whole
      (U.coreWhole ≫ quasicategoryCoreMap ((pre (joinStdSimplexIso n 0).inv).app C.obj)),
      ((SSet.ι₀ : K ⟶ K ⊗ (Δ[1] : SSet.{u})) ▷ (Δ[1] : SSet.{u})) ≫ H.h =
        d.simplexQuotientHomotopy.h ∧
      ((S.ι ▷ (Δ[1] : SSet.{u})) ▷ (Δ[1] : SSet.{u})) ≫ H.h =
        b.simplexQuotientHomotopy.h := by
  let T := U.coreWhole ≫ quasicategoryCoreMap ((pre (joinStdSimplexIso n 0).inv).app C.obj)
  have hface (L : SSet.{u}) : L ◁ stdSimplex.δ (1 : Fin 2) =
      fst L (Δ[0] : SSet.{u}) ≫ (SSet.ι₀ : L ⟶ L ⊗ (Δ[1] : SSet.{u})) := by
    rw [stdSimplex.δ_one_eq_const]
    rfl
  let Hpre := functorHomotopyPrecomp d.simplexQuotientHomotopy (fst K (Δ[0] : SSet.{u}))
  have hF : (K ◁ stdSimplex.δ (1 : Fin 2)) ≫ Y.whole =
      fst K (Δ[0] : SSet.{u}) ≫ (c.simplexFamily ≫ relativeFirstRowSimplexQuotient q (n + 1)) := by
    rw [hface, Category.assoc, Y.start_eq]
  have hG : (K ◁ stdSimplex.δ (1 : Fin 2)) ≫ T =
      fst K (Δ[0] : SSet.{u}) ≫
        ((SSet.ι₀ : K ⟶ K ⊗ (Δ[1] : SSet.{u})) ≫ U.coreWhole ≫
          quasicategoryCoreMap ((pre (joinStdSimplexIso n 0).inv).app C.obj)) := by
    rw [hface, Category.assoc]
  let H₀ : SSet.Homotopy ((K ◁ stdSimplex.δ (1 : Fin 2)) ≫ Y.whole)
      ((K ◁ stdSimplex.δ (1 : Fin 2)) ≫ T) :=
    { h := Hpre.h, h₀ := Hpre.h₀.trans hF.symm, h₁ := Hpre.h₁.trans hG.symm, rel := Hpre.rel }
  let Hₛ : SSet.Homotopy ((S.ι ▷ (Δ[1] : SSet.{u})) ≫ Y.whole)
      ((S.ι ▷ (Δ[1] : SSet.{u})) ≫ T) :=
    { h := b.simplexQuotientHomotopy.h
      h₀ := b.simplexQuotientHomotopy.h₀.trans Y.boundary_eq.symm
      h₁ := b.simplexQuotientHomotopy.h₁
      rel := b.simplexQuotientHomotopy.rel }
  have hc : ((S.ι ▷ (Δ[0] : SSet.{u})) ▷ (Δ[1] : SSet.{u})) ≫ H₀.h =
      ((S.toSSet ◁ stdSimplex.δ (1 : Fin 2)) ▷ (Δ[1] : SSet.{u})) ≫ Hₛ.h := by
    change ((S.ι ▷ (Δ[0] : SSet.{u})) ▷ (Δ[1] : SSet.{u})) ≫
      (fst K (Δ[0] : SSet.{u}) ▷ (Δ[1] : SSet.{u})) ≫ d.simplexQuotientHomotopy.h = _
    rw [← comp_whiskerRight_assoc, whiskerRight_fst,
      comp_whiskerRight, Category.assoc, d.simplexQuotientHomotopy_boundary,
      ← comp_whiskerRight_assoc, ← hface]
  obtain ⟨H, h₀, hₛ⟩ := exists_kanCylinderComparison S.ι Y.whole T H₀ Hₛ hc
  refine ⟨H, ?_, hₛ⟩
  have hz := congrArg
    (fun t => (LargeParameterHomotopy.vertexSection K ▷ (Δ[1] : SSet.{u})) ≫ t) h₀
  change _ = (LargeParameterHomotopy.vertexSection K ▷ (Δ[1] : SSet.{u})) ≫
    (fst K (Δ[0] : SSet.{u}) ▷ (Δ[1] : SSet.{u})) ≫ d.simplexQuotientHomotopy.h at hz
  simpa only [← comp_whiskerRight_assoc, LargeParameterHomotopy.section_zero,
    show LargeParameterHomotopy.vertexSection K ≫ fst K (Δ[0] : SSet.{u}) = 𝟙 K from rfl,
    id_whiskerRight, Category.id_comp] using hz

/-- 元の実有限境界から選択した比較を、完成円柱上まで保持した全回収。 -/
structure VerdierCompletedCoconeComparison (b : VerdierRecoveredBoundaryComparison r U) where
  initial : VerdierRecoveredInitialComparison r U
  relativeInitial : VerdierRelativeInitialComparison initial b
  cylinder : VerdierRecoveredCompletedCylinder initial
  image : VerdierCompletedCylinderImage cylinder
  homotopy : SSet.Homotopy image.whole
    (U.coreWhole ≫ quasicategoryCoreMap ((pre (joinStdSimplexIso n 0).inv).app C.obj))
  start_eq : ((SSet.ι₀ : K ⟶ K ⊗ (Δ[1] : SSet.{u})) ▷ (Δ[1] : SSet.{u})) ≫
    homotopy.h = relativeInitial.simplexQuotientHomotopy.h
  boundary_eq : ((S.ι ▷ (Δ[1] : SSet.{u})) ▷ (Δ[1] : SSet.{u})) ≫ homotopy.h =
    b.simplexQuotientHomotopy.h

/-- 指定された同じ実 S 全比較を保ち、元の亜群化まで全データを回収する。 -/
lemma exists_verdierCompletedCoconeComparison (b : VerdierRecoveredBoundaryComparison r U) :
    Nonempty (VerdierCompletedCoconeComparison b) := by
  obtain ⟨c⟩ := exists_verdierRecoveredInitialComparison r U
  obtain ⟨d⟩ := exists_verdierRelativeInitialComparison c b
  obtain ⟨X⟩ := exists_verdierRecoveredCompletedCylinder c
  obtain ⟨Y⟩ := exists_verdierCompletedCylinderImage X
  obtain ⟨H, h₀, hₛ⟩ := exists_verdierCompletedCylinderComparison d X Y
  exact ⟨⟨c, d, X, Y, H, h₀, hₛ⟩⟩

/-- 元の有限商全余錐と指定実境界から、完成上の境界付き全円柱比較を一括回収する。 -/
lemma exists_verdierFiniteCompletedCoconeRecovery [K.Finite] [S.toSSet.Finite]
    (G : K ⟶ (ihom J).obj C.obj)
    (hG : G ≫ (pre (joinInl (Δ[n] : SSet.{u}) Δ[0])).app C.obj =
      SSet.const (functorVertex (D ≫ q.hom)))
    (hz : G ≫ evaluateFunctorAt ((joinInr (Δ[n] : SSet.{u}) Δ[0]).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (0 : Fin 1))) = SSet.const (q.hom.app (Opposite.op ⦋0⦌) z))
    (ha : a ≫ verdierDenominatorSpanCanonicalComparison i
        (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z ≫
      fixedFractionEvaluation q.hom (weakEquivalences i) h.inverts
        (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z =
      S.ι ≫ spanCoconeLastMapping (D ≫ q.hom) (q.hom.app (Opposite.op ⦋0⦌) z) G hG hz) :
    ∃ r : VerdierFiniteMappingCoconeRecovery h D z S a
        (spanCoconeLastMapping (D ≫ q.hom) (q.hom.app (Opposite.op ⦋0⦌) z) G hG hz),
      ∃ U : VerdierRecoveredQuotientCoconeCylinder r G,
        ∃ b : VerdierRecoveredBoundaryComparison r U,
          Nonempty (VerdierCompletedCoconeComparison b) := by
  obtain ⟨r, U, ⟨b⟩⟩ := exists_verdierFiniteCoconeBoundaryRecovery G hG hz ha
  exact ⟨r, U, b, exists_verdierCompletedCoconeComparison b⟩

end SerrePositivity.KST.LocalizingInvariants
