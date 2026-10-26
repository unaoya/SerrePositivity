module

public import SerrePositivity.KST.LocalizingInvariants.VerdierCompletedCylinderComparison

/-!
概要：元の完成円柱の終端を、同じ K 全余錐と指定 S 正規化終端へ同時に接続する。
方針：保存された二段の全 Homotopy を同じ終面へ制限し、元の全境界式も制限する。
規約：単位・指定比較二胞体を選び直さず、全境界写像の厳密等式を保持する。
使われ方：元の第一行単体亜群化の有限相対持ち上げと実境界正規化の接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Fibration
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

variable {b : VerdierRecoveredBoundaryComparison r U}
namespace VerdierCompletedCoconeComparison
variable (w : VerdierCompletedCoconeComparison b)

/-- 同じ完成 K 円柱の実終端。 -/
def endpoint : K ⟶ groupoidCompletion (relativeFirstRowSimplex q (n + 1) : SSet.{u}) :=
  w.cylinder.endpoint

/-- 元の全商余錐そのものを表す core の実終端。 -/
def target (_w : VerdierCompletedCoconeComparison b) :
    K ⟶ (quasicategoryCore ((ihom (Δ[n + 1] : SSet.{u})).obj C.obj) : SSet.{u}) :=
  (SSet.ι₁ : K ⟶ K ⊗ (Δ[1] : SSet.{u})) ≫ U.coreWhole ≫
    quasicategoryCoreMap ((pre (joinStdSimplexIso n 0).inv).app C.obj)

lemma target_ι : w.target ≫
    (quasicategoryCore ((ihom (Δ[n + 1] : SSet.{u})).obj C.obj)).ι =
      G ≫ (pre (joinStdSimplexIso n 0).inv).app C.obj := by
  dsimp only [target]
  simp only [Category.assoc, quasicategoryCoreMap_ι]
  rw [
    ← Category.assoc U.coreWhole, U.coreWhole_ι, ← Category.assoc, U.endpoint]

/-- 元の全単位 Homotopy の、同じ完成 K 円柱の終端上の制限。 -/
def endpointUnitHomotopy : SSet.Homotopy
    (w.endpoint ≫ relativeFirstRowSimplexCompletionComparison q (n + 1))
    ((SSet.ι₁ : K ⟶ K ⊗ (Δ[1] : SSet.{u})) ≫ w.image.whole) := by
  let H := functorHomotopyPrecomp w.image.homotopy
    (SSet.ι₁ : K ⟶ K ⊗ (Δ[1] : SSet.{u}))
  have hs : (SSet.ι₁ : K ⟶ K ⊗ (Δ[1] : SSet.{u})) ≫
      (w.cylinder.homotopy.h ≫ relativeFirstRowSimplexCompletionComparison q (n + 1)) =
      w.endpoint ≫ relativeFirstRowSimplexCompletionComparison q (n + 1) := by
    rw [← Category.assoc, w.cylinder.homotopy.h₁]
    rfl
  exact { h := H.h, h₀ := H.h₀.trans hs, h₁ := H.h₁, rel := H.rel }

/-- 指定境界二胞体を保持した商全比較の、同じ K 終端上の制限。 -/
def endpointComparisonHomotopy : SSet.Homotopy
    ((SSet.ι₁ : K ⟶ K ⊗ (Δ[1] : SSet.{u})) ≫ w.image.whole) w.target :=
  functorHomotopyPrecomp w.homotopy (SSet.ι₁ : K ⟶ K ⊗ (Δ[1] : SSet.{u}))

/-- 同じ二段の終端 Homotopy が与える元の亜群化評価の全 FunctorIso。 -/
def endpointIso : FunctorIso
    (w.endpoint ≫ relativeFirstRowSimplexCompletionComparison q (n + 1)) w.target :=
  functorIsoOfSimplicialHomotopy w.endpointUnitHomotopy ≪≫
    functorIsoOfSimplicialHomotopy w.endpointComparisonHomotopy

/-- 実 S 正規化終端は、同じ完成 K 終端の厳密な制限。 -/
lemma endpoint_boundary : S.ι ≫ w.endpoint =
    (SSet.ι₁ : S.toSSet ⟶ P) ≫ r.simplexCylinder ≫
      groupoidCompletionMap (relativeFirstRowSimplex q (n + 1) : SSet.{u}) :=
  w.cylinder.endpoint_boundary

/-- K 終端の単位比較の S 制限は、同じ実 S 終端への元の全単位の制限。 -/
lemma endpointUnit_boundary : (S.ι ▷ (Δ[1] : SSet.{u})) ≫ w.endpointUnitHomotopy.h =
    (((SSet.ι₁ : S.toSSet ⟶ P) ≫ r.simplexCylinder) ▷ (Δ[1] : SSet.{u})) ≫
      (FunctorIso.simplicialHomotopy
        (relativeFirstRowSimplexCompletionComparison_unitIso q (n + 1))).h := by
  change (S.ι ▷ (Δ[1] : SSet.{u})) ≫
    ((SSet.ι₁ : K ⟶ K ⊗ (Δ[1] : SSet.{u})) ▷ (Δ[1] : SSet.{u})) ≫ w.image.homotopy.h = _
  rw [← comp_whiskerRight_assoc, ← SSet.ι₁_comp, comp_whiskerRight,
    Category.assoc, w.image.boundary_unit_eq, ← comp_whiskerRight_assoc]

/-- K 終端比較の S 制限は、選択済みの同じ S 全比較の終面そのもの。 -/
lemma endpointComparison_boundary : (S.ι ▷ (Δ[1] : SSet.{u})) ≫
    w.endpointComparisonHomotopy.h =
      ((SSet.ι₁ : S.toSSet ⟶ P) ▷ (Δ[1] : SSet.{u})) ≫ b.simplexQuotientHomotopy.h := by
  change (S.ι ▷ (Δ[1] : SSet.{u})) ≫
    ((SSet.ι₁ : K ⟶ K ⊗ (Δ[1] : SSet.{u})) ▷ (Δ[1] : SSet.{u})) ≫ w.homotopy.h = _
  rw [← comp_whiskerRight_assoc, ← SSet.ι₁_comp, comp_whiskerRight,
    Category.assoc, w.boundary_eq]

/-- 正規化 S 実終端の包含後は、保存済みの同じ元の実終端余錐。 -/
lemma endpoint_boundary_ι :
    ((SSet.ι₁ : S.toSSet ⟶ P) ≫ r.simplexCylinder) ≫
      (relativeFirstRowSimplex q (n + 1)).ι =
      r.cylinder.endCone ≫ (pre (joinStdSimplexIso n 0).inv).app B.obj := by
  rw [Category.assoc, r.simplexCylinder_ι, ← Category.assoc, r.cylinder.homotopy.h₁]

end VerdierCompletedCoconeComparison
end SerrePositivity.KST.LocalizingInvariants
