module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.AppendDifferential
public import SerrePositivity.DifferentialGraded.Module.MaurerCartanTriangulated

/-!
概要：局所縮約の graded 自己射を、実正規化 MC 加群の斉次自己射へ移す。
方針：始域と標的の既存 Hom 移送を合成し、評価成分を保つ。
規約：閉性は主張しない。微分の theta 項は後続の縮約式で検証する。
使われ方：実正規化 bar の局所ホモトピー。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open CochainComplex HomComplex
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {J : Type u} [PartialOrder J] (F : J ⥤ ModuleCategory R D)

def dgStrictNormalizedEndRebase (q : ℤ)
    (z : (moduleHom R D
      (ForgetEnrichment.to (Complex R)
        (dgCoherentBarNormalizedGraded R D (dgCoherentBarStrictDiagram R D F)))
      (ForgetEnrichment.to (Complex R)
        (dgCoherentBarNormalizedGraded R D (dgCoherentBarStrictDiagram R D F)))).X q) :
    (moduleHom R D (dgCoherentBarStrictNormalizedModule R D F)
      (dgCoherentBarStrictNormalizedModule R D F)).X q :=
  moduleMaurerCartanTargetRebase R D
    (ForgetEnrichment.to (Complex R)
      (dgCoherentBarNormalizedGraded R D (dgCoherentBarStrictDiagram R D F)))
    (dgCoherentBarNormalizedTheta R D (dgCoherentBarStrictDiagram R D F))
    (dgCoherentBarNormalizedTheta_maurerCartan R D (dgCoherentBarStrictDiagram R D F)
      (dgCoherentBarMaurerCartan_unconditional R D (dgCoherentBarStrictDiagram R D F)))
    (dgCoherentBarStrictNormalizedModule R D F) q
    (dgCoherentBarNormalizedRebaseHom R D (dgCoherentBarStrictDiagram R D F)
      (dgCoherentBarMaurerCartan_unconditional R D (dgCoherentBarStrictDiagram R D F))
      (ForgetEnrichment.to (Complex R)
        (dgCoherentBarNormalizedGraded R D (dgCoherentBarStrictDiagram R D F))) q z)

lemma dgStrictNormalizedEndRebase_π (q : ℤ)
    (z : (moduleHom R D
      (ForgetEnrichment.to (Complex R)
        (dgCoherentBarNormalizedGraded R D (dgCoherentBarStrictDiagram R D F)))
      (ForgetEnrichment.to (Complex R)
        (dgCoherentBarNormalizedGraded R D (dgCoherentBarStrictDiagram R D F)))).X q)
    (x : D) (i j : ℤ) (hij : i + q = j) :
    ((moduleHomπ R D (dgCoherentBarStrictNormalizedModule R D F)
      (dgCoherentBarStrictNormalizedModule R D F) x).f q
      (dgStrictNormalizedEndRebase R D F q z)).v i j hij =
    ((moduleHomπ R D
      (ForgetEnrichment.to (Complex R)
        (dgCoherentBarNormalizedGraded R D (dgCoherentBarStrictDiagram R D F)))
      (ForgetEnrichment.to (Complex R)
        (dgCoherentBarNormalizedGraded R D (dgCoherentBarStrictDiagram R D F))) x).f q z).v
          i j hij := by
  unfold dgStrictNormalizedEndRebase
  erw [moduleMaurerCartanTargetRebase_π]
  simp only [maurerCartanTargetRebaseCochain, Cochain.mk_v,
    dgCoherentBarNormalizedRebaseHom, moduleHomElementMk_π]

def dgStrictAppendHom (b : J) :
    (moduleHom R D (dgCoherentBarStrictNormalizedModule R D F)
      (dgCoherentBarStrictNormalizedModule R D F)).X (-1) :=
  dgStrictNormalizedEndRebase R D F (-1) (dgStrictAppendGradedHom R D F b)

end SerrePositivity.InfinityCategories
