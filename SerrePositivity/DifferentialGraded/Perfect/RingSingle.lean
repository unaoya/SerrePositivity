module
public import SerrePositivity.DifferentialGraded.Perfect.FiniteProjectiveImage
public import SerrePositivity.DifferentialGraded.Module.RingComplexFunctor
public import SerrePositivity.DifferentialGraded.Derived.Linear

/-! # 次数0に集中する有限射影複体の主導来像はperfect -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex MonoidalCategory
variable (A : Type u) [CommRing A]

/-- 一対象Aの代表加群は単位複体の定数加群と厳密に一致する。 -/
lemma ringModule_unit_eq_representable :
    ringModule A (𝟙_ (Complex A)) = representable A (D := PUnit.{1}) PUnit.unit :=
  ringModule_recover A (representable A (D := PUnit.{1}) PUnit.unit)

/-- 次数0の通常加群を主dg加群導来圏へ送る加法的関手。 -/
def ringSingleZeroToDerived : ModuleCat.{u} A ⥤ DerivedModuleCategory A PUnit.{1} :=
  single (ModuleCat.{u} A) (.up ℤ) 0 ⋙ complexToRingModule A ⋙ moduleToDerived A PUnit.{1}

instance ringSingleZeroToDerivedAdditive : (ringSingleZeroToDerived A).Additive := by
  dsimp [ringSingleZeroToDerived]
  infer_instance

/-- 基礎環Aの次数0像は主Perfの代表生成元である。 -/
lemma ringSingleZeroToDerived_unit_perfect :
    modulePerfect A PUnit.{1} ((ringSingleZeroToDerived A).obj (ModuleCat.of A A)) := by
  change modulePerfect A PUnit.{1} ((moduleToDerived A PUnit.{1}).obj
    (ForgetEnrichment.of (Complex A) (ringModule A (𝟙_ (Complex A)))))
  rw [ringModule_unit_eq_representable]
  exact modulePerfectOver_representable A PUnit.{1} PUnit.unit (Set.mem_univ _)

/-- 有限射影加群の次数0像は、有限個の代表生成元の和のretractとしてperfect。 -/
lemma ringSingleZeroToDerived_finiteProjective_perfect (M : ModuleCat.{u} A)
    [Module.Finite A M] [Module.Projective A M] :
    modulePerfect A PUnit.{1} ((ringSingleZeroToDerived A).obj M) :=
  modulePerfectOver_image_finiteProjective A PUnit.{1} Set.univ (ringSingleZeroToDerived A)
    (ringSingleZeroToDerived_unit_perfect A) M

end SerrePositivity.DifferentialGraded
