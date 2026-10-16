module
public import SerrePositivity.DifferentialGraded.Perfect.RingSingle
public import SerrePositivity.DifferentialGraded.Module.FreeSphereShift

/-! # 全整数次数に集中する有限射影複体のperfect性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex MonoidalCategory
variable (A : Type u) [CommRing A]

/-- 一対象加群の厳密な復元を使い、実際のshift対象を照合する。 -/
lemma ringModule_shift_eq (P : Complex A) (s : ℤ) :
    ringModule A (P⟦s⟧) = shiftModule s (ringModule A P) :=
  ringModule_recover A (shiftModule s (ringModule A P))

/-- 通常複体から主加群への比較はshift対象に関して厳密な同型を持つ。 -/
def complexToRingModuleShiftObjIso (P : Complex A) (s : ℤ) :
    (complexToRingModule A).obj (P⟦s⟧) ≅ ((complexToRingModule A).obj P)⟦s⟧ :=
  eqToIso (congrArg (ForgetEnrichment.of (Complex A)) (ringModule_shift_eq A P s))

/-- 次数nの通常加群を主dg加群導来圏へ送る。 -/
def ringSingleToDerived (n : ℤ) : ModuleCat.{u} A ⥤ DerivedModuleCategory A PUnit.{1} :=
  single (ModuleCat.{u} A) (.up ℤ) n ⋙ complexToRingModule A ⋙ moduleToDerived A PUnit.{1}

instance ringSingleToDerivedAdditive (n : ℤ) : (ringSingleToDerived A n).Additive := by
  dsimp [ringSingleToDerived]
  infer_instance

/-- sphere nの主導来像は、代表生成元の−n shiftと同型なのでperfect。 -/
lemma ringSingleToDerived_unit_perfect (n : ℤ) :
    modulePerfect A PUnit.{1} ((ringSingleToDerived A n).obj (ModuleCat.of A A)) := by
  let F := complexToRingModule A
  let Q := moduleToDerived A PUnit.{1}
  let e : (complexSphere A 0)⟦-n⟧ ≅ complexSphere A n :=
    complexSphereShiftIso A 0 (-n) ≪≫ eqToIso (by congr 1; omega)
  let eM : (F.obj (complexSphere A 0))⟦-n⟧ ≅ F.obj (complexSphere A n) :=
    (complexToRingModuleShiftObjIso A (complexSphere A 0) (-n)).symm ≪≫ F.mapIso e
  let eD : (Q.obj (F.obj (complexSphere A 0)))⟦-n⟧ ≅ Q.obj (F.obj (complexSphere A n)) :=
    ((Q.commShiftIso (-n)).app _).symm ≪≫ Q.mapIso eM
  exact (modulePerfect A PUnit.{1}).prop_of_iso eD
    (modulePerfect_shift A PUnit.{1} (ringSingleZeroToDerived_unit_perfect A) (-n))

/-- 任意整数次数の有限射影加群の主導来像はperfect。 -/
lemma ringSingleToDerived_finiteProjective_perfect (n : ℤ) (M : ModuleCat.{u} A)
    [Module.Finite A M] [Module.Projective A M] :
    modulePerfect A PUnit.{1} ((ringSingleToDerived A n).obj M) :=
  modulePerfectOver_image_finiteProjective A PUnit.{1} Set.univ (ringSingleToDerived A n)
    (ringSingleToDerived_unit_perfect A n) M

end SerrePositivity.DifferentialGraded
