module
public import SerrePositivity.InfinityCategories.Derived.Gluing.ConeModuleMapComparison
public import SerrePositivity.DifferentialGraded.Module.QuasiIso

/-! 指定 cochain から作った全 dg 自然な加群円錐射自身の準同型性。 -/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory CochainComplex HomologicalComplex DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (Y Z : DGGluingObject R C D M)
  (f : ForgetEnrichment.of (Complex R) Y ⟶ ForgetEnrichment.of (Complex R) Z)
  (p : DGGluingConeRepresentative R C Y.left Z.left (dgGluingConeLeftArrow R C D M Y Z f))
  (q : DGGluingConeRepresentative R D Y.right Z.right
    ((dgYoneda R D).onClosed.map (dgGluingConeRightArrow R C D M Y Z f)))
local notation "G" => DGGluingObject R C D M

/-- 評価円錐との同型を外すと、同じ全加群射が対象ごとの準同型になる。 -/
lemma dgGluingConeModuleMap_quasiIso :
    moduleQuasiIso R G (dgGluingConeModuleMap R C D M Y Z f p q) := by
  intro X
  apply (quasiIso_iff_comp_left (dgGluingConeModuleEvaluationIso R C D M Y Z f X).hom
    ((moduleEvaluation R G X).map (dgGluingConeModuleMap R C D M Y Z f p q))).1
  exact dgGluingConeModuleMapEvaluation_quasiIso R C D M X Y Z f p q

omit p q in
/-- 元の両圏の前三角性を明示入力とする、同じ選んだ円錐射も準同型。 -/
lemma dgGluingChosenConeModuleMap_quasiIso
    (hC : IsDGPretriangulated R C) (hD : IsDGPretriangulated R D) :
    moduleQuasiIso R G (dgGluingChosenConeModuleMap R C D M Y Z f hC hD) :=
  dgGluingConeModuleMap_quasiIso R C D M Y Z f
    (dgGluingChooseConeRepresentative R C Y.left Z.left
      (dgGluingConeLeftArrow R C D M Y Z f) hC)
    (dgGluingChooseConeRepresentative R D Y.right Z.right
      ((dgYoneda R D).onClosed.map (dgGluingConeRightArrow R C D M Y Z f)) hD)

end SerrePositivity.InfinityCategories
