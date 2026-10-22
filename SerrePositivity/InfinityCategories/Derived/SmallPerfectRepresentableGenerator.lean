module
public import SerrePositivity.InfinityCategories.Derived.SmallPerfectEvaluationGenerator
public import SerrePositivity.InfinityCategories.Derived.SmallPerfectRepresentablePoint

/-!
概要：表現可能加群の実小代表の生成性と H⁰ 自由代表比較。
方針：既存の実評価・導来 tensor と完全加群の厚い閉包を使う。
規約：生成性の結論を追加仮定にしない。使われ方：β5 と K-S• の実自由代表。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
local notation "C" => SmallPerfectDGModuleOver R D Set.univ

def smallPerfectRepresentablePoint_evaluationIso (d : D) :
    (moduleToDerived R D).obj (ForgetEnrichment.of (Complex R)
      ((smallPerfectEvaluationBimodule R D).obj (smallPerfectRepresentablePoint R D d))) ≅
      (moduleToDerived R D).obj (ForgetEnrichment.of (Complex R) (representable R d)) :=
  ((moduleToHomotopyDerivedIso R D).app (ForgetEnrichment.of (Complex R)
    ((smallPerfectEvaluationBimodule R D).obj (smallPerfectRepresentablePoint R D d)))).symm ≪≫
      (perfectModuleInclusion R D Set.univ).mapIso
        (smallPerfectRepresentablePoint_comparison R D d)

lemma smallPerfectRepresentablePoint_generates (d : D)
    (hD : modulePerfectOver R D {d} = modulePerfect R D) :
    modulePerfectOver R (C) {smallPerfectRepresentablePoint R D d} = modulePerfect R (C) :=
  smallPerfectEvaluation_singleton_generates R D (smallPerfectRepresentablePoint R D d) d hD
    (smallPerfectRepresentablePoint_evaluationIso R D d)

lemma smallPerfectRepresentablePoint_generates_of_subsingleton [Subsingleton D] (d : D) :
    modulePerfectOver R (C) {smallPerfectRepresentablePoint R D d} = modulePerfect R (C) := by
  apply smallPerfectRepresentablePoint_generates R D d
  have hd : ({d} : Set D) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    exact Set.mem_singleton_iff.mpr (Subsingleton.elim x d)
  rw [hd]
  rfl

def smallPerfectRepresentablePoint_homotopyComparison (d : D) :
    (smallPerfectDGModuleInclusion R D Set.univ).onHomotopy.obj
      ((toHomotopy R (C)).obj (ForgetEnrichment.of (Complex R)
        (smallPerfectRepresentablePoint R D d))) ≅
      (toHomotopy R (PerfectDGModule R D)).obj (ForgetEnrichment.of (Complex R)
        (smallPerfectRepresentableDGPoint R D d)) :=
  (perfectDGModuleToDerived R D Set.univ).preimageIso
    ((perfectModuleInclusion R D Set.univ).mapIso
      (smallPerfectRepresentablePoint_comparison R D d) ≪≫
        ((moduleToHomotopyDerivedIso R D).app
          (ForgetEnrichment.of (Complex R) (representable R d))).symm)

end SerrePositivity.InfinityCategories
