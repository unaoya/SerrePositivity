module

public import SerrePositivity.EInfinity.ComplexLimits.SemifreeResolutionAugmentation
public import SerrePositivity.InfinityCategories.Derived.DGModuleOutputResolutionAugmentation
public import SerrePositivity.DifferentialGraded.Derived.Ring

/-!
# 既存 D(R) 値解像の同じ実値と元の複体への準同型

概要：全 ∞ 関手の同じ値を実半自由複体として回収し、元の複体へ増大する。
方針：同じ厳密切断の出力と元の augmentation を一点評価する。
規約：値も分解も選び直さず、元の複体を厳密な終域とする。
使われ方：U の同じ実値と元の底の複体の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.ComplexLimits
open SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
open scoped Simplicial
variable (A : Type u) [CommRing A]

def complexSemifreeResolutionValue (X : Complex A) : Semifree A :=
  (semifreeRingEvaluationDG A).obj
    (dgModuleOutputResolutionValue A (Complex A) PUnit.{1} (ringConstantDG A) X)

def complexSemifreeResolutionValueAugmentation (X : Complex A) :
    (complexSemifreeResolutionValue A X).val ⟶ X :=
  (moduleEvaluation A PUnit.{1} PUnit.unit).map
    (dgModuleOutputResolutionAugmentation A (Complex A) PUnit.{1} (ringConstantDG A) X)

lemma complexSemifreeResolutionValueAugmentation_quasiIso (X : Complex A) :
    QuasiIso (complexSemifreeResolutionValueAugmentation A X) :=
  dgModuleOutputResolutionAugmentation_quasiIso A (Complex A) PUnit.{1}
    (ringConstantDG A) X PUnit.unit

lemma complexSemifreeResolutionInfinity_vertex (X : Complex A) :
    (complexSemifreeResolutionInfinity A).app (Opposite.op ⦋0⦌) (Simplex.vertex X) =
      Simplex.vertex (complexSemifreeResolutionValue A X) := by
  apply (Simplex.vertexEquiv (A := A) (D := Semifree A)).injective
  rfl

end SerrePositivity.EInfinity.ComplexLimits
