module
public import SerrePositivity.DifferentialGraded.Bimodule.LeftEvaluation

/-! # 閉零bimodule恒等射の値の成分 -/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.DifferentialGraded.BimoduleCategory
open CategoryTheory HomologicalComplex
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B]

lemma valueMap_id_apply (M : BimoduleCategory A B C) (b : B) (c : C) (n : ℤ)
    (v : ((underlying A B C M).value b c).X n) :
    ((valueEvaluation A B C b c).map (𝟙 M)).f n v = v :=
  (congrArg (fun k : (underlying A B C M).value b c ⟶
      (underlying A B C M).value b c => k.f n v)
    ((valueEvaluation A B C b c).map_id M)).trans (by rfl)

end SerrePositivity.DifferentialGraded.BimoduleCategory
