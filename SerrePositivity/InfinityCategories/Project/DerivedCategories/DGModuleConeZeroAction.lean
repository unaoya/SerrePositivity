module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGConeCoordinateTransport
public import SerrePositivity.DifferentialGraded.Module.Hom.HomotopyAndOperations
public import SerrePositivity.DifferentialGraded.Module.Basic

/-! # 加群 cone の次数零作用の二座標

概要：元の次数零射の作用で、加群 cone の二座標は各加群の作用に従う。
方針：加群 cone の作用を実対角 cochain と読み、二つの射影公式を適用する。
規約：全整数次数。使われ方：同じ閉細分による R・K の同時前合成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded HomologicalComplex CochainComplex HomComplex Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 加群 cone の次数零作用の第一座標は、元の第一座標への加群作用。 -/
lemma dgModuleConeZeroAction_fst {M N : ModuleCategory A D} (f : M ⟶ N)
    (x q : D) (s : GradedHom A q x 0) (n : ℤ)
    (z : ((moduleEvaluation A D x).obj (moduleCone A D f)).X n) :
    (mappingCone.fst ((moduleEvaluation A D q).map f)).val.v n (n + 1) rfl
      (moduleAction A (ForgetEnrichment.to (Complex A) (moduleCone A D f))
        (x := op x) (y := op q) s z (add_zero n)) =
      moduleAction A (ForgetEnrichment.to (Complex A) M) (x := op x) (y := op q) s
        ((mappingCone.fst ((moduleEvaluation A D x).map f)).val.v n (n + 1) rfl z)
        (add_zero (n + 1)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgConeZeroAction_fst ((moduleEvaluation A D x).map f) ((moduleEvaluation A D q).map f)
    (((ForgetEnrichment.to (Complex A) M).map (op x) (op q)).f 0 s)
    (((ForgetEnrichment.to (Complex A) N).map (op x) (op q)).f 0 s) n z

/-- 加群 cone の次数零作用の第二座標は、元の第二座標への加群作用。 -/
lemma dgModuleConeZeroAction_snd {M N : ModuleCategory A D} (f : M ⟶ N)
    (x q : D) (s : GradedHom A q x 0) (n : ℤ)
    (z : ((moduleEvaluation A D x).obj (moduleCone A D f)).X n) :
    (mappingCone.snd ((moduleEvaluation A D q).map f)).v n n (add_zero n)
      (moduleAction A (ForgetEnrichment.to (Complex A) (moduleCone A D f))
        (x := op x) (y := op q) s z (add_zero n)) =
      moduleAction A (ForgetEnrichment.to (Complex A) N) (x := op x) (y := op q) s
        ((mappingCone.snd ((moduleEvaluation A D x).map f)).v n n (add_zero n) z)
        (add_zero n) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgConeZeroAction_snd ((moduleEvaluation A D x).map f) ((moduleEvaluation A D q).map f)
    (((ForgetEnrichment.to (Complex A) M).map (op x) (op q)).f 0 s)
    (((ForgetEnrichment.to (Complex A) N).map (op x) (op q)).f 0 s) n z

end SerrePositivity.InfinityCategories.Project.DerivedCategories
