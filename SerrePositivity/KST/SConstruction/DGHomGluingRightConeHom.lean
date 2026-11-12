module
public import SerrePositivity.KST.SConstruction.DGHomGluingConeHomMap
public import SerrePositivity.KST.SConstruction.DGPerfectEndIsoComparison
public import SerrePositivity.KST.SConstruction.DGHomGluingRightCone
public import SerrePositivity.KST.SConstruction.DGHomGluingModuleConeConjugation
public import SerrePositivity.DifferentialGraded.Complexes.Perturbation

/-! # 元の右 cone 閉同型を通した全 Hom の回収
概要：同じ右軸の実 cone Hom を共役すると、元の右 Hom 射影の像を回収する。
方針：標準右包含への制限で二成分を消し、元の Yoneda Hom 同型で戻す。
規約：全 Hom 上の等号を保持。使われ方：元の右端の商 End 比較との整合性。
-/
@[expose] public section
noncomputable section
universe u v w z
namespace SerrePositivity.KST.SConstruction
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (R : Type u) [CommRing R] (E : Type z) [DGCategory R E] [Small.{u} E]
  (C : Type v) [DGCategory R C] [Small.{u} C] (D : Type w) [DGCategory R D]
  (p : DGFunctor R C E) (q : DGFunctor R D E)
  (c : C) (hc : CategoryTheory.Limits.IsZero (ForgetEnrichment.of (Complex R) c)) (b : D)
local notation "M" => dgHomGluingBimodule R C D E p q
local notation "X" => dgGluingRightAxisObject R C D (M) c b
local notation "e" => dgHomGluingRightConeIso R E C D p q c hc b

/-- 元の右 cone の閉同型による共役は、同じ実右 Hom 成分そのものを回収する。 -/
lemma dgHomGluingRightConeHom_conjugate :
    dgHomGluingConeHomMap R C D E p q (X) (X) ≫
      dgEndIsoHom R (D := RightModule R E) (e) =
        dgHomGluingConeRightMap R C D E p q (X) (X) := by
  apply chain_ext_apply
  intro n a
  change (dgEndIsoHom R (D := RightModule R E) (e)).f n
    ((dgHomGluingConeHomMap R C D E p q (X) (X)).f n a) = _
  rw [dgHomGluingConeHomMap_apply]
  exact dgGluingModuleConeElement_conjugate R E
    (dgHomGluingTargetModuleMap R C D E p q (X)) (e) rfl
    (n := n) (m := n - 1)
    ((dgHomGluingConeLeftMap R C D E p q (X) (X)).f n a)
    ((dgHomGluingConeRightMap R C D E p q (X) (X)).f n a)
    ((dgHomGluingConePrimitive R C D E p q (X) (X)).v n (n - 1) (by omega) a) (by omega)

/-- 同じ右 Hom 成分を元の Yoneda 逆同型で戻すと、元の右射影と q の像を回収する。 -/
lemma dgHomGluingRightConeHom_yoneda :
    dgHomGluingConeRightMap R C D E p q (X) (X) ≫
      (dgYonedaIso R (q.obj b) (representable R (q.obj b))).hom =
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightHomMap R C D (M) (X) (X) ≫ q.map b b := by
  change ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightHomMap R C D (M) (X) (X) ≫ q.map b b) ≫
    (dgYonedaIso R (q.obj b) (representable R (q.obj b))).inv) ≫ _ = _
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- 型を固定した実 End 比較は、元の右 Hom 射影と同じ q の全 Hom 作用を回収する。 -/
lemma dgHomGluingRightConeHom_object :
    dgHomGluingConeHomMap R C D E p q (X) (X) ≫
      dgPerfectEndIsoObjectHom R E (dgHomGluingTargetCone R C D E p q (X)) (q.obj b) (e) =
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightHomMap R C D (M) (X) (X) ≫ q.map b b := by
  change dgHomGluingConeHomMap R C D E p q (X) (X) ≫
    (dgEndIsoHom R (D := RightModule R E) (e) ≫
      (dgYonedaIso R (q.obj b) (representable R (q.obj b))).hom) = _
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫ (dgYonedaIso R (q.obj b) (representable R (q.obj b))).hom)
      (dgHomGluingRightConeHom_conjugate R E C D p q c hc b)).trans
      (dgHomGluingRightConeHom_yoneda R E C D p q c b))

end SerrePositivity.KST.SConstruction
