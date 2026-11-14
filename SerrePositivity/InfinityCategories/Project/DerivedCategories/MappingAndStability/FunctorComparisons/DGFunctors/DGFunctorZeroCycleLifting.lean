module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.DGFunctors.DGFunctorHomologyDetection
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.FunctorMapping
/-!
概要：H⁰ の充満忠実性を実次数零 cochain の持ち上げと境界の反映へ移す。
方針：元の cycle と境界原始元を保持した商の比較を使う。
規約：全次数の検査を省かない。使われ方：一般 Morita の全 Hom 比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) (E : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [DGCategory R E]
/-- 元の閉 cochain と境界原始元による検出。 -/
lemma dgFunctor_zero_cycle_lift (G : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C E) [G.onHomotopy.Full]
    (x y : C) (a : GradedHom R (G.obj x) (G.obj y) 0) (ha : differential R a = 0) :
    ∃ b : GradedHom R x y 0, differential R b = 0 ∧
      ∃ h : GradedHom R (G.obj x) (G.obj y) (-1),
        (homObject R E (G.obj x) (G.obj y)).d (-1) 0 h = a - (G.map x y).f 0 b := by
  let ac : zeroCycles (homObject R E (G.obj x) (G.obj y)) := ⟨a, ha⟩
  let acl : ForgetEnrichment.of (Complex R) (G.obj x) ⟶
      ForgetEnrichment.of (Complex R) (G.obj y) := (closedHomEquiv R E
      (ForgetEnrichment.of (Complex R) (G.obj x))
      (ForgetEnrichment.of (Complex R) (G.obj y))).symm ac
  obtain ⟨bH, hbH⟩ := G.onHomotopy.map_surjective
    (X := (toHomotopy R C).obj (ForgetEnrichment.of (Complex R) x))
    (Y := (toHomotopy R C).obj (ForgetEnrichment.of (Complex R) y))
    ((toHomotopy R E).map acl)
  obtain ⟨b, rfl⟩ := (toHomotopy R C).map_surjective bH
  change (toHomotopy R E).map (G.onClosed.map b) = (toHomotopy R E).map acl at hbH
  obtain ⟨h, hh⟩ := (toHomotopy_map_eq_iff_boundary R E acl (G.onClosed.map b)).mp hbH.symm
  let bc := closedHomEquiv R C
      (ForgetEnrichment.of (Complex R) x) (ForgetEnrichment.of (Complex R) y) b
  refine ⟨bc.val, bc.property, h, ?_⟩
  change (homObject R E (G.obj x) (G.obj y)).d (-1) 0 h =
    ((closedHomEquiv R E
      (ForgetEnrichment.of (Complex R) (G.obj x))
      (ForgetEnrichment.of (Complex R) (G.obj y)) acl).val :
        GradedHom R (G.obj x) (G.obj y) 0) -
    ((closedHomEquiv R E
      (ForgetEnrichment.of (Complex R) (G.obj x))
      (ForgetEnrichment.of (Complex R) (G.obj y)) (G.onClosed.map b)).val :
        GradedHom R (G.obj x) (G.obj y) 0) at hh
  erw [DGFunctor.closedHomEquiv_map] at hh
  simpa only [acl, Equiv.apply_symm_apply, ac, bc, complexMapZeroCycle] using! hh

/-- 元の閉 cochain と境界原始元による検出。 -/
lemma dgFunctor_zero_boundary_reflect (G : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C E) [G.onHomotopy.Faithful]
    (x y : C) (a : GradedHom R x y 0) (ha : differential R a = 0)
    (h : GradedHom R (G.obj x) (G.obj y) (-1))
    (hh : (homObject R E (G.obj x) (G.obj y)).d (-1) 0 h = (G.map x y).f 0 a) :
    ∃ k : GradedHom R x y (-1), (homObject R C x y).d (-1) 0 k = a := by
  let ac : zeroCycles (homObject R C x y) := ⟨a, ha⟩
  let zc : zeroCycles (homObject R C x y) := ⟨0, by simp⟩
  let acl : ForgetEnrichment.of (Complex R) x ⟶ ForgetEnrichment.of (Complex R) y :=
    (closedHomEquiv R C
      (ForgetEnrichment.of (Complex R) x) (ForgetEnrichment.of (Complex R) y)).symm ac
  let zcl : ForgetEnrichment.of (Complex R) x ⟶ ForgetEnrichment.of (Complex R) y :=
    (closedHomEquiv R C
      (ForgetEnrichment.of (Complex R) x) (ForgetEnrichment.of (Complex R) y)).symm zc
  have ht : (toHomotopy R E).map (G.onClosed.map acl) =
      (toHomotopy R E).map (G.onClosed.map zcl) := by
    apply (toHomotopy_map_eq_iff_boundary R E _ _).mpr
    refine ⟨h, ?_⟩
    change (homObject R E (G.obj x) (G.obj y)).d (-1) 0 h =
      ((closedHomEquiv R E
      (ForgetEnrichment.of (Complex R) (G.obj x))
      (ForgetEnrichment.of (Complex R) (G.obj y)) (G.onClosed.map acl)).val :
        GradedHom R (G.obj x) (G.obj y) 0) -
      ((closedHomEquiv R E
      (ForgetEnrichment.of (Complex R) (G.obj x))
      (ForgetEnrichment.of (Complex R) (G.obj y)) (G.onClosed.map zcl)).val :
        GradedHom R (G.obj x) (G.obj y) 0)
    erw [DGFunctor.closedHomEquiv_map, DGFunctor.closedHomEquiv_map]
    dsimp only [acl, zcl]
    erw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    change _ = (G.map x y).f 0 a - (G.map x y).f 0 0
    rw [map_zero, sub_zero]
    exact hh
  have hs : (toHomotopy R C).map acl = (toHomotopy R C).map zcl := by
    apply G.onHomotopy.map_injective
    exact ht
  obtain ⟨k, hk⟩ := (toHomotopy_map_eq_iff_boundary R C acl zcl).mp hs
  refine ⟨k, ?_⟩
  change (homObject R C x y).d (-1) 0 k =
    ((closedHomEquiv R C
      (ForgetEnrichment.of (Complex R) x) (ForgetEnrichment.of (Complex R) y) acl).val :
        GradedHom R x y 0) -
    ((closedHomEquiv R C
      (ForgetEnrichment.of (Complex R) x) (ForgetEnrichment.of (Complex R) y) zcl).val :
        GradedHom R x y 0) at hk
  simpa only [acl, zcl, Equiv.apply_symm_apply, ac, zc, sub_zero] using hk
end SerrePositivity.InfinityCategories.Project.DerivedCategories
