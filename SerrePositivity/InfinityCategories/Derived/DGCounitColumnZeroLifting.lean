module
public import SerrePositivity.InfinityCategories.Derived.DGCounitColumn
public import SerrePositivity.InfinityCategories.Derived.DGClosedPostcompositionComponents
public import SerrePositivity.DifferentialGraded.Functor.QuasiEquivalence
/-!
概要：同じ余単位の H⁰ 普遍性を、実次数零 cycle の持ち上げと境界反映へ移す。
方針：閉射の同じ合成と Hom の商の代表を使い、実境界原始元を回収する。
規約：元の dg 関手と実余単位を保持する。使われ方：全次数の準同型性の検査。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (C : Type v) (E : Type w)
  [DGCategory R C] [DGCategory R E]
variable (G : DGFunctor R C E) {t : C} {y : E}
  (ε : ForgetEnrichment.of (Complex R) (G.obj t) ⟶ ForgetEnrichment.of (Complex R) y)
/-- 同じ閉 cycle による後合成は標準豊穣後合成そのもの。 -/
lemma dgCyclePostcomposition_eq_closed {a b c : E}
    (e : ForgetEnrichment.of (Complex R) b ⟶ ForgetEnrichment.of (Complex R) c) :
    dgCyclePostcomposition R E a (closedHomEquiv R E _ _ e) =
      dgClosedPostcomposition R E (x := a) e := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  exact (dgClosedPostcomposition_f R E (x := a) (y := b) (z := c) e n f).symm
/-- 余単位の実 Hom 鎖写像は、同じ閉射の合成を回収する。 -/
lemma dgCounitColumn_closedCycle (x : C)
    (f : ForgetEnrichment.of (Complex R) x ⟶ ForgetEnrichment.of (Complex R) t) :
    complexMapZeroCycle R (dgCounitColumn R C E G (t := t) (y := y) (closedHomEquiv R E
      (ForgetEnrichment.of (Complex R) (G.obj t)) (ForgetEnrichment.of (Complex R) y) ε) x)
      (closedHomEquiv R C
      (ForgetEnrichment.of (Complex R) x) (ForgetEnrichment.of (Complex R) t) f) =
    closedHomEquiv R E
      (ForgetEnrichment.of (Complex R) (G.obj x)) (ForgetEnrichment.of (Complex R) y)
      (G.onClosed.map f ≫ ε) := by
  unfold dgCounitColumn
  erw [dgCyclePostcomposition_eq_closed]
  change complexMapZeroCycle R (dgClosedPostcomposition R E ε)
    (complexMapZeroCycle R (G.map x t) (closedHomEquiv R C
      (ForgetEnrichment.of (Complex R) x) (ForgetEnrichment.of (Complex R) t) f)) = _
  erw [← DGFunctor.closedHomEquiv_map]
  exact closedHomEquiv_postcompose R E (G.onClosed.map f) ε
/-- 余単位の H⁰ 全射性から、実零 cycle の持ち上げと境界原始元を得る。 -/
lemma dgCounitColumn_zero_cycle_lift
    (hs : ∀ x : C, Function.Surjective (fun f :
      (toHomotopy R C).obj (ForgetEnrichment.of (Complex R) x) ⟶
        (toHomotopy R C).obj (ForgetEnrichment.of (Complex R) t) =>
      G.onHomotopy.map f ≫ (toHomotopy R E).map ε))
    (x : C) (a : GradedHom R (G.obj x) y 0) (ha : differential R a = 0) :
    ∃ b : GradedHom R x t 0, differential R b = 0 ∧
      ∃ h : GradedHom R (G.obj x) y (-1),
        (homObject R E (G.obj x) y).d (-1) 0 h =
          a - (dgCounitColumn R C E G (t := t) (y := y) (closedHomEquiv R E
      (ForgetEnrichment.of (Complex R) (G.obj t))
      (ForgetEnrichment.of (Complex R) y) ε) x).f 0 b := by
  let ac : zeroCycles (homObject R E (G.obj x) y) := ⟨a, ha⟩
  let acl := (closedHomEquiv R E
    (ForgetEnrichment.of (Complex R) (G.obj x)) (ForgetEnrichment.of (Complex R) y)).symm ac
  obtain ⟨bH, hbH⟩ := hs x ((toHomotopy R E).map acl)
  obtain ⟨b, rfl⟩ := (toHomotopy R C).map_surjective bH
  change (toHomotopy R E).map (G.onClosed.map b) ≫ (toHomotopy R E).map ε = _ at hbH
  rw [← Functor.map_comp] at hbH
  obtain ⟨h, hh⟩ :=
    (toHomotopy_map_eq_iff_boundary R E acl (G.onClosed.map b ≫ ε)).mp hbH.symm
  let bc := closedHomEquiv R C
    (ForgetEnrichment.of (Complex R) x) (ForgetEnrichment.of (Complex R) t) b
  refine ⟨bc.val, bc.property, h, ?_⟩
  have he := congrArg Subtype.val (dgCounitColumn_closedCycle R C E G ε x b)
  change (dgCounitColumn R C E G (t := t) (y := y) (closedHomEquiv R E
      (ForgetEnrichment.of (Complex R) (G.obj t))
      (ForgetEnrichment.of (Complex R) y) ε) x).f 0 bc.val = _ at he
  rw [he]
  change (homObject R E (G.obj x) y).d (-1) 0 h =
    ((closedHomEquiv R E (ForgetEnrichment.of (Complex R) (G.obj x))
      (ForgetEnrichment.of (Complex R) y) acl).val : GradedHom R (G.obj x) y 0) -
    ((closedHomEquiv R E (ForgetEnrichment.of (Complex R) (G.obj x))
      (ForgetEnrichment.of (Complex R) y) (G.onClosed.map b ≫ ε)).val :
        GradedHom R (G.obj x) y 0) at hh
  simpa only [acl, Equiv.apply_symm_apply, ac] using! hh
/-- 余単位の H⁰ 単射性から、実零 cycle の境界原始元を反映する。 -/
lemma dgCounitColumn_zero_boundary_reflect
    (hi : ∀ x : C, Function.Injective (fun f :
      (toHomotopy R C).obj (ForgetEnrichment.of (Complex R) x) ⟶
        (toHomotopy R C).obj (ForgetEnrichment.of (Complex R) t) =>
      G.onHomotopy.map f ≫ (toHomotopy R E).map ε))
    (x : C) (a : GradedHom R x t 0) (ha : differential R a = 0)
    (h : GradedHom R (G.obj x) y (-1))
    (hh : (homObject R E (G.obj x) y).d (-1) 0 h =
      (dgCounitColumn R C E G (t := t) (y := y) (closedHomEquiv R E
      (ForgetEnrichment.of (Complex R) (G.obj t)) (ForgetEnrichment.of (Complex R) y) ε) x).f 0 a) :
    ∃ k : GradedHom R x t (-1), (homObject R C x t).d (-1) 0 k = a := by
  let ac : zeroCycles (homObject R C x t) := ⟨a, ha⟩
  let zc : zeroCycles (homObject R C x t) := ⟨0, by simp⟩
  let acl := (closedHomEquiv R C
    (ForgetEnrichment.of (Complex R) x) (ForgetEnrichment.of (Complex R) t)).symm ac
  let zcl := (closedHomEquiv R C
    (ForgetEnrichment.of (Complex R) x) (ForgetEnrichment.of (Complex R) t)).symm zc
  have ht : (toHomotopy R E).map (G.onClosed.map acl ≫ ε) =
      (toHomotopy R E).map (G.onClosed.map zcl ≫ ε) := by
    apply (toHomotopy_map_eq_iff_boundary R E _ _).mpr
    refine ⟨h, ?_⟩
    change (homObject R E (G.obj x) y).d (-1) 0 h =
      ((closedHomEquiv R E (ForgetEnrichment.of (Complex R) (G.obj x))
        (ForgetEnrichment.of (Complex R) y) (G.onClosed.map acl ≫ ε)).val :
          GradedHom R (G.obj x) y 0) -
      ((closedHomEquiv R E (ForgetEnrichment.of (Complex R) (G.obj x))
        (ForgetEnrichment.of (Complex R) y) (G.onClosed.map zcl ≫ ε)).val :
          GradedHom R (G.obj x) y 0)
    erw [← dgCounitColumn_closedCycle R C E G ε x acl,
      ← dgCounitColumn_closedCycle R C E G ε x zcl]
    dsimp only [acl, zcl]
    erw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    change _ = (dgCounitColumn R C E G (t := t) (y := y) (closedHomEquiv R E
      (ForgetEnrichment.of (Complex R) (G.obj t)) (ForgetEnrichment.of (Complex R) y) ε) x).f 0 a -
      (dgCounitColumn R C E G (t := t) (y := y) (closedHomEquiv R E
      (ForgetEnrichment.of (Complex R) (G.obj t)) (ForgetEnrichment.of (Complex R) y) ε) x).f 0 0
    rw [map_zero, sub_zero]
    exact hh
  have ht' : (toHomotopy R C).map acl = (toHomotopy R C).map zcl := by
    apply hi x
    simpa only [Functor.map_comp] using! ht
  obtain ⟨k, hk⟩ := (toHomotopy_map_eq_iff_boundary R C acl zcl).mp ht'
  refine ⟨k, ?_⟩
  change (homObject R C x t).d (-1) 0 k =
    ((closedHomEquiv R C (ForgetEnrichment.of (Complex R) x)
      (ForgetEnrichment.of (Complex R) t) acl).val : GradedHom R x t 0) -
    ((closedHomEquiv R C (ForgetEnrichment.of (Complex R) x)
      (ForgetEnrichment.of (Complex R) t) zcl).val : GradedHom R x t 0) at hk
  simpa only [acl, zcl, Equiv.apply_symm_apply, ac, zc, sub_zero] using! hk
end SerrePositivity.InfinityCategories
