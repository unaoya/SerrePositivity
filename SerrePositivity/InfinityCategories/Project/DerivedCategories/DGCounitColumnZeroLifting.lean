module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGCounitColumn
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedPostcompositionComponents
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) (E : Type w)
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E]
variable (G : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C E) {t : C} {y : E}
  (ε : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (G.obj t) ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) y)
/-- 同じ閉 cycle による後合成は標準豊穣後合成そのもの。 -/
lemma dgCyclePostcomposition_eq_closed {a b c : E}
    (e : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) b ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) c) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCyclePostcomposition R E a (closedHomEquiv R E _ _ e) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPostcomposition R E (x := a) e := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPostcomposition_f R E (x := a) (y := b) (z := c) e n f).symm
/-- 余単位の実 Hom 鎖写像は、同じ閉射の合成を回収する。 -/
lemma dgCounitColumn_closedCycle (x : C)
    (f : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) x ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) t) :
    complexMapZeroCycle R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCounitColumn R C E G (t := t) (y := y) (closedHomEquiv R E
      (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (G.obj t)) (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) y) ε) x)
      (_root_.SerrePositivity.DifferentialGraded.closedHomEquiv R C
      (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) x) (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) t) f) =
    _root_.SerrePositivity.DifferentialGraded.closedHomEquiv R E
      (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (G.obj x)) (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) y)
      (G.onClosed.map f ≫ ε) := by
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCounitColumn
  erw [dgCyclePostcomposition_eq_closed]
  change complexMapZeroCycle R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPostcomposition R E ε)
    (_root_.SerrePositivity.DifferentialGraded.complexMapZeroCycle R (G.map x t) (_root_.SerrePositivity.DifferentialGraded.closedHomEquiv R C
      (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) x) (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) t) f)) = _
  erw [← _root_.SerrePositivity.DifferentialGraded.DGFunctor.closedHomEquiv_map]
  exact _root_.SerrePositivity.DifferentialGraded.closedHomEquiv_postcompose R E (G.onClosed.map f) ε
/-- 余単位の H⁰ 全射性から、実零 cycle の持ち上げと境界原始元を得る。 -/
lemma dgCounitColumn_zero_cycle_lift
    (hs : ∀ x : C, Function.Surjective (fun f :
      (_root_.SerrePositivity.DifferentialGraded.toHomotopy R C).obj (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) x) ⟶
        (_root_.SerrePositivity.DifferentialGraded.toHomotopy R C).obj (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) t) =>
      G.onHomotopy.map f ≫ (_root_.SerrePositivity.DifferentialGraded.toHomotopy R E).map ε))
    (x : C) (a : _root_.SerrePositivity.DifferentialGraded.GradedHom R (G.obj x) y 0) (ha : _root_.SerrePositivity.DifferentialGraded.differential R a = 0) :
    ∃ b : _root_.SerrePositivity.DifferentialGraded.GradedHom R x t 0, _root_.SerrePositivity.DifferentialGraded.differential R b = 0 ∧
      ∃ h : _root_.SerrePositivity.DifferentialGraded.GradedHom R (G.obj x) y (-1),
        (_root_.SerrePositivity.DifferentialGraded.homObject R E (G.obj x) y).d (-1) 0 h =
          a - (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCounitColumn R C E G (t := t) (y := y) (closedHomEquiv R E
      (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (G.obj t))
      (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) y) ε) x).f 0 b := by
  let ac : _root_.SerrePositivity.DifferentialGraded.zeroCycles (_root_.SerrePositivity.DifferentialGraded.homObject R E (G.obj x) y) := ⟨a, ha⟩
  let acl := (_root_.SerrePositivity.DifferentialGraded.closedHomEquiv R E
    (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (G.obj x)) (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) y)).symm ac
  obtain ⟨bH, hbH⟩ := hs x ((_root_.SerrePositivity.DifferentialGraded.toHomotopy R E).map acl)
  obtain ⟨b, rfl⟩ := (_root_.SerrePositivity.DifferentialGraded.toHomotopy R C).map_surjective bH
  change (_root_.SerrePositivity.DifferentialGraded.toHomotopy R E).map (G.onClosed.map b) ≫ (_root_.SerrePositivity.DifferentialGraded.toHomotopy R E).map ε = _ at hbH
  rw [← Functor.map_comp] at hbH
  obtain ⟨h, hh⟩ :=
    (_root_.SerrePositivity.DifferentialGraded.toHomotopy_map_eq_iff_boundary R E acl (G.onClosed.map b ≫ ε)).mp hbH.symm
  let bc := _root_.SerrePositivity.DifferentialGraded.closedHomEquiv R C
    (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) x) (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) t) b
  refine ⟨bc.val, bc.property, h, ?_⟩
  have he := congrArg Subtype.val (dgCounitColumn_closedCycle R C E G ε x b)
  change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCounitColumn R C E G (t := t) (y := y) (closedHomEquiv R E
      (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (G.obj t))
      (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) y) ε) x).f 0 bc.val = _ at he
  rw [he]
  change (_root_.SerrePositivity.DifferentialGraded.homObject R E (G.obj x) y).d (-1) 0 h =
    ((_root_.SerrePositivity.DifferentialGraded.closedHomEquiv R E (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (G.obj x))
      (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) y) acl).val : _root_.SerrePositivity.DifferentialGraded.GradedHom R (G.obj x) y 0) -
    ((_root_.SerrePositivity.DifferentialGraded.closedHomEquiv R E (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (G.obj x))
      (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) y) (G.onClosed.map b ≫ ε)).val :
        _root_.SerrePositivity.DifferentialGraded.GradedHom R (G.obj x) y 0) at hh
  simpa only [acl, Equiv.apply_symm_apply, ac] using! hh
/-- 余単位の H⁰ 単射性から、実零 cycle の境界原始元を反映する。 -/
lemma dgCounitColumn_zero_boundary_reflect
    (hi : ∀ x : C, Function.Injective (fun f :
      (_root_.SerrePositivity.DifferentialGraded.toHomotopy R C).obj (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) x) ⟶
        (_root_.SerrePositivity.DifferentialGraded.toHomotopy R C).obj (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) t) =>
      G.onHomotopy.map f ≫ (_root_.SerrePositivity.DifferentialGraded.toHomotopy R E).map ε))
    (x : C) (a : _root_.SerrePositivity.DifferentialGraded.GradedHom R x t 0) (ha : _root_.SerrePositivity.DifferentialGraded.differential R a = 0)
    (h : _root_.SerrePositivity.DifferentialGraded.GradedHom R (G.obj x) y (-1))
    (hh : (_root_.SerrePositivity.DifferentialGraded.homObject R E (G.obj x) y).d (-1) 0 h =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCounitColumn R C E G (t := t) (y := y) (closedHomEquiv R E
      (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (G.obj t)) (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) y) ε) x).f 0 a) :
    ∃ k : _root_.SerrePositivity.DifferentialGraded.GradedHom R x t (-1), (_root_.SerrePositivity.DifferentialGraded.homObject R C x t).d (-1) 0 k = a := by
  let ac : _root_.SerrePositivity.DifferentialGraded.zeroCycles (_root_.SerrePositivity.DifferentialGraded.homObject R C x t) := ⟨a, ha⟩
  let zc : _root_.SerrePositivity.DifferentialGraded.zeroCycles (_root_.SerrePositivity.DifferentialGraded.homObject R C x t) := ⟨0, by simp⟩
  let acl := (_root_.SerrePositivity.DifferentialGraded.closedHomEquiv R C
    (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) x) (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) t)).symm ac
  let zcl := (_root_.SerrePositivity.DifferentialGraded.closedHomEquiv R C
    (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) x) (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) t)).symm zc
  have ht : (_root_.SerrePositivity.DifferentialGraded.toHomotopy R E).map (G.onClosed.map acl ≫ ε) =
      (_root_.SerrePositivity.DifferentialGraded.toHomotopy R E).map (G.onClosed.map zcl ≫ ε) := by
    apply (_root_.SerrePositivity.DifferentialGraded.toHomotopy_map_eq_iff_boundary R E _ _).mpr
    refine ⟨h, ?_⟩
    change (_root_.SerrePositivity.DifferentialGraded.homObject R E (G.obj x) y).d (-1) 0 h =
      ((_root_.SerrePositivity.DifferentialGraded.closedHomEquiv R E (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (G.obj x))
        (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) y) (G.onClosed.map acl ≫ ε)).val :
          _root_.SerrePositivity.DifferentialGraded.GradedHom R (G.obj x) y 0) -
      ((_root_.SerrePositivity.DifferentialGraded.closedHomEquiv R E (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (G.obj x))
        (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) y) (G.onClosed.map zcl ≫ ε)).val :
          _root_.SerrePositivity.DifferentialGraded.GradedHom R (G.obj x) y 0)
    erw [← dgCounitColumn_closedCycle R C E G ε x acl,
      ← dgCounitColumn_closedCycle R C E G ε x zcl]
    dsimp only [acl, zcl]
    erw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    change _ = (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCounitColumn R C E G (t := t) (y := y) (closedHomEquiv R E
      (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (G.obj t)) (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) y) ε) x).f 0 a -
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCounitColumn R C E G (t := t) (y := y) (closedHomEquiv R E
      (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (G.obj t)) (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) y) ε) x).f 0 0
    rw [map_zero, sub_zero]
    exact hh
  have ht' : (_root_.SerrePositivity.DifferentialGraded.toHomotopy R C).map acl = (_root_.SerrePositivity.DifferentialGraded.toHomotopy R C).map zcl := by
    apply hi x
    simpa only [Functor.map_comp] using! ht
  obtain ⟨k, hk⟩ := (_root_.SerrePositivity.DifferentialGraded.toHomotopy_map_eq_iff_boundary R C acl zcl).mp ht'
  refine ⟨k, ?_⟩
  change (_root_.SerrePositivity.DifferentialGraded.homObject R C x t).d (-1) 0 k =
    ((_root_.SerrePositivity.DifferentialGraded.closedHomEquiv R C (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) x)
      (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) t) acl).val : _root_.SerrePositivity.DifferentialGraded.GradedHom R x t 0) -
    ((_root_.SerrePositivity.DifferentialGraded.closedHomEquiv R C (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) x)
      (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) t) zcl).val : _root_.SerrePositivity.DifferentialGraded.GradedHom R x t 0) at hk
  simpa only [acl, zcl, Equiv.apply_symm_apply, ac, zc, sub_zero] using! hk
end SerrePositivity.InfinityCategories.Project.DerivedCategories
