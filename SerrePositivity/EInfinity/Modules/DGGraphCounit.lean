module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniversalCounitInterval
public import SerrePositivity.DifferentialGraded.Derived.FunctorExtensionAdjunction
public import SerrePositivity.DifferentialGraded.Module.ShiftResolution

/-!
# graph 延長の同じ余単位の全次数の普遍性

概要：HA §4.2.3 の dg 延長・制限の指定余単位が全 Hom 複体で準同型を与える。
方針：既存の H⁰ 随伴と実斉次シフトで全整数次数を検出する。
規約：元の余単位を選び直さず、源の対象の小ささは仮定しない。
使われ方：解像度付き restriction と native な右随伴の比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.EInfinity.Modules
open CategoryTheory
open SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Project.DerivedCategories
/-- 概要：通常の随伴の余単位表示は全単射（HA §4.2.3）。
方針：既存の随伴の定義式を使う。規約：同じ成分。使われ方：指定 graph 余単位の照合。 -/
private lemma counitBijection {C T : Type*} [Category C] [Category T]
    {L : C ⥤ T} {R : T ⥤ C} (adj : L ⊣ R) (x : C) (y : T) :
    Function.Bijective (fun f : x ⟶ R.obj y => L.map f ≫ adj.counit.app y) := by
  have h : ((adj.homEquiv x y).symm : _ → _) =
      (fun f => L.map f ≫ adj.counit.app y) := by
    funext f
    exact Adjunction.homEquiv_counit adj x y f
  rw [← h]
  exact (adj.homEquiv x y).symm.bijective

/-- 概要：右関手の同型に沿う随伴の余単位表示（HA §4.2.3）。
方針：既存の随伴の定義式を使う。規約：同じ成分。使われ方：指定 graph 余単位の照合。 -/
private lemma transportedCounit {C T : Type*} [Category C] [Category T]
    {L : C ⥤ T} {R R' : T ⥤ C} (adj : L ⊣ R) (e : R ≅ R') (y : T) :
    (adj.ofNatIsoRight e).counit.app y = L.map (e.inv.app y) ≫ adj.counit.app y := rfl

/-- 概要：関手の等式が定める同型の成分（HA §4.2.3）。
方針：既存の随伴の定義式を使う。規約：同じ成分。使われ方：指定 graph 余単位の照合。 -/
private lemma functorEqIso_hom_app {C T : Type*} [Category C] [Category T]
    {F G : C ⥤ T} (h : F = G) (x : C) :
    (eqToIso h).hom.app x = eqToHom (congrArg (fun H => H.obj x) h) := by
  cases h
  rfl

variable (A : Type u) [CommRing A]
variable (D E : Type v) [DGCategory A D] [Small.{u} D] [DGCategory A E] [Small.{u} E]

/-- 概要：生の dg 加群のシフトは実斉次閉射で逆を持つ（HA §1.3.1）。
方針：既存のシフトの入射・出射とその厳密な単位則を使う。
規約：境界原始元は零。使われ方：H⁰ の普遍性の全次数検出。 -/
lemma moduleGradedShiftWitness (M : RightModule A D) (s : ℤ) :
    ∃ (N : RightModule A D) (f : GradedHom A M N (-s)) (g : GradedHom A N M s),
      differential A f = 0 ∧ differential A g = 0 ∧
      ∃ h : GradedHom A M M (-1),
        (homObject A (RightModule A D) M M).d (-1) 0 h =
          compose A g f (neg_add_cancel s) - (unitElement A M).val := by
  refine ⟨shiftModule s M, moduleShiftInElement A D s M, moduleShiftOutElement A D s M,
    moduleShiftInElement_d A D s M, moduleShiftOutElement_d A D s M, 0, ?_⟩
  rw [map_zero, moduleShiftInOut, sub_self]

/-- 概要：同じ graph 余単位は H⁰ の Hom 対応を与える（HA §4.2.3）。
方針：既存の随伴の Hom 同値を、指定された余単位の式で表示する。
規約：元の閉射を保つ。使われ方：全 Hom 準同型性の入力。 -/
lemma graphCounit_homotopy_bijective (F : DGFunctor A D E) (M : RightModule A E)
    (P : RightModule A D) :
    Function.Bijective (fun f :
      (toHomotopy A (RightModule A D)).obj (ForgetEnrichment.of (Complex A) P) ⟶
        (toHomotopy A (RightModule A D)).obj
          (ForgetEnrichment.of (Complex A) (restrictModule A D E F.op M)) =>
      (dgModuleExtension A D E F).onHomotopy.map f ≫
        (toHomotopy A (RightModule A E)).map (functorExtensionCounit A D E F M)) := by
  have hc : (dgModuleEnrichedRestrictionAdjunction A D E F).counit.app
      (ForgetEnrichment.of (Complex A) M) = functorExtensionCounit A D E F M := by
    rw [dgModuleEnrichedRestrictionAdjunction, transportedCounit]
    have hi : (eqToIso (dgModuleRestriction_onClosed_eq A D E F.op)).symm.inv.app
        (ForgetEnrichment.of (Complex A) M) = 𝟙 _ := by
      rw [Iso.symm_inv, functorEqIso_hom_app]
      rfl
    rw [hi, CategoryTheory.Functor.map_id, Category.id_comp]
    rfl
  have h := counitBijection (dgModuleHomotopyAdjunction A D E F)
    ((toHomotopy A (RightModule A D)).obj (ForgetEnrichment.of (Complex A) P))
    ((toHomotopy A (RightModule A E)).obj (ForgetEnrichment.of (Complex A) M))
  change Function.Bijective (fun f => (dgModuleExtension A D E F).onHomotopy.map f ≫
    (toHomotopy A (RightModule A E)).map
      ((dgModuleEnrichedRestrictionAdjunction A D E F).counit.app
        (ForgetEnrichment.of (Complex A) M))) at h
  rw [hc] at h
  exact h

/-- 概要：同じ graph 余単位の全 Hom 複体の普遍性（HA §4.2.3）。
方針：H⁰ の随伴対応を実斉次シフトで全整数次数へ移す。
規約：同じ制限加群と同じ評価射。使われ方：native な余単位判定。 -/
def graphUniversalCounit (F : DGFunctor A D E) (M : RightModule A E) :
    DGUniversalCounit A (RightModule A D) (RightModule A E) (dgModuleExtension A D E F) M where
  source := restrictModule A D E F.op M
  counit := functorExtensionCounit A D E F M
  quasiIso P := by
    apply dgCounitColumn_quasiIso_of_gradedShifts A (RightModule A D) (RightModule A E)
      (dgModuleExtension A D E F) (functorExtensionCounit A D E F M)
      (graphCounit_homotopy_bijective A D E F M)
    intro N n
    obtain ⟨W, f, g, hf, hg, h, hh⟩ := moduleGradedShiftWitness A D N (-n)
    let f' := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport
      (A := A) rfl rfl (neg_neg n) f
    have hf' : differential A f' = 0 := by
      rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport_differential, hf, map_zero]
    have hc := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport_compose
      (A := A) rfl rfl rfl (neg_neg n) rfl rfl g f (neg_add_cancel (-n))
    simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport_refl,
      LinearEquiv.refl_apply] at hc
    exact ⟨W, f', g, hf', hg, h, hh.trans (congrArg (· - (unitElement A N).val) hc)⟩

end SerrePositivity.EInfinity.Modules
