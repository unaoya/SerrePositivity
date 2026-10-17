module
public import SerrePositivity.DifferentialGraded.Morita.CriterionPerfHomInduction
public import SerrePositivity.DifferentialGraded.Morita.CriterionPerfTriangulated
public import SerrePositivity.DifferentialGraded.Perfect.UniversalProperty

/-! # 表現可能対象から Perf への二変数の厚い帰納

全 Hom 複体の条件からここへの橋は別途示す。このファイルでは、全整数 shift の
表現可能対象間で得た射の全単射性を厚い帰納で延長する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory Opposite
open scoped CategoryTheory.Pretriangulated.Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]

abbrev criterionPerfRepresentable (d : D) : DerivedModuleCategory A D :=
  (moduleToDerived A D).obj (ForgetEnrichment.of (Complex A) (representable A d))

/-- 両変数で shift した表現可能対象上の比較から、両変数の厚い帰納を行う。 -/
lemma criterionPerf_hom_bijective_of_representables
    (F : DerivedModuleCategory A D ⥤ DerivedModuleCategory A E)
    [F.CommShift ℤ] [F.IsTriangulated] [F.Additive]
    (hgen : ∀ (d d' : D) (m n : ℤ), Function.Bijective
      (F.map (X := (criterionPerfRepresentable A D d)⟦m⟧)
        (Y := (criterionPerfRepresentable A D d')⟦n⟧)))
    (X : DerivedModuleCategory A D) (hX : modulePerfect A D X)
    (Y : DerivedModuleCategory A D) (hY : modulePerfect A D Y) :
    Function.Bijective (F.map (X := X) (Y := Y)) := by
  let S₀ : ObjectProperty (DerivedModuleCategory A D) :=
    fun Z => ∃ d : D, Z = criterionPerfRepresentable A D d
  let S := S₀.shiftClosure ℤ
  let P := criterionPerfRelativeHomTargets F S
  have htarget : modulePerfect A D ≤ P := by
    apply (modulePerfect_le_iff_generators A D P).2
    intro d' Z hZ
    obtain ⟨Z', m, e, d, rfl⟩ := hZ
    exact homComparison_bijective_of_iso F e.symm
      ((shiftFunctorZero (DerivedModuleCategory A D) ℤ).app _)
      (hgen d d' m 0)
  let Q := criterionPerfRelativeHomTargets F.op (modulePerfect A D).op
  let : Q.unop.IsStableUnderRetracts := ⟨fun a ha =>
    Q.prop_of_retract a.op ha⟩
  have hsource : modulePerfect A D ≤ Q.unop := by
    apply (modulePerfect_le_iff_generators A D Q.unop).2
    intro d Z hZ
    apply (criterionPerfHomComparison_op_iff F _ _).2
    exact htarget Z.unop hZ _ (S₀.le_shiftClosure _ ⟨d, rfl⟩)
  exact (criterionPerfHomComparison_op_iff F X Y).1 (hsource X hX (op Y) hY)

/-- 実際の kernel 作用の射比較を Perf 制限の充満忠実性へ延長する。
全 Hom 複体条件から `hgen` を導く比較は、この帰納とは分離する。 -/
def criterionPerfFullyFaithfulOfRepresentables (K : Kernel A D E)
    (hK : kernelColumnsPerfect A D E K)
    (hgen : ∀ (d d' : D) (m n : ℤ), Function.Bijective
      ((kernelDerivedTensor A D E K).map (X := (criterionPerfRepresentable A D d)⟦m⟧)
        (Y := (criterionPerfRepresentable A D d')⟦n⟧))) :
    (perfectDerivedKernelAction A D E K hK).FullyFaithful := by
  let := criterionPerfKernelCommShift A D E K
  let := criterionPerfKernelIsTriangulated A D E K
  apply Nonempty.some
  apply (Functor.FullyFaithful.nonempty_iff_map_bijective _).2
  intro X Y
  have h := criterionPerf_hom_bijective_of_representables A D E
    (kernelDerivedTensor A D E K) hgen X.obj X.property Y.obj Y.property
  constructor
  · intro f g he
    apply (modulePerfect A D).hom_ext
    exact h.1 (congrArg (fun k => k.hom) he)
  · intro f
    obtain ⟨g, hg⟩ := h.2 f.hom
    exact ⟨ObjectProperty.homMk g, (modulePerfect A E).hom_ext hg⟩

end SerrePositivity.DifferentialGraded.Morita
