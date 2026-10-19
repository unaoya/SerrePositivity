module

public import SerrePositivity.KST.DerivedBlowup.DiagramCoefficientFunctoriality
public import SerrePositivity.DifferentialGraded.Functor.QuasiEquivalence

/-!
概要：KST v4 §3.1・Lemma 3.6（pp.11–14）の係数図式同型は係数 dg 圏の準同値を誘導する。
方針：包含上の Hom は成分同型、非包含上は零複体の同型とし、添字から本質的全射を示す。
規約：係数 dg 圏の準同値であり、cartesian・局所 perfect 条件は別に比較する。
使われ方：二つの表示の全図式加群の導来模型を比較する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory DifferentialGraded

variable {R : Type u} [CommRing R] {J : Type v} [Preorder J] [DecidableLE J]
variable {F G : J ⥤ Mon (Complex R)}

/-- 概要：係数図式同型は係数 dg 圏の各 Hom 複体で同型を誘導する。
方針：包含上の標準同定で成分同型を移し、非包含では零複体の標準同定を使う。
規約：KST Lemma 3.6。使われ方：係数 dg 準同値の Hom 条件。 -/
theorem diagramCoefficientDGFunctor_map_isIso (e : F ≅ G)
    (x y : DiagramModuleCoefficientObject F) :
    IsIso ((diagramCoefficientDGFunctor e.hom).map x y) := by
  change IsIso (diagramCoefficientHomMap e.hom x.index y.index)
  by_cases h : x.index ≤ y.index
  · simp only [diagramCoefficientHomMap, dite_eq_left h]
    unfold diagramModuleHomInclusion
    infer_instance
  · simp only [diagramCoefficientHomMap, dite_eq_right h]
    infer_instance

/-- 概要：係数図式の射の H⁰ 関手は本質的全射。
方針：対象の添字を変えないので、行先の同じ添字を始点として取る。
規約：KST §3.1、成分が同型であることは不要。
使われ方：係数図式同型の準同値性の対象条件。 -/
theorem diagramCoefficientDGFunctor_homotopy_essSurj (α : F ⟶ G) :
    (diagramCoefficientDGFunctor α).onHomotopy.EssSurj := by
  apply Functor.essSurj_of_surj
  rintro ⟨y⟩
  change DiagramModuleCoefficientObject G at y
  rcases y with ⟨i⟩
  exact ⟨⟨⟨i⟩⟩, rfl⟩

/-- 概要：係数図式同型の誘導する係数 dg 関手は準同値。
方針：全 Hom の同型性と添字に関する本質的全射性を組み合わせる。
規約：KST §3.1・Lemma 3.6。使われ方：既存の導来 Morita 比較への入力。 -/
theorem diagramCoefficientDGFunctor_quasiEquivalence (e : F ≅ G) :
    QuasiEquivalence (diagramCoefficientDGFunctor e.hom) := by
  refine ⟨?_, diagramCoefficientDGFunctor_homotopy_essSurj e.hom⟩
  intro x y
  let := diagramCoefficientDGFunctor_map_isIso e x y
  infer_instance

end SerrePositivity.KST.DerivedBlowup
