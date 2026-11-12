module

public import SerrePositivity.KST.Spectra.LoopIntervalEndFamilies
public import SerrePositivity.KST.Spectra.IntervalBoundary
public import SerrePositivity.Spectra.Pointed.TensorCoproduct

/-!
概要：区間の二つの面上での定数性を、二端点の境界全体の定数性へ同定する。
方針：零単体と単位の同型、tensor した余積の二成分を使う。
規約：面添字一が始点。使われ方：円の商への写像族の降下と復元。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped _root_.Simplicial
namespace SerrePositivity.KST.Spectra

/-- 区間の面は、対応する頂点への定数射と一致する。 -/
lemma intervalFace_eq_const (i : Fin 2) :
    (stdSimplex.δ i : (Δ[0] : SSet.{u}) ⟶ Δ[1]) =
      SSet.const (stdSimplex.obj₀Equiv.symm i.rev) := by
  fin_cases i <;> apply SSet.yonedaEquiv.injective <;> decide

/-- 零単体上の面による制限と、単位上の頂点による制限の定数性は同値。 -/
lemma intervalFamily_endpoint_unit_iff {P Y : SSet.{u}}
    (a : (Δ[1] : SSet.{u}) ⊗ P ⟶ Y) (y : Y _⦋0⦌) (i : Fin 2) :
    (stdSimplex.δ i ▷ P) ≫ a = SSet.const y ↔
      (SSet.const (X := 𝟙_ SSet.{u}) (stdSimplex.obj₀Equiv.symm i.rev) ▷ P) ≫ a =
        SSet.const y := by
  have hf : (stdSimplex.δ i : (Δ[0] : SSet.{u}) ⟶ Δ[1]) =
      PointedSimplicialSet.deltaZeroUnitIso.hom ≫
        SSet.const (stdSimplex.obj₀Equiv.symm i.rev) := by
    rw [SSet.comp_const, intervalFace_eq_const]
  constructor
  · intro h
    apply (cancel_epi (PointedSimplicialSet.deltaZeroUnitIso.hom ▷ P)).mp
    rw [← comp_whiskerRight_assoc, ← hf, h, SSet.comp_const]
  · intro h
    rw [hf, comp_whiskerRight_assoc, h, SSet.comp_const]

/-- 両端の面上の定数性は、二端点の境界全体での定数性と同値。 -/
lemma intervalFamily_boundary_iff {P Y : SSet.{u}}
    (a : (Δ[1] : SSet.{u}) ⊗ P ⟶ Y) (y : Y _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint.{u}.right ▷ P) ≫ a = SSet.const y ↔
      (stdSimplex.δ (1 : Fin 2) ▷ P) ≫ a = SSet.const y ∧
        (stdSimplex.δ (0 : Fin 2) ▷ P) ≫ a = SSet.const y := by
  rw [intervalFamily_endpoint_unit_iff a y 1, intervalFamily_endpoint_unit_iff a y 0]
  have hr₀ : (0 : Fin 2).rev = 1 := by decide
  have hr₁ : (1 : Fin 2).rev = 0 := by decide
  rw [hr₀, hr₁]
  constructor
  · intro h
    constructor
    · have hh := congrArg (fun t ↦ (coprod.inr ▷ P) ≫ t) h
      simpa only [← comp_whiskerRight_assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint_inr,
        SSet.comp_const] using hh
    · have hh := congrArg (fun t ↦ (coprod.inl ▷ P) ≫ t) h
      simpa only [← comp_whiskerRight_assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint_inl,
        SSet.comp_const] using hh
  · rintro ⟨h₀, h₁⟩
    apply PointedObject.tensorRightCoprod_hom_ext
    · simpa only [← comp_whiskerRight_assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint_inl,
        SSet.comp_const] using h₁
    · simpa only [← comp_whiskerRight_assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint_inr,
        SSet.comp_const] using h₀

end SerrePositivity.KST.Spectra
