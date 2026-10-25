module

public import SerrePositivity.InfinityCategories.F2.Ind.CompactGeneratorPresentation

/-!
概要：冪等完備 C の Ind 内で、compact 対象は元の Yoneda の像そのものである。
方針：compact 全部分圏での生成同値の本質全射性を、同じ包含で元の Ind へ戻す。
規約：元の Ind 頂点と元の Yoneda 像の実頂点同型を保持する。
使われ方：I-2 e、K-B の K-7 d4 における compact 像の同定。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable (κ : Cardinal.{u}) [Fact κ.IsRegular] {C : SSet.{u}} [Quasicategory C]

/-- 冪等完備 C の元の Yoneda の本質像は、Ind 内の全ての κ-compact 対象。 -/
lemma ind_isKappaCompact_iff_yoneda (hC : Idempotent.IsIdempotentComplete C)
    (x : (IndInfinity κ C) _⦋0⦌) :
    Compact.IsKappaCompact.{u, u + 1} κ x ↔ ∃ y : C _⦋0⦌,
      Nonempty (VertexIso ((indYoneda κ C).app (Opposite.op ⦋0⦌) (ULift.up y)) x) := by
  constructor
  · intro hx
    let z : Compact.kappaCompactObjects.{u, u + 1} κ (IndInfinity κ C) _⦋0⦌ :=
      ⟨x, fun v ↦ by
        have hv : v = 𝟙 ⦋0⦌ := Subsingleton.elim _ _
        simpa only [hv, op_id, CategoryTheory.Functor.map_id_apply] using hx⟩
    obtain ⟨⟨y⟩, ⟨e⟩⟩ := compactYoneda_isEssentiallySurjective κ hC z
    refine ⟨y, ⟨?_⟩⟩
    have h := VertexIso.map e
      (Compact.kappaCompactInclusion.{u, u + 1} κ (IndInfinity κ C))
    have hy := congrArg (fun f ↦ f.app (Opposite.op ⦋0⦌) (ULift.up y))
      (Compact.compactIndYoneda_inclusion (C := C) κ)
    change VertexIso _ x at h
    exact hy ▸ h
  · rintro ⟨y, ⟨e⟩⟩
    exact (Compact.isKappaCompact_iff_of_iso e).mp (Compact.indYoneda_isKappaCompact κ y)

end SerrePositivity.InfinityCategories.F2.Ind
