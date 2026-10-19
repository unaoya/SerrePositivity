module
public import SerrePositivity.InfinityCategories.Derived.DGQuotientZeroObjects
public import SerrePositivity.InfinityCategories.Derived.DGFunctorZeroObjects

/-! # 指定対象を零化する dg 関手の商への延長

概要：dg nerve で指定対象を零化する dg 関手を、明示的 dg 商からの関手へ延長する。
方針：実零対象性から収縮元を選び、既存の指定収縮付き延長を適用する。
規約：dg 関手から来る写像に関する主張。全 ∞ 関手圏の局所化普遍性は別途必要。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable {A : Type u} [CommRing A] {D E : Type v} [DGCategory A D] [DGCategory A E]
variable {P : Set D}

/-- 対象像が実零頂点なら、その dg 関手に指定収縮データを付けられる。 -/
lemma dgFunctor_exists_contracted_of_zeroing (F : DGFunctor A D E)
    (hF : ∀ b : P, IsZeroVertex (X := dgNerve A E) (Simplex.vertex (F.obj b.val))) :
    ∃ C : DGQuotient.ContractedFunctor A D P E, C.toDGFunctor = F := by
  have hc (b : P) := (dgNerve_isZeroVertex_iff_contractingElement (F.obj b.val)).1 (hF b)
  exact ⟨⟨F, fun b => (hc b).choose, fun b => (hc b).choose_spec⟩, rfl⟩

/-- 指定収縮データが存在することと、対象像が実零頂点となることは同値。 -/
lemma dgFunctor_zeroing_iff_exists_contracted (F : DGFunctor A D E) :
    (∀ b : P, IsZeroVertex (X := dgNerve A E) (Simplex.vertex (F.obj b.val))) ↔
      ∃ C : DGQuotient.ContractedFunctor A D P E, C.toDGFunctor = F := by
  constructor
  · exact dgFunctor_exists_contracted_of_zeroing F
  · rintro ⟨C, rfl⟩ b
    exact dgNerve_contractingElement_isZeroVertex _ (C.homotopy b) (C.d_homotopy b)

variable [Small.{u} D]

/-- 指定対象を実零頂点へ送る dg 関手は、商の nerve を経由する dg 関手の像に延長する。 -/
lemma dgQuotient_exists_nerve_extension_of_zeroing (F : DGFunctor A D E)
    (hF : ∀ b : P, IsZeroVertex (X := dgNerve A E)
      ((dgNerve.map F).app _ (Simplex.vertex b.val))) :
    ∃ G : DGFunctor A (DGQuotient.QuotientObject D P) E,
      dgQuotientNerveProjection A D P ≫ dgNerve.map G = dgNerve.map F := by
  have hz (b : P) : IsZeroVertex (X := dgNerve A E) (Simplex.vertex (F.obj b.val)) := by
    simpa only [dgFunctorNerve_vertex] using hF b
  obtain ⟨C, hC⟩ := dgFunctor_exists_contracted_of_zeroing F hz
  refine ⟨DGQuotient.extension A C, ?_⟩
  change dgQuotientNerveProjection A D P ≫ dgQuotientNerveExtension A C = dgNerve.map F
  rw [dgQuotientNerveExtension_projection, hC]

end SerrePositivity.InfinityCategories
