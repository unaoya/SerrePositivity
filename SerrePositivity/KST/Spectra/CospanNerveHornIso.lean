module

public import SerrePositivity.KST.Spectra.CospanNerveCoordinates

/-!
概要：通常の小さい cospan の nerve と二辺のホーン Λ[2,2] の厳密な同型を構成する。
方針：射列の頂点を 0・1・2 で読み、二始点を同時に含まないことからホーンの単体を得る。
規約：全ての面・退化に自然。使われ方：通常の Kan 値 cospan の native な余錐への形状の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra.CospanShape
noncomputable section

/-- ホーンの単体は二つの始点 0 と 1 を同時に含まない。 -/
lemma hornCospanSimplex_not_both {n : ℕ} (s : (horn 2 2 : SSet.{u}) _⦋n⦌)
    (i j : Fin (n + 1)) : ¬ (s.val i = 0 ∧ s.val j = 1) := by
  obtain ⟨k, hk, hmiss⟩ := (mem_horn_iff_notMem_range s.val 2).mp s.property
  fin_cases k
  · intro h
    exact hmiss ⟨i, h.1⟩
  · intro h
    exact hmiss ⟨j, h.2⟩
  · exact (hk rfl).elim

/-- ホーンの単体の頂点と射を、元の小さい cospan の合成可能射列として読む。 -/
def hornCospanSimplexChain {n : ℕ} (s : (horn 2 2 : SSet.{u}) _⦋n⦌) :
    Fin (n + 1) ⥤ AsSmall.{u} WalkingCospan where
  obj i := cospanIndexVertex (s.val i)
  map {i j} f := (cospanIndexVertex_nonempty_hom _ _
    (stdSimplex.monotone_apply s.val (leOfHom f)) (hornCospanSimplex_not_both s i j)).some
  map_id _ := by apply ULift.ext; exact Subsingleton.elim _ _
  map_comp _ _ := by apply ULift.ext; exact Subsingleton.elim _ _

/-- ホーンの全ての単体を、通常の小さい cospan の nerve へ写す。 -/
def hornToCospanNerve : (horn 2 2 : SSet.{u}) ⟶ nerve (AsSmall.{u} WalkingCospan) where
  app n := ↾fun s ↦ hornCospanSimplexChain s
  naturality := by
    rintro ⟨⟨n⟩⟩ ⟨⟨m⟩⟩ α
    apply ConcreteCategory.hom_ext
    intro s
    refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
    intro i j f
    apply ULift.ext
    exact Subsingleton.elim _ _

/-- cospan の射列にも、二始点 0 と 1 は同時に現れない。 -/
lemma cospanNerveSimplex_not_both {n : ℕ}
    (s : (nerve (AsSmall.{u} WalkingCospan)) _⦋n⦌)
    (i j : Fin (n + 1)) :
    ¬ (cospanVertexIndex (s.obj i) = 0 ∧ cospanVertexIndex (s.obj j) = 1) := by
  intro h
  rcases le_total i j with hij | hji
  · exact (cospanVertexIndex_hom_condition (s.map (homOfLE hij))).2 h
  · have hh := (cospanVertexIndex_hom_condition (s.map (homOfLE hji))).1
    rw [h.1, h.2] at hh
    omega

/-- cospan の射列の頂点番号は、標準二単体のホーンに属する単体となる。 -/
def cospanNerveHornSimplex {n : ℕ} (s : (nerve (AsSmall.{u} WalkingCospan)) _⦋n⦌) :
    (horn 2 2 : SSet.{u}) _⦋n⦌ := by
  let t : (Δ[2] : SSet.{u}) _⦋n⦌ := stdSimplex.objMk
    ⟨fun i ↦ cospanVertexIndex (s.obj i),
      fun _ _ h ↦ (cospanVertexIndex_hom_condition (s.map (homOfLE h))).1⟩
  refine ⟨t, (mem_horn_iff_notMem_range t 2).mpr ?_⟩
  by_cases h : ∃ i, cospanVertexIndex (s.obj i) = 0
  · obtain ⟨i, hi⟩ := h
    refine ⟨1, by decide, ?_⟩
    rintro ⟨j, hj⟩
    exact cospanNerveSimplex_not_both s i j ⟨hi, hj⟩
  · refine ⟨0, by decide, ?_⟩
    rintro ⟨i, hi⟩
    exact h ⟨i, hi⟩

/-- 全ての射列の頂点番号は、面と退化を保ってホーンへ写る。 -/
def cospanNerveToHorn : nerve (AsSmall.{u} WalkingCospan) ⟶ (horn 2 2 : SSet.{u}) where
  app n := ↾fun s ↦ cospanNerveHornSimplex s
  naturality := by
    rintro ⟨⟨n⟩⟩ ⟨⟨m⟩⟩ α
    apply ConcreteCategory.hom_ext
    intro s
    apply Subtype.ext
    apply stdSimplex.ext
    intro i
    rfl

/-- 小さい cospan の nerve は、二辺のホーンと厳密に同型。 -/
def cospanNerveHornIso : nerve (AsSmall.{u} WalkingCospan) ≅ (horn 2 2 : SSet.{u}) where
  hom := cospanNerveToHorn
  inv := hornToCospanNerve
  hom_inv_id := by
    apply SSet.hom_ext
    rintro ⟨⟨n⟩⟩
    apply ConcreteCategory.hom_ext
    intro s
    refine CategoryTheory.Functor.ext (fun i ↦ cospanIndexVertex_vertexIndex (s.obj i)) ?_
    intro i j f
    apply ULift.ext
    exact Subsingleton.elim _ _
  inv_hom_id := by
    apply SSet.hom_ext
    rintro ⟨⟨n⟩⟩
    apply ConcreteCategory.hom_ext
    intro s
    apply Subtype.ext
    apply stdSimplex.ext
    intro i
    exact cospanVertexIndex_indexVertex (s.val i)

/-- ホーンの左辺は、小さい cospan の実際の左構造射の nerve の辺になる。 -/
lemma hornToCospanNerve_left_edge :
    horn₂₂.ι₀₂ ≫ hornToCospanNerve.{u} =
      SSet.yonedaEquiv.symm (nerve.edgeMk (AsSmall.up.map WalkingCospan.Hom.inl)).edge := by
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
  change hornCospanSimplexChain (SSet.yonedaEquiv horn₂₂.ι₀₂) = _
  refine ComposableArrows.ext₁ ?_ ?_ ?_
  · change cospanIndexVertex (0 : Fin 3) = AsSmall.up.obj WalkingCospan.left
    simp [cospanIndexVertex]
  · change cospanIndexVertex (2 : Fin 3) = AsSmall.up.obj WalkingCospan.one
    simp [cospanIndexVertex]
  · apply ULift.ext
    exact Subsingleton.elim _ _

/-- ホーンの右辺は、小さい cospan の実際の右構造射の nerve の辺になる。 -/
lemma hornToCospanNerve_right_edge :
    horn₂₂.ι₁₂ ≫ hornToCospanNerve.{u} =
      SSet.yonedaEquiv.symm (nerve.edgeMk (AsSmall.up.map WalkingCospan.Hom.inr)).edge := by
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
  change hornCospanSimplexChain (SSet.yonedaEquiv horn₂₂.ι₁₂) = _
  refine ComposableArrows.ext₁ ?_ ?_ ?_
  · change cospanIndexVertex (1 : Fin 3) = AsSmall.up.obj WalkingCospan.right
    simp [cospanIndexVertex]
  · change cospanIndexVertex (2 : Fin 3) = AsSmall.up.obj WalkingCospan.one
    simp [cospanIndexVertex]
  · apply ULift.ext
    exact Subsingleton.elim _ _

end
end SerrePositivity.KST.Spectra.CospanShape
