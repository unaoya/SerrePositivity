module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FunctorComparison.SpanNerveCoordinates

/-!
概要：通常の小さい span の nerve と二辺のホーン Λ[2,0] の厳密な同型を構成する。
方針：射列の頂点を 0・1・2 で読み、二終点を同時に含まないことからホーンの単体を得る。
規約：全ての面・退化に自然。使われ方：通常の Kan 値 span の native な余錐への形状の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section

/-- ホーンの単体は二つの終点 1 と 2 を同時に含まない。 -/
lemma hornSpanSimplex_not_both {n : ℕ} (s : (horn 2 0 : SSet.{u}) _⦋n⦌)
    (i j : Fin (n + 1)) : ¬ (s.val i = 1 ∧ s.val j = 2) := by
  obtain ⟨k, hk, hmiss⟩ := (mem_horn_iff_notMem_range s.val 0).mp s.property
  fin_cases k
  · exact (hk rfl).elim
  · intro h
    exact hmiss ⟨i, h.1⟩
  · intro h
    exact hmiss ⟨j, h.2⟩

/-- ホーンの単体の頂点と射を、元の小さい span の合成可能射列として読む。 -/
def hornSpanSimplexChain {n : ℕ} (s : (horn 2 0 : SSet.{u}) _⦋n⦌) :
    Fin (n + 1) ⥤ AsSmall.{u} WalkingSpan where
  obj i := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.spanIndexVertex (s.val i)
  map {i j} f := (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.spanIndexVertex_nonempty_hom _ _
    (stdSimplex.monotone_apply s.val (leOfHom f)) (hornSpanSimplex_not_both s i j)).some
  map_id _ := by apply ULift.ext; exact Subsingleton.elim _ _
  map_comp _ _ := by apply ULift.ext; exact Subsingleton.elim _ _

/-- ホーンの全ての単体を、通常の小さい span の nerve へ写す。 -/
def hornToSpanNerve : (horn 2 0 : SSet.{u}) ⟶ nerve (AsSmall.{u} WalkingSpan) where
  app n := ↾fun s ↦ hornSpanSimplexChain s
  naturality := by
    rintro ⟨⟨n⟩⟩ ⟨⟨m⟩⟩ α
    apply ConcreteCategory.hom_ext
    intro s
    refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
    intro i j f
    apply ULift.ext
    exact Subsingleton.elim _ _

/-- span の射列にも、二終点 1 と 2 は同時に現れない。 -/
lemma spanNerveSimplex_not_both {n : ℕ} (s : (nerve (AsSmall.{u} WalkingSpan)) _⦋n⦌)
    (i j : Fin (n + 1)) : ¬ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.spanVertexIndex (s.obj i) = 1 ∧ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.spanVertexIndex (s.obj j) = 2) := by
  intro h
  rcases le_total i j with hij | hji
  · exact (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.spanVertexIndex_hom_condition (s.map (homOfLE hij))).2 h
  · have hh := (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.spanVertexIndex_hom_condition (s.map (homOfLE hji))).1
    rw [h.1, h.2] at hh
    omega

/-- span の射列の頂点番号は、標準二単体のホーンに属する単体となる。 -/
def spanNerveHornSimplex {n : ℕ} (s : (nerve (AsSmall.{u} WalkingSpan)) _⦋n⦌) :
    (horn 2 0 : SSet.{u}) _⦋n⦌ := by
  let t : (Δ[2] : SSet.{u}) _⦋n⦌ := stdSimplex.objMk
    ⟨fun i ↦ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.spanVertexIndex (s.obj i),
      fun _ _ h ↦ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.spanVertexIndex_hom_condition (s.map (homOfLE h))).1⟩
  refine ⟨t, (mem_horn_iff_notMem_range t 0).mpr ?_⟩
  by_cases h : ∃ i, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.spanVertexIndex (s.obj i) = 1
  · obtain ⟨i, hi⟩ := h
    refine ⟨2, by decide, ?_⟩
    rintro ⟨j, hj⟩
    exact spanNerveSimplex_not_both s i j ⟨hi, hj⟩
  · refine ⟨1, by decide, ?_⟩
    rintro ⟨i, hi⟩
    exact h ⟨i, hi⟩

/-- 全ての射列の頂点番号は、面と退化を保ってホーンへ写る。 -/
def spanNerveToHorn : nerve (AsSmall.{u} WalkingSpan) ⟶ (horn 2 0 : SSet.{u}) where
  app n := ↾fun s ↦ spanNerveHornSimplex s
  naturality := by
    rintro ⟨⟨n⟩⟩ ⟨⟨m⟩⟩ α
    apply ConcreteCategory.hom_ext
    intro s
    apply Subtype.ext
    apply stdSimplex.ext
    intro i
    rfl

/-- 小さい span の nerve は、二辺のホーンと厳密に同型。 -/
def spanNerveHornIso : nerve (AsSmall.{u} WalkingSpan) ≅ (horn 2 0 : SSet.{u}) where
  hom := spanNerveToHorn
  inv := hornToSpanNerve
  hom_inv_id := by
    apply SSet.hom_ext
    rintro ⟨⟨n⟩⟩
    apply ConcreteCategory.hom_ext
    intro s
    refine CategoryTheory.Functor.ext (fun i ↦ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.spanIndexVertex_vertexIndex (s.obj i)) ?_
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
    exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.spanVertexIndex_indexVertex (s.val i)

/-- ホーンの左辺は、小さい span の実際の左構造射の nerve の辺になる。 -/
lemma hornToSpanNerve_left_edge :
    horn₂₀.ι₀₁ ≫ hornToSpanNerve.{u} =
      SSet.yonedaEquiv.symm (nerve.edgeMk (AsSmall.up.map WalkingSpan.Hom.fst)).edge := by
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
  change hornSpanSimplexChain (SSet.yonedaEquiv horn₂₀.ι₀₁) = _
  refine ComposableArrows.ext₁ ?_ ?_ ?_
  · change _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.spanIndexVertex (0 : Fin 3) = AsSmall.up.obj WalkingSpan.zero
    simp [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.spanIndexVertex]
  · change _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.spanIndexVertex (1 : Fin 3) = AsSmall.up.obj WalkingSpan.left
    simp [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.spanIndexVertex]
  · apply ULift.ext
    exact Subsingleton.elim _ _

/-- ホーンの右辺は、小さい span の実際の右構造射の nerve の辺になる。 -/
lemma hornToSpanNerve_right_edge :
    horn₂₀.ι₀₂ ≫ hornToSpanNerve.{u} =
      SSet.yonedaEquiv.symm (nerve.edgeMk (AsSmall.up.map WalkingSpan.Hom.snd)).edge := by
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
  change hornSpanSimplexChain (SSet.yonedaEquiv horn₂₀.ι₀₂) = _
  refine ComposableArrows.ext₁ ?_ ?_ ?_
  · change _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.spanIndexVertex (0 : Fin 3) = AsSmall.up.obj WalkingSpan.zero
    simp [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.spanIndexVertex]
  · change _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.spanIndexVertex (2 : Fin 3) = AsSmall.up.obj WalkingSpan.right
    simp [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.spanIndexVertex]
  · apply ULift.ext
    exact Subsingleton.elim _ _

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
