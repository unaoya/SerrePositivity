module
public import SerrePositivity.KST.LocalizingInvariants.CospanConeSquareLegs

public import SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.CosliceRoofPasting
public import SerrePositivity.InfinityCategories.Core.SimplexVertexDetection

/-!
概要：指定合成三角柱の二つの屋根面を、同じ五頂点図式の実 cospan として読む。
方針：五頂点への包含で cospan を作り、同じ始点の join を三角柱へ写す。
規約：商四角形の二面と同じ次辺を選び直さない。
使われ方：回収した実屋根の全 slice 比較を元の指定合成三角柱へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

lemma roofPastingPrismIso_inl :
    joinInl (Δ[0] : SSet.{u}) (pastingCorner : SSet.{u}).op ≫ _root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofPastingPrismIso.hom =
      SSet.yonedaEquiv.symm
        (stdSimplex.obj₀Equiv.symm (0 : Fin 3), stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofPastingPrismIso, Iso.trans_hom, joinIso, Iso.symm_hom]
  rw [← Category.assoc (joinInl _ _) (joinMap _ _), joinInl_joinMap, Category.assoc,
    ← Category.assoc (joinInl _ _) (stableJoinReverseIso _ _).inv,
    stableJoinReverse_inl_inv]
  simp only [Functor.mapIso_hom]
  rw [← Category.assoc (SSet.opFunctor.map _) (SSet.opFunctor.map _),
    ← SSet.opFunctor.map_comp]
  apply SSet.yonedaEquiv.injective
  apply Prod.ext <;> decide

lemma roofPastingDenominator_target : stdSimplex.δ (0 : Fin 2) ≫
    squareLeftEdge ≫ _root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofPastingSquareInclusion.{u} =
      stdSimplex.δ (0 : Fin 2) ≫ stdSimplex.δ (2 : Fin 3) ≫
        _root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofPastingTriangleInclusion := by
  apply SSet.yonedaEquiv.injective
  apply Subtype.ext
  apply Prod.ext <;> decide

lemma roofPastingNumerator_target : stdSimplex.δ (0 : Fin 2) ≫
    stdSimplex.δ (1 : Fin 3) ≫ _root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofPastingTriangleInclusion.{u} =
      stdSimplex.δ (0 : Fin 2) ≫ squareRightEdge ≫ _root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofPastingSquareInclusion := by
  apply SSet.yonedaEquiv.injective
  apply Subtype.ext
  apply Prod.ext <;> decide

/-- 元の前段と同じ実分母の cospan。 -/
def roofPastingDenominatorCospan : (horn 2 2 : SSet.{u}) ⟶
    (pastingCorner : SSet.{u}).op :=
  conePairCospan (squareLeftEdge ≫ _root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofPastingSquareInclusion)
    (stdSimplex.δ (2 : Fin 3) ≫ _root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofPastingTriangleInclusion) roofPastingDenominator_target

/-- 同じ実分子と元の次辺の cospan。 -/
def roofPastingNumeratorCospan : (horn 2 2 : SSet.{u}) ⟶
    (pastingCorner : SSet.{u}).op :=
  conePairCospan (stdSimplex.δ (1 : Fin 3) ≫ _root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofPastingTriangleInclusion)
    (squareRightEdge ≫ _root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofPastingSquareInclusion) roofPastingNumerator_target

/-- join の頂点は同じ左因子または右因子から来る。 -/
lemma roofJoin_vertex_cases {K L : SSet.{u}} (s : (join K L) _⦋0⦌) :
    (∃ x : K _⦋0⦌, (joinInl K L).app (Opposite.op ⦋0⦌) x = s) ∨
      (∃ y : L _⦋0⦌, (joinInr K L).app (Opposite.op ⦋0⦌) y = s) := by
  rcases s with ⟨⟨_ | _ | l, hl⟩, x, y⟩
  · right
    cases x
    exact ⟨y, rfl⟩
  · left
    cases y
    exact ⟨x, rfl⟩
  · change l + 2 < 2 at hl
    omega

/-- 標準格子への join 図式は、両因子の制限で一意に決まる。 -/
lemma roofGrid_join_hom_ext {K L : SSet.{u}} {m n : ℕ}
    {f g : join K L ⟶ (Δ[m] : SSet.{u}) ⊗ Δ[n]}
    (hl : joinInl K L ≫ f = joinInl K L ≫ g)
    (hr : joinInr K L ≫ f = joinInr K L ≫ g) : f = g := by
  have h₀ : f.app (Opposite.op ⦋0⦌) = g.app (Opposite.op ⦋0⦌) := by
    apply ConcreteCategory.hom_ext
    intro s
    rcases roofJoin_vertex_cases s with ⟨x, rfl⟩ | ⟨y, rfl⟩
    · exact congrArg (fun u : K ⟶ (Δ[m] : SSet.{u}) ⊗ Δ[n] =>
        u.app (Opposite.op ⦋0⦌) x) hl
    · exact congrArg (fun u : L ⟶ (Δ[m] : SSet.{u}) ⊗ Δ[n] =>
        u.app (Opposite.op ⦋0⦌) y) hr
  apply CartesianMonoidalCategory.hom_ext
  · apply stdSimplex_hom_ext_vertices
    apply ConcreteCategory.hom_ext
    intro s
    exact congrArg Prod.fst (ConcreteCategory.congr_hom h₀ s)
  · apply stdSimplex_hom_ext_vertices
    apply ConcreteCategory.hom_ext
    intro s
    exact congrArg Prod.snd (ConcreteCategory.congr_hom h₀ s)

lemma roofCospanSquareIso_inl :
    joinInl (Δ[0] : SSet.{u}) (horn 2 2 : SSet.{u}) ≫ cospanConeSquareIso.hom =
      SSet.yonedaEquiv.symm
        (stdSimplex.obj₀Equiv.symm (0 : Fin 2), stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
  have hs := F2.coneLegInclusion_source
    (SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 2) ≫ horn₂₂.ι₀₂) :
      (horn 2 2 : SSet.{u}) _⦋0⦌)
  rw [← hs, ← cospanConeSquare_bottom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  apply SSet.yonedaEquiv.injective
  apply Prod.ext <;> decide

/-- 分母側の面は、同じ二辺の cospan 上の同じ錐の正方形表示。 -/
lemma roofPastingPrismIso_denominator :
    (stdSimplex.δ (2 : Fin 3) ▷ (Δ[1] : SSet.{u})) ≫ _root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofPastingPrismIso.inv =
      cospanConeSquareIso.inv ≫ joinMap (𝟙 Δ[0]) roofPastingDenominatorCospan := by
  apply (cancel_mono _root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofPastingPrismIso.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  apply (cancel_epi cospanConeSquareIso.hom).mp
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  apply roofGrid_join_hom_ext
  · rw [← Category.assoc, roofCospanSquareIso_inl]
    rw [← Category.assoc (joinInl _ _) (joinMap _ _), joinInl_joinMap,
      Category.id_comp, roofPastingPrismIso_inl]
    apply SSet.yonedaEquiv.injective
    apply Prod.ext <;> decide
  · rw [← Category.assoc (joinInr _ _) (joinMap _ _), joinInr_joinMap,
      Category.assoc, _root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofPastingPrismIso_inr]
    change cospanSquareBoundary ≫ (stdSimplex.δ (2 : Fin 3) ▷ Δ[1]) = _
    apply horn₂₂.isPushout.hom_ext
    · rw [← Category.assoc, cospanSquareBoundary_rightEdge,
        ← Category.assoc, roofPastingDenominatorCospan, conePairCospan_first,
        Category.assoc, _root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofPastingSquareInclusion_corner]
      apply SSet.yonedaEquiv.injective
      apply Prod.ext <;> decide
    · rw [← Category.assoc, cospanSquareBoundary_topEdge,
        ← Category.assoc, roofPastingDenominatorCospan, conePairCospan_second,
        Category.assoc, _root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofPastingTriangleInclusion_corner]
      apply SSet.yonedaEquiv.injective
      apply Prod.ext <;> decide

/-- 分子側の面も、同じ二辺の cospan 上の同じ錐の転置正方形。 -/
lemma roofPastingPrismIso_numerator :
    (stdSimplex.δ (1 : Fin 3) ▷ (Δ[1] : SSet.{u})) ≫ _root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofPastingPrismIso.inv =
      (β_ Δ[1] Δ[1]).hom ≫ cospanConeSquareIso.inv ≫
        joinMap (𝟙 Δ[0]) roofPastingNumeratorCospan := by
  apply (cancel_mono _root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofPastingPrismIso.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  apply (cancel_epi (cospanConeSquareIso.hom ≫ (β_ Δ[1] Δ[1]).hom)).mp
  simp only [Category.assoc]
  rw [← Category.assoc (β_ Δ[1] Δ[1]).hom (β_ Δ[1] Δ[1]).hom,
    SymmetricCategory.symmetry, Category.id_comp,
    ← Category.assoc cospanConeSquareIso.hom cospanConeSquareIso.inv,
    Iso.hom_inv_id, Category.id_comp]
  apply roofGrid_join_hom_ext
  · rw [← Category.assoc, ← Category.assoc, roofCospanSquareIso_inl]
    rw [← Category.assoc (joinInl _ _) (joinMap _ _), joinInl_joinMap,
      Category.id_comp, roofPastingPrismIso_inl]
    apply SSet.yonedaEquiv.injective
    apply Prod.ext <;> decide
  · rw [← Category.assoc (joinInr _ _) (joinMap _ _), joinInr_joinMap,
      Category.assoc, _root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofPastingPrismIso_inr]
    change cospanSquareBoundary ≫ (β_ Δ[1] Δ[1]).hom ≫
      (stdSimplex.δ (1 : Fin 3) ▷ Δ[1]) = _
    apply horn₂₂.isPushout.hom_ext
    · rw [← Category.assoc, cospanSquareBoundary_rightEdge,
        ← Category.assoc (horn₂₂.ι₀₂) roofPastingNumeratorCospan,
        roofPastingNumeratorCospan, conePairCospan_first,
        Category.assoc, _root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofPastingTriangleInclusion_corner]
      apply SSet.yonedaEquiv.injective
      apply Prod.ext <;> decide
    · rw [← Category.assoc, cospanSquareBoundary_topEdge,
        ← Category.assoc (horn₂₂.ι₁₂) roofPastingNumeratorCospan,
        roofPastingNumeratorCospan, conePairCospan_second,
        Category.assoc, _root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofPastingSquareInclusion_corner]
      apply SSet.yonedaEquiv.injective
      apply Prod.ext <;> decide

variable {X : SSet.{u}} {a : (Δ[0] : SSet.{u}) ⟶ X}
  (F : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ sliceUnder a)
  (σ : (Δ[2] : SSet.{u}) ⟶ sliceUnder a)
  (hσ : stdSimplex.δ (0 : Fin 3) ≫ σ = squareRightEdge ≫ F)

/-- 同じ五頂点の商 coslice 図式の全錐。 -/
def roofPastingCone : JoinCone (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofPastingCosliceDiagram F σ hσ ≫ sliceUnderProjection a) :=
  ⟨sliceUnderUncurry (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofPastingCosliceDiagram F σ hσ), sliceUnderUncurry_projection _⟩

lemma roofPastingPrism_denominator : pastingSquare (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofPastingPrism F σ hσ) 2 =
    cospanConeSquareIso.inv ≫ joinMap (𝟙 Δ[0]) roofPastingDenominatorCospan ≫
      (roofPastingCone F σ hσ).val := by
  change (stdSimplex.δ (2 : Fin 3) ▷ (Δ[1] : SSet.{u})) ≫
    (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofPastingPrismIso.inv ≫ sliceUnderUncurry _) = _
  rw [← Category.assoc, roofPastingPrismIso_denominator]
  rfl

lemma roofPastingPrism_numerator : pastingSquare (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofPastingPrism F σ hσ) 1 =
    (β_ Δ[1] Δ[1]).hom ≫ cospanConeSquareIso.inv ≫
      joinMap (𝟙 Δ[0]) roofPastingNumeratorCospan ≫ (roofPastingCone F σ hσ).val := by
  change (stdSimplex.δ (1 : Fin 3) ▷ (Δ[1] : SSet.{u})) ≫
    (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofPastingPrismIso.inv ≫ sliceUnderUncurry _) = _
  rw [← Category.assoc, roofPastingPrismIso_numerator]
  rfl

lemma roofPastingCosliceDiagram_square : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofPastingSquareInclusion ≫
    _root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofPastingCosliceDiagram F σ hσ = (β_ Δ[1] Δ[1]).hom ≫ F := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofPastingSquareInclusion, _root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofPastingCosliceDiagram]
  simp only [Category.assoc]
  rw [← Category.assoc (SSet.opFunctor.map _) (SSet.opFunctor.map _),
    ← SSet.opFunctor.map_comp, pastingCornerGlue_left]
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofGridReverseIso_hom_map]
  exact reverseGrid_double (X := sliceUnder a) (m := 1) (n := 1) ((β_ Δ[1] Δ[1]).hom ≫ F)

lemma roofPastingCosliceDiagram_triangle : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofPastingTriangleInclusion ≫
    _root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofPastingCosliceDiagram F σ hσ = σ := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofPastingTriangleInclusion, _root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofPastingCosliceDiagram]
  simp only [Category.assoc]
  rw [← Category.assoc (SSet.opFunctor.map _) (SSet.opFunctor.map _),
    ← SSet.opFunctor.map_comp, pastingCornerGlue_bottom]
  exact _root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofReverseSimplex_double (X := sliceUnder a) σ

end SerrePositivity.KST.LocalizingInvariants
