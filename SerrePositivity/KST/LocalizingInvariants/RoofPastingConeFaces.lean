module
public import SerrePositivity.KST.LocalizingInvariants.CospanConeSquareLegs

public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.CosliceRoofPasting
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.SimplexVertexDetection

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
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{u}) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingCorner : SSet.{u}).op ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofPastingPrismIso.hom =
      SSet.yonedaEquiv.symm
        (stdSimplex.obj₀Equiv.symm (0 : Fin 3), stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
  simp only [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofPastingPrismIso, Iso.trans_hom, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinIso, Iso.symm_hom]
  rw [← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl _ _) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap _ _), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap, Category.assoc,
    ← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl _ _) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableJoinReverseIso _ _).inv,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableJoinReverse_inl_inv]
  simp only [Functor.mapIso_hom]
  rw [← Category.assoc (SSet.opFunctor.map _) (SSet.opFunctor.map _),
    ← SSet.opFunctor.map_comp]
  apply SSet.yonedaEquiv.injective
  apply Prod.ext <;> decide

lemma roofPastingDenominator_target : stdSimplex.δ (0 : Fin 2) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofPastingSquareInclusion.{u} =
      stdSimplex.δ (0 : Fin 2) ≫ stdSimplex.δ (2 : Fin 3) ≫
        _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofPastingTriangleInclusion := by
  apply SSet.yonedaEquiv.injective
  apply Subtype.ext
  apply Prod.ext <;> decide

lemma roofPastingNumerator_target : stdSimplex.δ (0 : Fin 2) ≫
    stdSimplex.δ (1 : Fin 3) ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofPastingTriangleInclusion.{u} =
      stdSimplex.δ (0 : Fin 2) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofPastingSquareInclusion := by
  apply SSet.yonedaEquiv.injective
  apply Subtype.ext
  apply Prod.ext <;> decide

/-- 元の前段と同じ実分母の cospan。 -/
def roofPastingDenominatorCospan : (horn 2 2 : SSet.{u}) ⟶
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingCorner : SSet.{u}).op :=
  conePairCospan (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofPastingSquareInclusion)
    (stdSimplex.δ (2 : Fin 3) ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofPastingTriangleInclusion) roofPastingDenominator_target

/-- 同じ実分子と元の次辺の cospan。 -/
def roofPastingNumeratorCospan : (horn 2 2 : SSet.{u}) ⟶
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingCorner : SSet.{u}).op :=
  conePairCospan (stdSimplex.δ (1 : Fin 3) ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofPastingTriangleInclusion)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofPastingSquareInclusion) roofPastingNumerator_target

/-- join の頂点は同じ左因子または右因子から来る。 -/
lemma roofJoin_vertex_cases {K L : SSet.{u}} (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K L) _⦋0⦌) :
    (∃ x : K _⦋0⦌, (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K L).app (Opposite.op ⦋0⦌) x = s) ∨
      (∃ y : L _⦋0⦌, (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr K L).app (Opposite.op ⦋0⦌) y = s) := by
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
    {f g : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K L ⟶ (Δ[m] : SSet.{u}) ⊗ Δ[n]}
    (hl : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K L ≫ f = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K L ≫ g)
    (hr : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr K L ≫ f = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr K L ≫ g) : f = g := by
  have h₀ : f.app (Opposite.op ⦋0⦌) = g.app (Opposite.op ⦋0⦌) := by
    apply ConcreteCategory.hom_ext
    intro s
    rcases roofJoin_vertex_cases s with ⟨x, rfl⟩ | ⟨y, rfl⟩
    · exact congrArg (fun u : K ⟶ (Δ[m] : SSet.{u}) ⊗ Δ[n] =>
        u.app (Opposite.op ⦋0⦌) x) hl
    · exact congrArg (fun u : L ⟶ (Δ[m] : SSet.{u}) ⊗ Δ[n] =>
        u.app (Opposite.op ⦋0⦌) y) hr
  apply CartesianMonoidalCategory.hom_ext
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.stdSimplex_hom_ext_vertices
    apply ConcreteCategory.hom_ext
    intro s
    exact congrArg Prod.fst (ConcreteCategory.congr_hom h₀ s)
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.stdSimplex_hom_ext_vertices
    apply ConcreteCategory.hom_ext
    intro s
    exact congrArg Prod.snd (ConcreteCategory.congr_hom h₀ s)

lemma roofCospanSquareIso_inl :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{u}) (horn 2 2 : SSet.{u}) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso.hom =
      SSet.yonedaEquiv.symm
        (stdSimplex.obj₀Equiv.symm (0 : Fin 2), stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
  have hs := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneLegInclusion_source
    (SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 2) ≫ horn₂₂.ι₀₂) :
      (horn 2 2 : SSet.{u}) _⦋0⦌)
  rw [← hs, ← cospanConeSquare_bottom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  apply SSet.yonedaEquiv.injective
  apply Prod.ext <;> decide

/-- 分母側の面は、同じ二辺の cospan 上の同じ錐の正方形表示。 -/
lemma roofPastingPrismIso_denominator :
    (stdSimplex.δ (2 : Fin 3) ▷ (Δ[1] : SSet.{u})) ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofPastingPrismIso.inv =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso.inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 Δ[0]) roofPastingDenominatorCospan := by
  apply (cancel_mono _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofPastingPrismIso.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  apply (cancel_epi _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso.hom).mp
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  apply roofGrid_join_hom_ext
  · rw [← Category.assoc, roofCospanSquareIso_inl]
    rw [← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl _ _) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap _ _), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap,
      Category.id_comp, roofPastingPrismIso_inl]
    apply SSet.yonedaEquiv.injective
    apply Prod.ext <;> decide
  · rw [← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr _ _) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap _ _), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap,
      Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofPastingPrismIso_inr]
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary ≫ (stdSimplex.δ (2 : Fin 3) ▷ Δ[1]) = _
    apply horn₂₂.isPushout.hom_ext
    · rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary_rightEdge,
        ← Category.assoc, roofPastingDenominatorCospan, conePairCospan_first,
        Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofPastingSquareInclusion_corner]
      apply SSet.yonedaEquiv.injective
      apply Prod.ext <;> decide
    · rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary_topEdge,
        ← Category.assoc, roofPastingDenominatorCospan, conePairCospan_second,
        Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofPastingTriangleInclusion_corner]
      apply SSet.yonedaEquiv.injective
      apply Prod.ext <;> decide

/-- 分子側の面も、同じ二辺の cospan 上の同じ錐の転置正方形。 -/
lemma roofPastingPrismIso_numerator :
    (stdSimplex.δ (1 : Fin 3) ▷ (Δ[1] : SSet.{u})) ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofPastingPrismIso.inv =
      (β_ Δ[1] Δ[1]).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso.inv ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 Δ[0]) roofPastingNumeratorCospan := by
  apply (cancel_mono _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofPastingPrismIso.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  apply (cancel_epi (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso.hom ≫ (β_ Δ[1] Δ[1]).hom)).mp
  simp only [Category.assoc]
  rw [← Category.assoc (β_ Δ[1] Δ[1]).hom (β_ Δ[1] Δ[1]).hom,
    SymmetricCategory.symmetry, Category.id_comp,
    ← Category.assoc _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso.hom _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso.inv,
    Iso.hom_inv_id, Category.id_comp]
  apply roofGrid_join_hom_ext
  · rw [← Category.assoc, ← Category.assoc, roofCospanSquareIso_inl]
    rw [← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl _ _) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap _ _), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap,
      Category.id_comp, roofPastingPrismIso_inl]
    apply SSet.yonedaEquiv.injective
    apply Prod.ext <;> decide
  · rw [← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr _ _) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap _ _), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap,
      Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofPastingPrismIso_inr]
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary ≫ (β_ Δ[1] Δ[1]).hom ≫
      (stdSimplex.δ (1 : Fin 3) ▷ Δ[1]) = _
    apply horn₂₂.isPushout.hom_ext
    · rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary_rightEdge,
        ← Category.assoc (horn₂₂.ι₀₂) roofPastingNumeratorCospan,
        roofPastingNumeratorCospan, conePairCospan_first,
        Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofPastingTriangleInclusion_corner]
      apply SSet.yonedaEquiv.injective
      apply Prod.ext <;> decide
    · rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary_topEdge,
        ← Category.assoc (horn₂₂.ι₁₂) roofPastingNumeratorCospan,
        roofPastingNumeratorCospan, conePairCospan_second,
        Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofPastingSquareInclusion_corner]
      apply SSet.yonedaEquiv.injective
      apply Prod.ext <;> decide

variable {X : SSet.{u}} {a : (Δ[0] : SSet.{u}) ⟶ X}
  (F : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder a)
  (σ : (Δ[2] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder a)
  (hσ : stdSimplex.δ (0 : Fin 3) ≫ σ = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ F)

/-- 同じ五頂点の商 coslice 図式の全錐。 -/
def roofPastingCone : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofPastingCosliceDiagram F σ hσ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection a) :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofPastingCosliceDiagram F σ hσ), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.sliceUnderUncurry_projection _⟩

lemma roofPastingPrism_denominator : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofPastingPrism F σ hσ) 2 =
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso.inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 Δ[0]) roofPastingDenominatorCospan ≫
      (roofPastingCone F σ hσ).val := by
  change (stdSimplex.δ (2 : Fin 3) ▷ (Δ[1] : SSet.{u})) ≫
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofPastingPrismIso.inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry _) = _
  rw [← Category.assoc, roofPastingPrismIso_denominator]
  rfl

lemma roofPastingPrism_numerator : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofPastingPrism F σ hσ) 1 =
    (β_ Δ[1] Δ[1]).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso.inv ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 Δ[0]) roofPastingNumeratorCospan ≫ (roofPastingCone F σ hσ).val := by
  change (stdSimplex.δ (1 : Fin 3) ▷ (Δ[1] : SSet.{u})) ≫
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofPastingPrismIso.inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry _) = _
  rw [← Category.assoc, roofPastingPrismIso_numerator]
  rfl

lemma roofPastingCosliceDiagram_square : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofPastingSquareInclusion ≫
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofPastingCosliceDiagram F σ hσ = (β_ Δ[1] Δ[1]).hom ≫ F := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofPastingSquareInclusion, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofPastingCosliceDiagram]
  simp only [Category.assoc]
  rw [← Category.assoc (SSet.opFunctor.map _) (SSet.opFunctor.map _),
    ← SSet.opFunctor.map_comp, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingCornerGlue_left]
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofGridReverseIso_hom_map]
  exact _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.reverseGrid_double (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder a) (m := 1) (n := 1) ((β_ Δ[1] Δ[1]).hom ≫ F)

lemma roofPastingCosliceDiagram_triangle : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofPastingTriangleInclusion ≫
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofPastingCosliceDiagram F σ hσ = σ := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofPastingTriangleInclusion, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofPastingCosliceDiagram]
  simp only [Category.assoc]
  rw [← Category.assoc (SSet.opFunctor.map _) (SSet.opFunctor.map _),
    ← SSet.opFunctor.map_comp, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingCornerGlue_bottom]
  exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofReverseSimplex_double (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder a) σ

end SerrePositivity.KST.LocalizingInvariants
