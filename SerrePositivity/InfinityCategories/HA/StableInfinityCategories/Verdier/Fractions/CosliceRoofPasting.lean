module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Coslice
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.GridOpposite
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinReverse
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinReverseBoundary
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinReverseFactors
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinTensorPoint
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.PastingCorner
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.PastingCornerCocone
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.PastingShapes
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.PrismOpposite
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.Pullback
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.PushoutShape
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Slice
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.PastingCornerGluing
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.PastingCornerJoinIso
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.PastingLeftSquareIso

/-!
概要：指定商四角形と同じ coslice 内の分数三角形を、実合成三角柱へ貼る。
方針：五頂点の貼合せを反転し、始点の join 表示で三角柱へ戻す。
規約：元の全四角形と指定三角形を保持し、合成を Hom 類で選び直さない。
使われ方：回収した二つの実四角形の商像を元の商四角形へ接続する。
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
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions
open _root_.SerrePositivity.KST.LocalizingInvariants

/-- 両座標の反転をまとめた標準格子の同型。 -/
def roofGridReverseIso (m n : ℕ) :
    (Δ[m] : SSet.{u}) ⊗ Δ[n] ≅ ((Δ[m] : SSet.{u}) ⊗ Δ[n]).op :=
  tensorIso (stdSimplex.opIso ⦋m⦌).symm (stdSimplex.opIso ⦋n⦌).symm ≪≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.opTensorIso Δ[m] Δ[n]

lemma roofGridReverseIso_hom_map {X : SSet.{u}} {m n : ℕ}
    (f : (Δ[m] : SSet.{u}) ⊗ Δ[n] ⟶ X) :
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofGridReverseIso m n).hom ≫ SSet.opFunctor.map f = _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.reverseGrid f := rfl

/-- 五頂点図式の反転に同じ始点を付けた、三角柱全体の表示。 -/
def roofPastingPrismIso : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingCorner : SSet.{u}).op ≅
    (Δ[2] : SSet.{u}) ⊗ Δ[1] :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinIso (stdSimplex.opIso ⦋0⦌).symm (Iso.refl _) ≪≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableJoinReverseIso (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingCorner : SSet.{u}) Δ[0]).symm ≪≫
    SSet.opFunctor.mapIso _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingCornerJoinIso ≪≫
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofGridReverseIso 2 1).symm

/-- 三角柱の残る五頂点の包含。 -/
def roofPastingCornerInclusion : (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingCorner : SSet.{u}).op ⟶
    (Δ[2] : SSet.{u}) ⊗ Δ[1] :=
  SSet.opFunctor.map _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingCorner.ι ≫ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofGridReverseIso 2 1).inv

lemma roofPastingPrismIso_inr : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[0] : SSet.{u}) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingCorner : SSet.{u}).op ≫
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofPastingPrismIso.hom = _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofPastingCornerInclusion := by
  simp only [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofPastingPrismIso, Iso.trans_hom, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinIso, Iso.symm_hom,
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofPastingCornerInclusion]
  rw [← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr _ _) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap _ _), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap,
    Iso.refl_hom, Category.id_comp, ← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr _ _) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableJoinReverseIso _ _).inv,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableJoinReverse_inr_inv]
  simp only [Functor.mapIso_hom]
  rw [← Category.assoc, ← SSet.opFunctor.map_comp]
  change SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl _ _ ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingCornerCocone) ≫ _ = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingCornerCocone_inl]

/-- 原四角形の、反転した五頂点図式への包含。 -/
def roofPastingSquareInclusion : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingCorner : SSet.{u}).op :=
  (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofGridReverseIso 1 1).hom ≫ SSet.opFunctor.map _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingCornerLeftInclusion

lemma roofPastingSquareInclusion_corner : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofPastingSquareInclusion.{u} ≫
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofPastingCornerInclusion = stdSimplex.δ (0 : Fin 3) ▷ (Δ[1] : SSet.{u}) := by
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofGridReverseIso 2 1).hom).mp
  simp only [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofPastingSquareInclusion, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofPastingCornerInclusion,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← SSet.opFunctor.map_comp]
  have hi : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingCornerLeftInclusion.{u} ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingCorner.ι =
      stdSimplex.δ (2 : Fin 3) ▷ (Δ[1] : SSet.{u}) := by
    change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingLeftSquareIso.hom ≫
      (Subcomplex.homOfLE _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingLeftSquare_le_corner ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingCorner.ι) = _
    exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingLeftSquareIso_hom_ι
  rw [hi]
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨s, t⟩
  apply Prod.ext
  · apply SSet.stdSimplex.ext
    intro j
    change (SimplexCategory.δ (2 : Fin 3)).toOrderHom ((s j.rev).rev) =
      ((SimplexCategory.δ (0 : Fin 3)).toOrderHom (s j.rev)).rev
    exact (by decide : ∀ v : Fin 2,
      (SimplexCategory.δ (2 : Fin 3)).toOrderHom v.rev =
        ((SimplexCategory.δ (0 : Fin 3)).toOrderHom v).rev) (s j.rev)
  · rfl

/-- 指定分数三角形の、反転した五頂点図式への包含。 -/
def roofPastingTriangleInclusion : (Δ[2] : SSet.{u}) ⟶
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingCorner : SSet.{u}).op :=
  (stdSimplex.opIso ⦋2⦌).inv ≫ SSet.opFunctor.map _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingCornerBottomInclusion

lemma roofPastingTriangleInclusion_corner : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofPastingTriangleInclusion.{u} ≫
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofPastingCornerInclusion = CartesianMonoidalCategory.lift (𝟙 Δ[2])
      (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) := by
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofGridReverseIso 2 1).hom).mp
  simp only [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofPastingTriangleInclusion, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofPastingCornerInclusion,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← SSet.opFunctor.map_comp]
  have hi : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingCornerBottomInclusion.{u} ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingCorner.ι =
      CartesianMonoidalCategory.lift (𝟙 Δ[2])
        (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro t
    rfl
  rw [hi]
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro t
  rfl

/-- 同じ指定単体を、頂点順と値域を同時に反転する。 -/
def roofReverseSimplex {X : SSet.{u}} {n : ℕ} (f : (Δ[n] : SSet.{u}) ⟶ X) :
    (Δ[n] : SSet.{u}) ⟶ X.op :=
  (stdSimplex.opIso ⦋n⦌).inv ≫ SSet.opFunctor.map f

lemma roofReverseSquare_bottom {X : SSet.{u}}
    (F : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.reverseGrid ((β_ Δ[1] Δ[1]).hom ≫ F) =
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofReverseSimplex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ F) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  rfl

lemma roofReverseTriangle_last {X : SSet.{u}} (σ : (Δ[2] : SSet.{u}) ⟶ X) :
    stdSimplex.δ (2 : Fin 3) ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofReverseSimplex σ =
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofReverseSimplex (stdSimplex.δ (0 : Fin 3) ≫ σ) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  change SSet.opObjEquiv.symm (σ.app _ _) = SSet.opObjEquiv.symm (σ.app _ _)
  congr 2
  apply SSet.stdSimplex.ext
  intro j
  change ((SimplexCategory.δ (2 : Fin 3)).toOrderHom (s j.rev)).rev =
    (SimplexCategory.δ (0 : Fin 3)).toOrderHom ((s j.rev).rev)
  exact (by decide : ∀ v : Fin 2,
    ((SimplexCategory.δ (2 : Fin 3)).toOrderHom v).rev =
      (SimplexCategory.δ (0 : Fin 3)).toOrderHom v.rev) (s j.rev)

lemma roofReverseSimplex_double {X : SSet.{u}} {n : ℕ}
    (f : (Δ[n] : SSet.{u}) ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofReverseSimplex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofReverseSimplex f) ≫
      (SSet.opFunctorCompOpFunctorIso.app X).hom = f := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  intro t
  change f.app _ _ = f.app _ t
  congr 1
  apply SSet.stdSimplex.ext
  intro j
  change ((t j.rev.rev).rev).rev = t j
  simp

/-- 元の商四角形と実分数三角形の同じ共有辺に沿う、五頂点の全 coslice 図式。 -/
def roofPastingCosliceDiagram {X : SSet.{u}} {a : (Δ[0] : SSet.{u}) ⟶ X}
    (F : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder a)
    (σ : (Δ[2] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder a)
    (hσ : stdSimplex.δ (0 : Fin 3) ≫ σ = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ F) :
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingCorner : SSet.{u}).op ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder a :=
  SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingCornerGlue
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.reverseGrid ((β_ Δ[1] Δ[1]).hom ≫ F)) (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofReverseSimplex σ) (by
      rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofReverseSquare_bottom, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofReverseTriangle_last, hσ])) ≫
    (SSet.opFunctorCompOpFunctorIso.app (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder a)).hom

/-- 全 coslice 貼合せから取り出す、同じ指定商四角形を含む実合成三角柱。 -/
def roofPastingPrism {X : SSet.{u}} {a : (Δ[0] : SSet.{u}) ⟶ X}
    (F : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder a)
    (σ : (Δ[2] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder a)
    (hσ : stdSimplex.δ (0 : Fin 3) ≫ σ = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ F) :
    (Δ[2] ⊗ Δ[1] : SSet.{u}) ⟶ X :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofPastingPrismIso.inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofPastingCosliceDiagram F σ hσ)

/-- 同じ商四角形を、三角柱の元の面として厳密に保持する。 -/
lemma roofPastingPrism_original {X : SSet.{u}} {a : (Δ[0] : SSet.{u}) ⟶ X}
    (F : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder a)
    (σ : (Δ[2] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder a)
    (hσ : stdSimplex.δ (0 : Fin 3) ≫ σ = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ F) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofPastingPrism F σ hσ) 0 =
      (β_ Δ[1] Δ[1]).hom ≫ F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection a := by
  have hi : (stdSimplex.δ (0 : Fin 3) ▷ (Δ[1] : SSet.{u})) ≫
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofPastingPrismIso.inv = _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofPastingSquareInclusion ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[0] _ := by
    apply (cancel_mono _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofPastingPrismIso.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofPastingPrismIso_inr, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofPastingSquareInclusion_corner]
  change (stdSimplex.δ (0 : Fin 3) ▷ (Δ[1] : SSet.{u})) ≫
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofPastingPrismIso.inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry _) = _
  rw [← Category.assoc, hi, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.sliceUnderUncurry_projection]
  change (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofPastingSquareInclusion ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofPastingCosliceDiagram F σ hσ) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection a = ((β_ Δ[1] Δ[1]).hom ≫ F) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection a
  apply congrArg (fun f : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder a =>
    f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection a)
  dsimp only [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofPastingSquareInclusion, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofPastingCosliceDiagram]
  simp only [Category.assoc]
  rw [← Category.assoc (SSet.opFunctor.map _) (SSet.opFunctor.map _),
    ← SSet.opFunctor.map_comp, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingCornerGlue_left]
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofGridReverseIso_hom_map]
  exact _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.reverseGrid_double (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder a) (m := 1) (n := 1) ((β_ Δ[1] Δ[1]).hom ≫ F)

/-- 三角柱の終端列は、同じ指定分数三角形の商射影そのもの。 -/
lemma roofPastingPrism_top {X : SSet.{u}} {a : (Δ[0] : SSet.{u}) ⟶ X}
    (F : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder a)
    (σ : (Δ[2] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder a)
    (hσ : stdSimplex.δ (0 : Fin 3) ≫ σ = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ F) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingTopTriangle (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofPastingPrism F σ hσ) = σ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection a := by
  have hi : CartesianMonoidalCategory.lift (𝟙 (Δ[2] : SSet.{u}))
        (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) ≫
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofPastingPrismIso.inv = _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofPastingTriangleInclusion ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[0] _ := by
    apply (cancel_mono _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofPastingPrismIso.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofPastingPrismIso_inr, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofPastingTriangleInclusion_corner]
  change CartesianMonoidalCategory.lift (𝟙 (Δ[2] : SSet.{u}))
      (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) ≫
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofPastingPrismIso.inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry _) = _
  rw [← Category.assoc, hi, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.sliceUnderUncurry_projection]
  change (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofPastingTriangleInclusion ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofPastingCosliceDiagram F σ hσ) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection a = σ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection a
  apply congrArg (fun f : (Δ[2] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder a => f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection a)
  dsimp only [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofPastingTriangleInclusion, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofPastingCosliceDiagram]
  simp only [Category.assoc]
  rw [← Category.assoc (SSet.opFunctor.map _) (SSet.opFunctor.map _),
    ← SSet.opFunctor.map_comp, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingCornerGlue_bottom]
  exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofReverseSimplex_double (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder a) σ

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofGridReverseIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.roofGridReverseIso := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofGridReverseIso

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.roofGridReverseIso_hom_map := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofGridReverseIso_hom_map

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofPastingCornerInclusion (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.roofPastingCornerInclusion := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofPastingCornerInclusion

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofPastingCosliceDiagram (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.roofPastingCosliceDiagram := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofPastingCosliceDiagram

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofPastingPrism (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.roofPastingPrism := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofPastingPrism

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofPastingPrismIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.roofPastingPrismIso := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofPastingPrismIso

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.roofPastingPrismIso_inr := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofPastingPrismIso_inr

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.roofPastingPrism_original := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofPastingPrism_original

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.roofPastingPrism_top := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofPastingPrism_top

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofPastingSquareInclusion (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.roofPastingSquareInclusion := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofPastingSquareInclusion

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.roofPastingSquareInclusion_corner := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofPastingSquareInclusion_corner

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofPastingTriangleInclusion (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.roofPastingTriangleInclusion := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofPastingTriangleInclusion

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.roofPastingTriangleInclusion_corner := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofPastingTriangleInclusion_corner

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofReverseSimplex (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.roofReverseSimplex := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofReverseSimplex

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.roofReverseSimplex_double := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofReverseSimplex_double

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.roofReverseSquare_bottom := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofReverseSquare_bottom

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.roofReverseTriangle_last := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofReverseTriangle_last

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.roofPastingCornerInclusion.eq_1 := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofPastingCornerInclusion.eq_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.roofPastingCosliceDiagram._proof_1 := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofPastingCosliceDiagram._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.roofPastingCosliceDiagram._proof_2 := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofPastingCosliceDiagram._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.roofPastingPrismIso.eq_1 := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofPastingPrismIso.eq_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.roofPastingSquareInclusion.eq_1 := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofPastingSquareInclusion.eq_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.roofPastingTriangleInclusion.eq_1 := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofPastingTriangleInclusion.eq_1
