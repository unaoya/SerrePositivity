module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Core.Coslice
public import SerrePositivity.InfinityCategories.Core.GridOpposite
public import SerrePositivity.InfinityCategories.Core.Join
public import SerrePositivity.InfinityCategories.Core.JoinReverse
public import SerrePositivity.InfinityCategories.Core.JoinReverseBoundary
public import SerrePositivity.InfinityCategories.Core.JoinReverseFactors
public import SerrePositivity.InfinityCategories.Core.JoinTensorPoint
public import SerrePositivity.InfinityCategories.Core.PastingCorner
public import SerrePositivity.InfinityCategories.Core.PastingCornerCocone
public import SerrePositivity.InfinityCategories.Core.PastingShapes
public import SerrePositivity.InfinityCategories.Core.PrismOpposite
public import SerrePositivity.InfinityCategories.Core.Pullback
public import SerrePositivity.InfinityCategories.Core.PushoutShape
public import SerrePositivity.InfinityCategories.Core.RightFibration
public import SerrePositivity.InfinityCategories.Core.Slice
public import SerrePositivity.InfinityCategories.Stable.PastingCornerGluing
public import SerrePositivity.InfinityCategories.Stable.PastingCornerJoinIso
public import SerrePositivity.InfinityCategories.Stable.PastingLeftSquareIso

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
namespace SerrePositivity.InfinityCategories.Stable.Verdier.Fractions
open SerrePositivity.KST.LocalizingInvariants

/-- 両座標の反転をまとめた標準格子の同型。 -/
def roofGridReverseIso (m n : ℕ) :
    (Δ[m] : SSet.{u}) ⊗ Δ[n] ≅ ((Δ[m] : SSet.{u}) ⊗ Δ[n]).op :=
  tensorIso (stdSimplex.opIso ⦋m⦌).symm (stdSimplex.opIso ⦋n⦌).symm ≪≫
    opTensorIso Δ[m] Δ[n]

lemma roofGridReverseIso_hom_map {X : SSet.{u}} {m n : ℕ}
    (f : (Δ[m] : SSet.{u}) ⊗ Δ[n] ⟶ X) :
    (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofGridReverseIso m n).hom ≫ SSet.opFunctor.map f = reverseGrid f := rfl

/-- 五頂点図式の反転に同じ始点を付けた、三角柱全体の表示。 -/
def roofPastingPrismIso : join (Δ[0] : SSet.{u}) (pastingCorner : SSet.{u}).op ≅
    (Δ[2] : SSet.{u}) ⊗ Δ[1] :=
  joinIso (stdSimplex.opIso ⦋0⦌).symm (Iso.refl _) ≪≫
    (stableJoinReverseIso (pastingCorner : SSet.{u}) Δ[0]).symm ≪≫
    SSet.opFunctor.mapIso pastingCornerJoinIso ≪≫
    (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofGridReverseIso 2 1).symm

/-- 三角柱の残る五頂点の包含。 -/
def roofPastingCornerInclusion : (pastingCorner : SSet.{u}).op ⟶
    (Δ[2] : SSet.{u}) ⊗ Δ[1] :=
  SSet.opFunctor.map pastingCorner.ι ≫ (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofGridReverseIso 2 1).inv

lemma roofPastingPrismIso_inr : joinInr (Δ[0] : SSet.{u}) (pastingCorner : SSet.{u}).op ≫
    _root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofPastingPrismIso.hom = _root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofPastingCornerInclusion := by
  simp only [_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofPastingPrismIso, Iso.trans_hom, joinIso, Iso.symm_hom,
    _root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofPastingCornerInclusion]
  rw [← Category.assoc (joinInr _ _) (joinMap _ _), joinInr_joinMap,
    Iso.refl_hom, Category.id_comp, ← Category.assoc (joinInr _ _) (stableJoinReverseIso _ _).inv,
    stableJoinReverse_inr_inv]
  simp only [Functor.mapIso_hom]
  rw [← Category.assoc, ← SSet.opFunctor.map_comp]
  change SSet.opFunctor.map (joinInl _ _ ≫ pastingCornerCocone) ≫ _ = _
  rw [pastingCornerCocone_inl]

/-- 原四角形の、反転した五頂点図式への包含。 -/
def roofPastingSquareInclusion : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶
    (pastingCorner : SSet.{u}).op :=
  (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofGridReverseIso 1 1).hom ≫ SSet.opFunctor.map pastingCornerLeftInclusion

lemma roofPastingSquareInclusion_corner : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofPastingSquareInclusion.{u} ≫
    _root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofPastingCornerInclusion = stdSimplex.δ (0 : Fin 3) ▷ (Δ[1] : SSet.{u}) := by
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofGridReverseIso 2 1).hom).mp
  simp only [_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofPastingSquareInclusion, _root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofPastingCornerInclusion,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← SSet.opFunctor.map_comp]
  have hi : pastingCornerLeftInclusion.{u} ≫ pastingCorner.ι =
      stdSimplex.δ (2 : Fin 3) ▷ (Δ[1] : SSet.{u}) := by
    change pastingLeftSquareIso.hom ≫
      (Subcomplex.homOfLE pastingLeftSquare_le_corner ≫ pastingCorner.ι) = _
    exact pastingLeftSquareIso_hom_ι
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
    (pastingCorner : SSet.{u}).op :=
  (stdSimplex.opIso ⦋2⦌).inv ≫ SSet.opFunctor.map pastingCornerBottomInclusion

lemma roofPastingTriangleInclusion_corner : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofPastingTriangleInclusion.{u} ≫
    _root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofPastingCornerInclusion = CartesianMonoidalCategory.lift (𝟙 Δ[2])
      (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) := by
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofGridReverseIso 2 1).hom).mp
  simp only [_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofPastingTriangleInclusion, _root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofPastingCornerInclusion,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← SSet.opFunctor.map_comp]
  have hi : pastingCornerBottomInclusion.{u} ≫ pastingCorner.ι =
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
    squareBottomEdge ≫ reverseGrid ((β_ Δ[1] Δ[1]).hom ≫ F) =
      _root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofReverseSimplex (squareRightEdge ≫ F) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  rfl

lemma roofReverseTriangle_last {X : SSet.{u}} (σ : (Δ[2] : SSet.{u}) ⟶ X) :
    stdSimplex.δ (2 : Fin 3) ≫ _root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofReverseSimplex σ =
      _root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofReverseSimplex (stdSimplex.δ (0 : Fin 3) ≫ σ) := by
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
    _root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofReverseSimplex (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofReverseSimplex f) ≫
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
    (F : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ sliceUnder a)
    (σ : (Δ[2] : SSet.{u}) ⟶ sliceUnder a)
    (hσ : stdSimplex.δ (0 : Fin 3) ≫ σ = squareRightEdge ≫ F) :
    (pastingCorner : SSet.{u}).op ⟶ sliceUnder a :=
  SSet.opFunctor.map (pastingCornerGlue
    (reverseGrid ((β_ Δ[1] Δ[1]).hom ≫ F)) (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofReverseSimplex σ) (by
      rw [_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofReverseSquare_bottom, _root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofReverseTriangle_last, hσ])) ≫
    (SSet.opFunctorCompOpFunctorIso.app (sliceUnder a)).hom

/-- 全 coslice 貼合せから取り出す、同じ指定商四角形を含む実合成三角柱。 -/
def roofPastingPrism {X : SSet.{u}} {a : (Δ[0] : SSet.{u}) ⟶ X}
    (F : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ sliceUnder a)
    (σ : (Δ[2] : SSet.{u}) ⟶ sliceUnder a)
    (hσ : stdSimplex.δ (0 : Fin 3) ≫ σ = squareRightEdge ≫ F) :
    (Δ[2] ⊗ Δ[1] : SSet.{u}) ⟶ X :=
  _root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofPastingPrismIso.inv ≫ sliceUnderUncurry (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofPastingCosliceDiagram F σ hσ)

/-- 同じ商四角形を、三角柱の元の面として厳密に保持する。 -/
lemma roofPastingPrism_original {X : SSet.{u}} {a : (Δ[0] : SSet.{u}) ⟶ X}
    (F : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ sliceUnder a)
    (σ : (Δ[2] : SSet.{u}) ⟶ sliceUnder a)
    (hσ : stdSimplex.δ (0 : Fin 3) ≫ σ = squareRightEdge ≫ F) :
    pastingSquare (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofPastingPrism F σ hσ) 0 =
      (β_ Δ[1] Δ[1]).hom ≫ F ≫ sliceUnderProjection a := by
  have hi : (stdSimplex.δ (0 : Fin 3) ▷ (Δ[1] : SSet.{u})) ≫
      _root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofPastingPrismIso.inv = _root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofPastingSquareInclusion ≫ joinInr Δ[0] _ := by
    apply (cancel_mono _root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofPastingPrismIso.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofPastingPrismIso_inr, _root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofPastingSquareInclusion_corner]
  change (stdSimplex.δ (0 : Fin 3) ▷ (Δ[1] : SSet.{u})) ≫
    (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofPastingPrismIso.inv ≫ sliceUnderUncurry _) = _
  rw [← Category.assoc, hi, Category.assoc, sliceUnderUncurry_projection]
  change (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofPastingSquareInclusion ≫ _root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofPastingCosliceDiagram F σ hσ) ≫
    sliceUnderProjection a = ((β_ Δ[1] Δ[1]).hom ≫ F) ≫ sliceUnderProjection a
  apply congrArg (fun f : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ sliceUnder a =>
    f ≫ sliceUnderProjection a)
  dsimp only [_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofPastingSquareInclusion, _root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofPastingCosliceDiagram]
  simp only [Category.assoc]
  rw [← Category.assoc (SSet.opFunctor.map _) (SSet.opFunctor.map _),
    ← SSet.opFunctor.map_comp, pastingCornerGlue_left]
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofGridReverseIso_hom_map]
  exact reverseGrid_double (X := sliceUnder a) (m := 1) (n := 1) ((β_ Δ[1] Δ[1]).hom ≫ F)

/-- 三角柱の終端列は、同じ指定分数三角形の商射影そのもの。 -/
lemma roofPastingPrism_top {X : SSet.{u}} {a : (Δ[0] : SSet.{u}) ⟶ X}
    (F : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ sliceUnder a)
    (σ : (Δ[2] : SSet.{u}) ⟶ sliceUnder a)
    (hσ : stdSimplex.δ (0 : Fin 3) ≫ σ = squareRightEdge ≫ F) :
    pastingTopTriangle (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofPastingPrism F σ hσ) = σ ≫ sliceUnderProjection a := by
  have hi : CartesianMonoidalCategory.lift (𝟙 (Δ[2] : SSet.{u}))
        (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) ≫
      _root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofPastingPrismIso.inv = _root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofPastingTriangleInclusion ≫ joinInr Δ[0] _ := by
    apply (cancel_mono _root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofPastingPrismIso.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofPastingPrismIso_inr, _root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofPastingTriangleInclusion_corner]
  change CartesianMonoidalCategory.lift (𝟙 (Δ[2] : SSet.{u}))
      (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) ≫
    (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofPastingPrismIso.inv ≫ sliceUnderUncurry _) = _
  rw [← Category.assoc, hi, Category.assoc, sliceUnderUncurry_projection]
  change (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofPastingTriangleInclusion ≫ _root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofPastingCosliceDiagram F σ hσ) ≫
    sliceUnderProjection a = σ ≫ sliceUnderProjection a
  apply congrArg (fun f : (Δ[2] : SSet.{u}) ⟶ sliceUnder a => f ≫ sliceUnderProjection a)
  dsimp only [_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofPastingTriangleInclusion, _root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofPastingCosliceDiagram]
  simp only [Category.assoc]
  rw [← Category.assoc (SSet.opFunctor.map _) (SSet.opFunctor.map _),
    ← SSet.opFunctor.map_comp, pastingCornerGlue_bottom]
  exact _root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofReverseSimplex_double (X := sliceUnder a) σ

end SerrePositivity.InfinityCategories.Stable.Verdier.Fractions

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofGridReverseIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.roofGridReverseIso := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofGridReverseIso

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.roofGridReverseIso_hom_map := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofGridReverseIso_hom_map

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofPastingCornerInclusion (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.roofPastingCornerInclusion := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofPastingCornerInclusion

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofPastingCosliceDiagram (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.roofPastingCosliceDiagram := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofPastingCosliceDiagram

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofPastingPrism (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.roofPastingPrism := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofPastingPrism

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofPastingPrismIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.roofPastingPrismIso := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofPastingPrismIso

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.roofPastingPrismIso_inr := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofPastingPrismIso_inr

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.roofPastingPrism_original := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofPastingPrism_original

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.roofPastingPrism_top := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofPastingPrism_top

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofPastingSquareInclusion (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.roofPastingSquareInclusion := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofPastingSquareInclusion

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.roofPastingSquareInclusion_corner := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofPastingSquareInclusion_corner

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofPastingTriangleInclusion (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.roofPastingTriangleInclusion := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofPastingTriangleInclusion

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.roofPastingTriangleInclusion_corner := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofPastingTriangleInclusion_corner

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofReverseSimplex (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.roofReverseSimplex := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofReverseSimplex

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.roofReverseSimplex_double := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofReverseSimplex_double

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.roofReverseSquare_bottom := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofReverseSquare_bottom

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.roofReverseTriangle_last := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofReverseTriangle_last

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.roofPastingCornerInclusion.eq_1 := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofPastingCornerInclusion.eq_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.roofPastingCosliceDiagram._proof_1 := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofPastingCosliceDiagram._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.roofPastingCosliceDiagram._proof_2 := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofPastingCosliceDiagram._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.roofPastingPrismIso.eq_1 := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofPastingPrismIso.eq_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.roofPastingSquareInclusion.eq_1 := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofPastingSquareInclusion.eq_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.roofPastingTriangleInclusion.eq_1 := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.roofPastingTriangleInclusion.eq_1
