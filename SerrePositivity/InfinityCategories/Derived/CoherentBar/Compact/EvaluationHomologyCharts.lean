module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.EvaluationHomologyCoefficients
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.HomologyChartsPiData
/-!
概要：元の bar の実評価空間と、同じホモロジー余錐の自然なチャート。
方針：全基点比較を既存 H⁰ 図式の対象同型で送る。
規約：実頂点・transition・余錐の全脚を保つ。
使われ方：filtered 空間判定の元ごとの五条件と native compact 性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open SerrePositivity.KST.Spectra
open scoped Simplicial
lemma DGBarCompactPiChartNaturality.reparam_source
    {X Y : SSet.{u}} [KanComplex X] [KanComplex Y] {n : ℕ}
    {A A' : Type v} {B : Type w} {c : DGBarCompactPiChart X n A}
    {c' : DGBarCompactPiChart Y n B} {f : X ⟶ Y} {φ : A → B}
    (h : DGBarCompactPiChartNaturality c c' f φ) (α : A ≃ A') (ψ : A' → B)
    (hψ : ∀ a, φ a = ψ (α a)) :
    DGBarCompactPiChartNaturality (c.postcompose α) c' f ψ :=
  ⟨fun x a => (h.app x a).trans (hψ (c.equiv x a))⟩

lemma dgBarCompactPiZeroChart_reparam_source
    {X Y : SSet.{u}} {A A' : Type v} {B : Type w}
    (c : SSet.π₀ X ≃ A) (c' : SSet.π₀ Y ≃ B) (f : X ⟶ Y)
    (φ : A → B) (h : ∀ a, c' (SSet.mapπ₀ f a) = φ (c a))
    (α : A ≃ A') (ψ : A' → B) (hψ : ∀ a, φ a = ψ (α a)) (a : SSet.π₀ X) :
    c' (SSet.mapπ₀ f a) = ψ ((c.trans α) a) :=
  (h a).trans (hψ (c a))

structure DGBarCompactPiZeroChartNaturality {X Y : SSet.{u}}
    {A : Type v} {B : Type w} (c : SSet.π₀ X ≃ A) (c' : SSet.π₀ Y ≃ B)
    (f : X ⟶ Y) (φ : A → B) : Prop where
  app : ∀ a, c' (SSet.mapπ₀ f a) = φ (c a)

lemma DGBarCompactPiZeroChartNaturality.cast {X X' Y Y' : SSet.{u}}
    {A : Type v} {B : Type w} {c : SSet.π₀ X ≃ A} {c' : SSet.π₀ Y ≃ B}
    {f : X ⟶ Y} {φ : A → B} (h : DGBarCompactPiZeroChartNaturality c c' f φ)
    (hx : X = X') (hy : Y = Y') :
    DGBarCompactPiZeroChartNaturality (dgBarCompactPiZeroChart_cast hx c)
      (dgBarCompactPiZeroChart_cast hy c') (dgBarCompactSpaceMapCast hx hy f) φ :=
  ⟨dgBarCompactPiZeroChart_cast_naturality hx hy c c' f φ h.app⟩

lemma DGBarCompactPiZeroChartNaturality.reparam_source {X Y : SSet.{u}}
    {A A' : Type v} {B : Type w} {c : SSet.π₀ X ≃ A} {c' : SSet.π₀ Y ≃ B}
    {f : X ⟶ Y} {φ : A → B} (h : DGBarCompactPiZeroChartNaturality c c' f φ)
    (α : A ≃ A') (ψ : A' → B) (hψ : ∀ a, φ a = ψ (α a)) :
    DGBarCompactPiZeroChartNaturality (c.trans α) c' f ψ :=
  ⟨fun a => (h.app a).trans (hψ (c a))⟩

variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : Type u} [PartialOrder I]
  (G : (SSet.uliftFunctor.{max (u + 1) v, u}).obj (nerve I) ⟶ dgProjectiveModuleNerve R D)
  (c : JoinCocone G) (x : D)

abbrev dgBarCompactEvaluationCoefficientDiagram (n : ℕ) :=
  dgCoherentBarHomologyDiagram R D (dgProjectiveBarDiagram R D G) x (-(n : ℤ))

abbrev dgBarCompactEvaluationCoefficientCocone (n : ℕ) :=
  dgCoherentCoconeHomology R D (dgProjectiveBarDiagram R D G)
    (fullInclusionCocone R (RightModule R D) (dgModuleProjectiveProperty R D)
      c) x (-(n : ℤ))

def dgBarCompactEvaluationStagePiChart (n : ℕ) (i : I) :
    DGBarCompactPiChart
      (dgBarCompactSpaceStage (dgBarCompactEvaluationPosetDiagram R D G x) i).obj n
      ((dgBarCompactEvaluationCoefficientDiagram R D G x (n + 1)).obj i) :=
  (dgBarCompactEvaluationVertexPiChart R D x (dgBarCompactEvaluationStageVertex R D G i) n).postcompose
    (dgBarCompactEvaluationStageHomologyIso R D G x (-((n + 1 : ℕ) : ℤ)) i).symm.toLinearEquiv.toEquiv

def dgBarCompactEvaluationStagePiZeroChart (i : I) :
    SSet.π₀ (dgBarCompactSpaceStage (dgBarCompactEvaluationPosetDiagram R D G x) i).obj ≃
      ((dgBarCompactEvaluationCoefficientDiagram R D G x 0).obj i) :=
  (dgBarCompactEvaluationVertexPiZeroChart R D x (dgBarCompactEvaluationStageVertex R D G i)).trans
    (dgBarCompactEvaluationStageHomologyIso R D G x 0 i).symm.toLinearEquiv.toEquiv

def dgBarCompactEvaluationApexPiChart (n : ℕ) :
    DGBarCompactPiChart
      (dgBarCompactSpaceApex (dgBarCompactEvaluationPosetDiagram R D G x)
        (dgBarCompactEvaluationCocone R D G c x)).obj n
      (dgBarCompactEvaluationCoefficientCocone R D G c x (n + 1)).pt :=
  (dgBarCompactEvaluationVertexPiChart R D x c.vertex n).cast
    (dgBarCompactEvaluationApexSpace_eq R D G c x)

def dgBarCompactEvaluationApexPiZeroChart :
    SSet.π₀ (dgBarCompactSpaceApex (dgBarCompactEvaluationPosetDiagram R D G x)
      (dgBarCompactEvaluationCocone R D G c x)).obj ≃
      (dgBarCompactEvaluationCoefficientCocone R D G c x 0).pt :=
  dgBarCompactPiZeroChart_cast (dgBarCompactEvaluationApexSpace_eq R D G c x)
    (dgBarCompactEvaluationVertexPiZeroChart R D x c.vertex)

end SerrePositivity.InfinityCategories
