module

public import SerrePositivity.AlgebraicGeometry.AugmentedCechCoordinates
public import SerrePositivity.AlgebraicGeometry.SchemeCechTupleCover
public import SerrePositivity.AlgebraicGeometry.SchemeCechNerveScalars
public import SerrePositivity.AlgebraicGeometry.SchemeStructurePerfectCechPullback

/-!
概要：二つの増大 nerve の積と、同じタプルの開と係数を定める。
方針：元の基底射の pullback と、二つの射影による逆像の交叉を取る。
規約：増大点でも同じ基底 Spec R を保持し、別の大域切断へ置き換えない。
使われ方：複体値の二重 Čech の幾何（計画 P06・P07・P11・P13・P14）。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
set_option backward.isDefEq.respectTransparency false

/-- 元の増大 nerve の、増大点を含めたタプル開。 -/
def augmentedTupleOpen {X S : Scheme.{u}} (f : X ⟶ S)
    {ι : Type} (U : ι → X.Opens) (a : AugmentedSimplexCategory)
    (t : Fin (augmentedTupleLength a) → ι) :
    ((AugmentedSimplexCategory.equivAugmentedSimplicialObject.inverse.obj
      (Arrow.mk f).augmentedCechNerve).obj (op a)).Opens := by
  cases a with
  | star => exact ⊤
  | of n => exact schemeCechTupleOpen f U (op n) t

/-- 元の二つの増大 nerve の、同じ基底上の積。 -/
def pairedCechScheme {R : Type u} [CommRing R] {X Y : Scheme.{u}}
    (h : X ⟶ Spec (CommRingCat.of R)) (g : Y ⟶ Spec (CommRingCat.of R))
    (a b : AugmentedSimplexCategory) : Scheme.{u} :=
  pullback (augmentedNerveBase h a) (augmentedNerveBase g b)

/-- 二つの元のタプル開の逆像の交叉。 -/
def pairedCechOpen {R : Type u} [CommRing R] {X Y : Scheme.{u}}
    (h : X ⟶ Spec (CommRingCat.of R)) (g : Y ⟶ Spec (CommRingCat.of R))
    {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (U : ι → X.Opens) (V : κ → Y.Opens)
    (a b : AugmentedSimplexCategory)
    (t : (Fin (augmentedTupleLength a) → ι) × (Fin (augmentedTupleLength b) → κ)) :
    (pairedCechScheme h g a b).Opens :=
  pullback.fst (augmentedNerveBase h a) (augmentedNerveBase g b) ⁻¹ᵁ
      augmentedTupleOpen h U a t.1 ⊓
    pullback.snd (augmentedNerveBase h a) (augmentedNerveBase g b) ⁻¹ᵁ
      augmentedTupleOpen g V b t.2

/-- 同じ基底環での p の零化は、積の各開の切断環に移る。 -/
theorem pairedCechPrimeCast {R : Type u} [CommRing R] {X Y : Scheme.{u}}
    (h : X ⟶ Spec (CommRingCat.of R)) (g : Y ⟶ Spec (CommRingCat.of R))
    (p : ℕ) (hR : (p : R) = 0) (a b : AugmentedSimplexCategory)
    (O : ((pairedCechScheme h g a b).Opens)ᵒᵖ) :
    (p : (pairedCechScheme h g a b).presheaf.obj O) = 0 :=
  schemeScalarPresheaf_primeCast _
    (pullback.fst (augmentedNerveBase h a) (augmentedNerveBase g b) ≫
      augmentedNerveBase h a) p hR O

/-- 同じ積のタプル開と元の Frobenius 係数による Čech 複体。 -/
def pairedPerfectCechComplex {R : Type u} [CommRing R] {X Y : Scheme.{u}}
    (h : X ⟶ Spec (CommRingCat.of R)) (g : Y ⟶ Spec (CommRingCat.of R))
    {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (U : ι → X.Opens) (V : κ → Y.Opens)
    (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0)
    (a b : AugmentedSimplexCategory) : CochainComplex (ModuleCat.{u} ℤ) ℕ :=
  fullCechComplex (openCoverCechDiagram
    (frobeniusRingDiagram (pairedCechScheme h g a b).presheaf p hp
      (pairedCechPrimeCast h g p hR a b)) (pairedCechOpen h g U V a b))

end SerrePositivity.AlgebraicGeometry
