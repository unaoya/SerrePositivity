module

public import SerrePositivity.AlgebraicGeometry.PerfectAffineVCoverCech
public import SerrePositivity.CommutativeAlgebra.ValuationInterval.Basic
public import SerrePositivity.HomologicalAlgebra.Cech.Composition

/-!
概要：完全F_p代数のarc被覆のČech完全性の、元の射と有限族の型を固定する。
方針：2hと同じ付値判定を階数1に制限し、指定したtensorの構造射で底変換する。
規約：零環・空の有限族を除外せず、任意の完全係数での普遍完全性を量化する。
使われ方：2iのU01〜U03・T00〜T05・O07。最終型はdrafts/A6/ArcRouteB.leanと同じ。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits
open SerrePositivity
open scoped Simplicial TensorProduct
namespace SerrePositivity.AlgebraicGeometry.ArcRouteB

/-- 計画T00：元の係数・射・増大項を保つ定義。 -/
abbrev ValuativeCoverFamily (rank : CommRingCat.{u} → Prop)
    {A : Type u} [CommRing A] {ι : Type u} [Finite ι]
    (B : ι → Type u) [∀ i, CommRing (B i)] (f : ∀ i, A →+* B i) : Prop :=
  SerrePositivity.AlgebraicGeometry.ValuativeCoverFamily rank B f

/-- 計画T01：元の係数・射・増大項を保つ定義。 -/
def IsVCoverFamily {A : Type u} [CommRing A] {ι : Type u} [Finite ι]
    (B : ι → Type u) [∀ i, CommRing (B i)] (f : ∀ i, A →+* B i) : Prop :=
  ValuativeCoverFamily (fun _ => True) B f

/-- 計画T02：元の係数・射・増大項を保つ定義。 -/
def IsArcCoverFamilyCharP {A : Type u} [CommRing A] {ι : Type u} [Finite ι]
    (B : ι → Type u) [∀ i, CommRing (B i)] (f : ∀ i, A →+* B i) : Prop :=
  ValuativeCoverFamily (fun V => ringKrullDim V ≤ 1) B f

/-- 計画T03：元の係数・射・増大項を保つ定義。 -/
def affineFamilyCech {A : Type u} [CommRing A] {ι : Type u} [Finite ι]
    (B : ι → Type u) [∀ i, CommRing (B i)] (f : ∀ i, A →+* B i) :
    CosimplicialObject.Augmented CommRingCat.{u} :=
  (Arrow.mk (CommRingCat.ofHom (RingHom.pi f))).augmentedCechConerve

/-- 計画T04：元の係数・射・増大項を保つ定義。 -/
def BS17VCechInput (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ {A : Type u} [CommRing A] [CharP A p] [PerfectRing A p]
    {ι : Type u} [Finite ι] (B : ι → Type u) [∀ i, CommRing (B i)]
    [∀ i, CharP (B i) p] [∀ i, PerfectRing (B i) p]
    (f : ∀ i, A →+* B i), IsVCoverFamily B f →
    Cech.AugmentedRingCechExact (affineFamilyCech B f)

/-- 計画T05：元の係数・射・増大項を保つ定義。 -/
def ArcRouteBGoal (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ {A : Type u} [CommRing A] [CharP A p] [PerfectRing A p]
    {ι : Type u} [Finite ι] (B : ι → Type u) [∀ i, CommRing (B i)]
    [∀ i, CharP (B i) p] [∀ i, PerfectRing (B i) p]
    (f : ∀ i, A →+* B i), IsArcCoverFamilyCharP B f →
    Cech.AugmentedRingCechExact (affineFamilyCech B f)

/-- 計画U01：元の係数・射・増大項を保つ定義。 -/
def arcBaseChangeHom {A B T : Type u} [CommRing A] [CommRing B]
    [CommRing T] (f : A →+* B) (g : A →+* T) :
    letI := f.toAlgebra; letI := g.toAlgebra
    T →+* T ⊗[A] B := by
  letI := f.toAlgebra
  letI := g.toAlgebra
  exact algebraMap T (T ⊗[A] B)

/-- 計画U02：元の係数・射・増大項を保つ定義。 -/
def PerfectRingCechUniversalExact (p : ℕ)
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) : Prop :=
  ∀ (T : Type u) [CommRing T] [PerfectRing T p] (g : A →+* T),
    Cech.IsCechExact (Arrow.mk (CommRingCat.ofHom (arcBaseChangeHom f g)))

/-- 計画U03：元の係数・射・増大項を保つ定義。 -/
def IsArcHom {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) : Prop :=
  ∀ (V : CommRingCat.{u}) [IsDomain V] [ValuationRing V],
    ringKrullDim V ≤ 1 → ∀ k : A →+* V,
    ∃ (W : CommRingCat.{u}) (hW : IsDomain W),
      letI : IsDomain W := hW
      ValuationRing W ∧ ringKrullDim W ≤ 1 ∧
      ∃ (e : V →+* W) (l : B →+* W), e.FaithfullyFlat ∧ l.comp f = e.comp k

/-- 計画O07：元の係数・射・増大項を保つ定義。 -/
def GoodArcInterval (p : ℕ) {V B : Type u} [CommRing V] [CommRing B]
    (f : V →+* B) (a b : PrimeSpectrum V) : Prop :=
  ∀ h : a ≤ b, PerfectRingCechUniversalExact p
    (arcBaseChangeHom f (algebraMap V (ValuationIntervalRing h)))

end SerrePositivity.AlgebraicGeometry.ArcRouteB
