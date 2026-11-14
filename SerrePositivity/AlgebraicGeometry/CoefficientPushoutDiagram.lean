module

public import SerrePositivity.AlgebraicGeometry.CoefficientSubalgebraDiagram
public import SerrePositivity.AlgebraicGeometry.FilteredPushoutRingPoint
public import SerrePositivity.AlgebraicGeometry.FilteredPushoutVCover
public import SerrePositivity.AlgebraicGeometry.AffineTensorModelPushout

/-!
概要：実際の係数部分代数と固定した代数の pushout を図式にし、元の tensor 模型を頂点に保つ。
方針：係数部分代数の余極限と、filtered pushout の普遍性を組み合わせる。
規約：元の環の Noether 性・係数射の忠実平坦性を要求しない。
使われ方：B03・B04 の模型からの有限個の射を共通の係数段へ因子化する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory Limits
open scoped TensorProduct
universe u
variable (A R : Type u) [CommRing A] [CommRing R] [Algebra A R]

/-- 各係数部分代数への、元の係数環からの自然な構造射。 -/
def coefficientSubalgebraBaseNatTrans :
    (Functor.const (Finset R)).obj (CommRingCat.of A) ⟶ coefficientSubalgebraDiagram A R where
  app j := CommRingCat.ofHom (algebraMap A (Algebra.adjoin A (j : Set R)))
  naturality {j m} f := by ext x; rfl

/-- 実際の係数 cocone は元の A-代数構造射と可換。 -/
theorem coefficientSubalgebraCocone_base (j : Finset R) :
    (coefficientSubalgebraBaseNatTrans A R).app j ≫
      (coefficientSubalgebraCocone A R).ι.app j =
      CommRingCat.ofHom (algebraMap A R) := by ext x; rfl

variable (S : Type u) [CommRing S] [Algebra A S]

/-- 各係数部分代数と S の実際の pushout の図式。 -/
def coefficientPushoutRingDiagram : Finset R ⥤ CommRingCat.{u} :=
  filteredPushoutRingDiagram (coefficientSubalgebraDiagram A R)
    (coefficientSubalgebraBaseNatTrans A R) (CommRingCat.ofHom (algebraMap A S))

/-- 各係数部分代数から pushout への自然変換。 -/
def coefficientPushoutBaseMap : coefficientSubalgebraDiagram A R ⟶
    coefficientPushoutRingDiagram A R S :=
  filteredPushoutRingInl (coefficientSubalgebraDiagram A R)
    (coefficientSubalgebraBaseNatTrans A R) (CommRingCat.ofHom (algebraMap A S))

/-- 固定した係数環から、各段の始域への構造射も自然変換。 -/
def coefficientPushoutRootMap : (Functor.const (Finset R)).obj (CommRingCat.of A) ⟶
    coefficientPushoutRingDiagram A R S :=
  coefficientSubalgebraBaseNatTrans A R ≫ coefficientPushoutBaseMap A R S

variable {C : Type u} [CommRing C] [Algebra R C] (e : R ⊗[A] S ≃ₐ[R] C)

/-- 元の tensor 模型 C を頂点に保つ、係数段ごとの pushout の cocone。 -/
def coefficientPushoutRingCocone : Cocone (coefficientPushoutRingDiagram A R S) :=
  filteredPushoutRingPointCocone (coefficientSubalgebraDiagram A R)
    (coefficientSubalgebraBaseNatTrans A R) (CommRingCat.ofHom (algebraMap A S))
    (coefficientSubalgebraCocone A R) (CommRingCat.ofHom (algebraMap A R))
    (coefficientSubalgebraCocone_base A R) (CommRingCat.ofHom (algebraMap R C))
    (CommRingCat.ofHom (e.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom))
    (isPushout_affineTensorModel e)

/-- 実際の tensor 模型 C は、係数段ごとの pushout の filtered colimit。 -/
def coefficientPushoutRingCoconeIsColimit : IsColimit (coefficientPushoutRingCocone A R S e) :=
  filteredPushoutRingPointCoconeIsColimit (coefficientSubalgebraDiagram A R)
    (coefficientSubalgebraBaseNatTrans A R) (CommRingCat.ofHom (algebraMap A S))
    (coefficientSubalgebraCocone A R) (CommRingCat.ofHom (algebraMap A R))
    (coefficientSubalgebraCocone_base A R) (CommRingCat.ofHom (algebraMap R C))
    (CommRingCat.ofHom (e.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom))
    (isPushout_affineTensorModel e) (coefficientSubalgebraCoconeIsColimit A R)

/-- 実際の模型への cocone は、係数部分代数からの挿入と可換。 -/
theorem coefficientPushoutRingCocone_base (j : Finset R) :
    (coefficientPushoutBaseMap A R S).app j ≫
      (coefficientPushoutRingCocone A R S e).ι.app j =
      (coefficientSubalgebraCocone A R).ι.app j ≫ CommRingCat.ofHom (algebraMap R C) :=
  filteredPushoutRingPointCocone_inl _ _ _ _ _ _ _ _ _ j

/-- 固定の S の挿入も、元の模型と全ての係数段で可換。 -/
theorem coefficientPushoutRingCocone_right (j : Finset R) :
    pushout.inr ((coefficientSubalgebraBaseNatTrans A R).app j)
      (CommRingCat.ofHom (algebraMap A S)) ≫
      (coefficientPushoutRingCocone A R S e).ι.app j =
      CommRingCat.ofHom (e.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom) :=
  filteredPushoutRingPointCocone_inr _ _ _ _ _ _ _ _ _ j

/-- cocone は固定した係数環からの構造射と可換。 -/
theorem coefficientPushoutRingCocone_root (j : Finset R) :
    (coefficientPushoutRootMap A R S).app j ≫
      (coefficientPushoutRingCocone A R S e).ι.app j =
      CommRingCat.ofHom (algebraMap A R) ≫ CommRingCat.ofHom (algebraMap R C) := by
  change ((coefficientSubalgebraBaseNatTrans A R).app j ≫
    (coefficientPushoutBaseMap A R S).app j) ≫ _ = _
  rw [Category.assoc, coefficientPushoutRingCocone_base,
    ← Category.assoc, coefficientSubalgebraCocone_base]

/-- 固定の射が v 被覆なら、係数段ごとの射も同じ付値判定を満たす。 -/
theorem coefficientPushoutBaseMap_vCover
    (h : IsAffineVCover (algebraMap A S)) (j : Finset R) :
    IsAffineVCover ((coefficientPushoutBaseMap A R S).app j).hom :=
  filteredPushoutRingInl_vCover _ _ _ h j

/-- 固定の射が有限型なら、係数段ごとの射も有限型。 -/
theorem coefficientPushoutBaseMap_finiteType [Algebra.FiniteType A S] (j : Finset R) :
    ((coefficientPushoutBaseMap A R S).app j).hom.FiniteType :=
  filteredPushoutRingInl_finiteType _ _ _ (RingHom.finiteType_algebraMap.mpr inferInstance) j

end SerrePositivity.AlgebraicGeometry
