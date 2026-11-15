module

public import SerrePositivity.AlgebraicGeometry.CoefficientPushoutVCoverModel
public import SerrePositivity.AlgebraicGeometry.CoefficientVCoverDiagramFunctor

/-!
概要：実際の係数段の被覆模型と遷移を、模型の圏への関手にまとめる。
方針：係数と両辺の自然性、元の cocone の可換式から遷移の五つの式を確認する。
規約：元の環写像への正方形と実際の両辺の環の射を保持する。
使われ方：B03・B04 の固定した有限表示模型からの被覆模型の図式。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory Limits
open scoped TensorProduct
universe u
variable (k A R S : Type u) [CommRing k] [CommRing A] [CommRing R] [CommRing S]
  [Algebra k R] [Algebra A R] [Algebra A S] [Algebra.FiniteType A S]
  {T C : Type u} [CommRing T] [CommRing C] [Algebra R T] [Algebra k C]
  (g : R →ₐ[k] C) (e : R ⊗[A] S ≃ₐ[R] T)
  (κ : k →+* A) (hκ : κ.FiniteType)
  (hκR : (algebraMap A R).comp κ = algebraMap k R)
  (p : T →+* C) (hp : p.comp (algebraMap R T) = g.toRingHom)
  (hv : IsAffineVCover (algebraMap A S))

/-- 固定した実際の模型からの係数段の被覆模型は、実際の関手をなす。 -/
def coefficientPushoutVCoverModelFunctor : Finset R ⥤ CoefficientVCoverModelCategory k g := by
  let α : (Functor.const (Finset R)).obj (CommRingCat.of k) ⟶
      coefficientSubalgebraDiagram A R :=
    (Functor.const (Finset R)).map (CommRingCat.ofHom κ) ≫
      coefficientSubalgebraBaseNatTrans A R
  let a := (coefficientSubalgebraCocone A R).ι
  let d := ((coefficientPushoutRingCocone A R S e).extend (CommRingCat.ofHom p)).ι
  apply coefficientVCoverModelFunctorOfRingDiagrams g (coefficientSubalgebraDiagram A R)
    (coefficientPushoutRingDiagram A R S) (coefficientPushoutBaseMap A R S) α a d
  · intro j
    change (CommRingCat.ofHom κ ≫ (coefficientSubalgebraBaseNatTrans A R).app j) ≫
      (coefficientSubalgebraCocone A R).ι.app j = CommRingCat.ofHom (algebraMap k R)
    rw [Category.assoc, coefficientSubalgebraCocone_base]
    exact CommRingCat.hom_ext hκR
  · intro j
    change (coefficientPushoutBaseMap A R S).app j ≫
      ((coefficientPushoutRingCocone A R S e).ι.app j ≫ CommRingCat.ofHom p) =
      (coefficientSubalgebraCocone A R).ι.app j ≫ CommRingCat.ofHom g.toRingHom
    rw [← Category.assoc, coefficientPushoutRingCocone_base, Category.assoc]
    exact congrArg (fun q : CommRingCat.of R ⟶ CommRingCat.of C ↦
      (coefficientSubalgebraCocone A R).ι.app j ≫ q) (CommRingCat.hom_ext hp)
  · intro j
    exact (coefficientPushout_base_source_finiteType A R S κ hκ j).1
  · intro j
    change (((coefficientPushoutRootMap A R S).app j).hom.comp κ).FiniteType
    exact (coefficientPushout_base_source_finiteType A R S κ hκ j).2
  · intro j
    exact coefficientPushoutBaseMap_vCover A R S hv j

/-- 実際の係数遷移は、この関手の被覆模型の間の射。 -/
abbrev coefficientPushoutVCoverModelMap {j l : Finset R} (w : j ⟶ l) :
    (coefficientPushoutVCoverModelFunctor k A R S g e κ hκ hκR p hp hv).obj j ⟶
      (coefficientPushoutVCoverModelFunctor k A R S g e κ hκ hκR p hp hv).obj l :=
  (coefficientPushoutVCoverModelFunctor k A R S g e κ hκ hκR p hp hv).map w

end SerrePositivity.AlgebraicGeometry
