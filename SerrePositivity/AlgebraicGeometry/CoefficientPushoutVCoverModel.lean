module

public import SerrePositivity.AlgebraicGeometry.CoefficientPushoutFiniteType
public import SerrePositivity.AlgebraicGeometry.CoefficientVCoverRingModel

/-!
概要：各係数 pushout を、元の環写像への実際の有限型被覆模型として登録する。
方針：構成した環と射を変えず、有限型性・被覆性・係数可換式をそろえる。
規約：実際の tensor 模型から元の対象への射と可換性を保持する。
使われ方：B03・B04 の古い模型から共通する後段への射の標的。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory Limits
open scoped TensorProduct
universe u

/-- 各後段の実際の係数 pushout は、元の環写像への有限型被覆模型を与える。 -/
def coefficientPushoutVCoverModel
    (k A R S : Type u) [CommRing k] [CommRing A] [CommRing R] [CommRing S]
    [Algebra k R] [Algebra A R] [Algebra A S] [Algebra.FiniteType A S]
    {T C : Type u} [CommRing T] [CommRing C] [Algebra R T] [Algebra k C]
    (g : R →ₐ[k] C) (e : R ⊗[A] S ≃ₐ[R] T)
    (κ : k →+* A) (hκ : κ.FiniteType)
    (hκR : (algebraMap A R).comp κ = algebraMap k R)
    (p : T →+* C) (hp : p.comp (algebraMap R T) = g.toRingHom)
    (hv : IsAffineVCover (algebraMap A S)) (j : Finset R) :
    CoefficientVCoverModelCategory k g := by
  let κF := ((coefficientSubalgebraBaseNatTrans A R).app j).hom.comp κ
  let κG := ((coefficientPushoutRootMap A R S).app j).hom.comp κ
  let t := ((coefficientPushoutBaseMap A R S).app j).hom
  let a := ((coefficientSubalgebraCocone A R).ι.app j).hom
  let d := p.comp ((coefficientPushoutRingCocone A R S e).ι.app j).hom
  have hbase : a.comp ((coefficientSubalgebraBaseNatTrans A R).app j).hom =
      algebraMap A R := congrArg CommRingCat.Hom.hom (coefficientSubalgebraCocone_base A R j)
  have hroot : ((coefficientPushoutRingCocone A R S e).ι.app j).hom.comp
      ((coefficientPushoutRootMap A R S).app j).hom =
      (algebraMap R T).comp (algebraMap A R) :=
    congrArg CommRingCat.Hom.hom (coefficientPushoutRingCocone_root A R S e j)
  have hκa : a.comp κF = algebraMap k R := by
    change (a.comp ((coefficientSubalgebraBaseNatTrans A R).app j).hom).comp κ = _
    rw [hbase, hκR]
  have hκd : d.comp κG = algebraMap k C := by
    calc
      d.comp κG = p.comp
          ((((coefficientPushoutRingCocone A R S e).ι.app j).hom.comp
            ((coefficientPushoutRootMap A R S).app j).hom).comp κ) := rfl
      _ = p.comp ((algebraMap R T).comp ((algebraMap A R).comp κ)) := by rw [hroot]; rfl
      _ = g.toRingHom.comp (algebraMap k R) := by rw [hκR, ← RingHom.comp_assoc, hp]
      _ = algebraMap k C := g.comp_algebraMap
  have hs : ((coefficientPushoutRingCocone A R S e).ι.app j).hom.comp t =
      (algebraMap R T).comp a :=
    congrArg CommRingCat.Hom.hom (coefficientPushoutRingCocone_base A R S e j)
  have hsq : d.comp t = g.toRingHom.comp a := by
    change p.comp (((coefficientPushoutRingCocone A R S e).ι.app j).hom.comp t) = _
    rw [hs, ← RingHom.comp_assoc, hp]
  have hft := coefficientPushout_base_source_finiteType A R S κ hκ j
  exact coefficientVCoverModelObjOfRingHoms g κF κG hft.1 hft.2 t a d rfl hκa hκd hsq
    (coefficientPushoutBaseMap_vCover A R S hv j)

end SerrePositivity.AlgebraicGeometry
