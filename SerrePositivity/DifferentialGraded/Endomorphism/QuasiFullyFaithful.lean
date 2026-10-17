module
public import SerrePositivity.DifferentialGraded.Endomorphism.ThickHomComparison
public import SerrePositivity.DifferentialGraded.Category.HomotopyHomologyNaturality

/-! # 全Hom擬同型から主H⁰の完全忠実性への比較

全Hom写像の次数零Homologyを用い、H⁰の射計算と自然に照合する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex
variable {A : Type u} [CommRing A] {C : Type v} {B : Type w}
  [DGCategory A C] [DGCategory A B] (F : DGFunctor A C B)

lemma dgHomMap_closedCycle {x y : ClosedCategory A C} (f : x ⟶ y) :
    complexMapZeroCycle A (F.map x y) (closedHomEquiv A C x y f) =
      closedHomEquiv A B (F.onClosed.obj x) (F.onClosed.obj y) (F.onClosed.map f) := by
  apply Subtype.ext
  exact (cycleFromUnit_postcomp (ForgetEnrichment.homTo (Complex A) f) (F.map x y)).symm

lemma dgHomMap_homotopyHomologyEquiv (x y : ClosedCategory A C)
    (f : (toHomotopy A C).obj x ⟶ (toHomotopy A C).obj y) :
    homotopyHomologyEquiv A B (F.onClosed.obj x) (F.onClosed.obj y) (F.onHomotopy.map f) =
      homologyMap (F.map x y) 0 (homotopyHomologyEquiv A C x y f) := by
  obtain ⟨f, rfl⟩ := (toHomotopy A C).map_surjective f
  change homotopyHomologyEquiv A B (F.onClosed.obj x) (F.onClosed.obj y)
      ((toHomotopy A B).map (F.onClosed.map f)) = _
  rw [homotopyHomologyEquiv_map, homotopyHomologyEquiv_map,
    complexZeroHomologyClass_naturality, dgHomMap_closedCycle]
  rfl

lemma dgHomMap_onHomotopy_bijective (hF : HomQuasiIso F) (X Y : HomotopyCategory A C) :
    Function.Bijective (F.onHomotopy.map (X := X) (Y := Y)) := by
  obtain ⟨x⟩ := X
  obtain ⟨y⟩ := Y
  have := hF x y
  have hb := (ConcreteCategory.isIso_iff_bijective (homologyMap (F.map x y) 0)).mp inferInstance
  let eC := homotopyHomologyEquiv A C x y
  let eB := homotopyHomologyEquiv A B (F.onClosed.obj x) (F.onClosed.obj y)
  constructor
  · intro f g h
    apply eC.injective
    apply hb.1
    exact (dgHomMap_homotopyHomologyEquiv F x y f).symm.trans
      ((congrArg eB h).trans (dgHomMap_homotopyHomologyEquiv F x y g))
  · intro f
    obtain ⟨c, hc⟩ := hb.2 (eB f)
    refine ⟨eC.symm c, eB.injective ?_⟩
    exact (dgHomMap_homotopyHomologyEquiv F x y (eC.symm c)).trans
      ((congrArg (homologyMap (F.map x y) 0) (eC.apply_symm_apply c)).trans hc)

lemma dgHomMap_onHomotopy_full (hF : HomQuasiIso F) : F.onHomotopy.Full where
  map_surjective {X Y} := (dgHomMap_onHomotopy_bijective F hF X Y).2

lemma dgHomMap_onHomotopy_faithful (hF : HomQuasiIso F) : F.onHomotopy.Faithful where
  map_injective {X Y} := (dgHomMap_onHomotopy_bijective F hF X Y).1

variable (A) (D : Type v) [DGCategory A D] [Small.{u} D]

lemma perfectEndomorphismModuleHom_onHomotopy_full (S : Set D)
    (E : PerfectDGModuleOver A D S) (hgen : endomorphismThickGeneratesPerfect A D S E) :
    (perfectEndomorphismModuleHom A D S E).onHomotopy.Full :=
  dgHomMap_onHomotopy_full _ (perfectEndomorphismModuleHom_homQuasiIso A D S E hgen)

lemma perfectEndomorphismModuleHom_onHomotopy_faithful (S : Set D)
    (E : PerfectDGModuleOver A D S) (hgen : endomorphismThickGeneratesPerfect A D S E) :
    (perfectEndomorphismModuleHom A D S E).onHomotopy.Faithful :=
  dgHomMap_onHomotopy_faithful _ (perfectEndomorphismModuleHom_homQuasiIso A D S E hgen)

end SerrePositivity.DifferentialGraded
