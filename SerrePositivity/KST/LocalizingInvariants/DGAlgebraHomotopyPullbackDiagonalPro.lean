module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraHomotopyPullbackConnectingNaturality
public import SerrePositivity.KST.LocalizingInvariants.ProGroupDiagonalKernel
public import SerrePositivity.KST.LocalizingInvariants.ProRetractionInverse

/-!
概要：隣接二次数での元の pro 同型から、実自己 cospan の対角の pro 同型を導く。
方針：実 cocone 接続射で射影の eventual 核を消し、元の対角切断を回収する。
規約：一般 pro ∞ 同値は主張しない。使われ方：二切断逆の対角反映。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.HomotopyPullbackModel
open ProExcision
variable (R : Type u) [CommRing R]

/-- 実 cocone 完全列の cohomological な添字に合わせた既存群関手の表示。 -/
def cohomologyGroups (n : ℤ) : Mon (Complex R) ⥤ CommGrpCat.{u} :=
  Mon.forget (Complex R) ⋙ homologyFunctor (ModuleCat R) (.up ℤ) n ⋙
    forget₂ (ModuleCat R) AddCommGrpCat ⋙ AddCommGrpCat.toCommGrp

abbrev groupForget : ModuleCat.{u} R ⥤ CommGrpCat.{u} :=
  forget₂ (ModuleCat R) AddCommGrpCat ⋙ AddCommGrpCat.toCommGrp

variable {X Y : Tower (Mon (Complex R))} (F : LevelHom X Y)

def connectingHom (n : ℤ) :
    LevelHom (Y.map (cohomologyGroups R (n - 1)))
      ((modelTower R F F).map (cohomologyGroups R n)) where
  app i := (groupForget R).map (connecting R (F.app i) (F.app i) n)
  naturality h := by
    change (groupForget R).map (homologyMap (Y.transition h).hom (n - 1)) ≫
      (groupForget R).map (connecting R (F.app _) (F.app _) n) =
      (groupForget R).map (connecting R (F.app _) (F.app _) n) ≫
        (groupForget R).map (homologyMap (map R (F.app _) (F.app _) (F.app _) (F.app _)
          (X.transition h) (Y.transition h) (X.transition h)
          (F.naturality h) (F.naturality h)).hom n)
    have hn := congrArg ((groupForget R).map)
      (connecting_naturality R (F.app _) (F.app _) (F.app _) (F.app _)
        (X.transition h) (Y.transition h) (X.transition h)
        (F.naturality h) (F.naturality h) n)
    simpa only [CategoryTheory.Functor.map_comp] using hn

lemma leftProjection_cohomology_isProIso (n : ℤ)
    (hprev : IsProIso (F.map (cohomologyGroups R (n - 1))))
    (hcurr : IsProIso (F.map (cohomologyGroups R n))) :
    IsProIso ((leftProjection R F F).map (cohomologyGroups R n)) := by
  let p := F.map (cohomologyGroups R (n - 1))
  let d := connectingHom R F n
  let l := (leftProjection R F F).map (cohomologyGroups R n)
  let r := (rightProjection R F F).map (cohomologyGroups R n)
  let q := F.map (cohomologyGroups R n)
  have hp0 : ∀ i (x : (X.map (cohomologyGroups R (n - 1))).obj i),
      (d.app i).hom ((p.app i).hom x) = 1 := by
    intro i x
    have hz := congrArg (fun t => t x) (left_connecting_zero R (F.app i) (F.app i) n)
    exact hz
  have he : ∀ i (x : ((modelTower R F F).map (cohomologyGroups R n)).obj i),
      (l.app i).hom x = 1 ∧ (r.app i).hom x = 1 ↔
        ∃ z, (d.app i).hom z = x := by
    intro i x
    exact connecting_pair_exact R (F.app i) (F.app i) n x
  have hpair : ∀ i (x : ((modelTower R F F).map (cohomologyGroups R n)).obj i),
      (q.app i).hom ((l.app i).hom x) = (q.app i).hom ((r.app i).hom x) := by
    intro i x
    let w : Path.Witness R (left R (F.app i) (F.app i) ≫ F.app i)
        (right R (F.app i) (F.app i) ≫ F.app i) :=
      ⟨path R _ _, path_source R _ _, path_target R _ _⟩
    have hh := congrArg (fun t => t x) (w.chainHomotopy.homologyMap_eq n)
    change homologyMap (F.app i).hom n (homologyMap (left R (F.app i) (F.app i)).hom n x) =
      homologyMap (F.app i).hom n (homologyMap (right R (F.app i) (F.app i)).hom n x)
    change homologyMap ((left R (F.app i) (F.app i)).hom ≫ (F.app i).hom) n x =
      homologyMap ((right R (F.app i) (F.app i)).hom ≫ (F.app i).hom) n x at hh
    simpa only [homologyMap_comp, ModuleCat.comp_apply] using hh
  apply ProGroup.proIso_of_kernel_image
  · exact ProGroup.eventuallyKernelTrivial_of_pair_exact p d l r q hp0 he hpair
      (ProGroup.imageSurjective_of_proIso hprev) (ProGroup.kernelTrivial_of_proIso hcurr)
  · intro i
    refine ⟨i, le_rfl, fun x => ⟨((cohomologyGroups R n).map (diagonal R (F.app i))).hom x, ?_⟩⟩
    have hm : (cohomologyGroups R n).map (diagonal R (F.app i)) ≫
        (cohomologyGroups R n).map (left R (F.app i) (F.app i)) = 𝟙 _ :=
      ((cohomologyGroups R n).map_comp _ _).symm.trans
        ((congrArg ((cohomologyGroups R n).map) (diagonal_left R (F.app i))).trans
          ((cohomologyGroups R n).map_id _))
    have ht := congrArg (fun t => t.hom x) hm
    exact ht.trans ((congrArg (fun t => t.hom x)
      ((X.map (cohomologyGroups R n)).transition_self i)).symm)

lemma diagonal_cohomology_isProIso (n : ℤ)
    (hprev : IsProIso (F.map (cohomologyGroups R (n - 1))))
    (hcurr : IsProIso (F.map (cohomologyGroups R n))) :
    IsProIso ((diagonalHom R F).map (cohomologyGroups R n)) := by
  apply TowerDiagram.proIso_section_of_retraction _
    ((leftProjection R F F).map (cohomologyGroups R n))
  · intro i
    exact ((cohomologyGroups R n).map_comp _ _).symm.trans
      ((congrArg ((cohomologyGroups R n).map) (diagonal_left R (F.app i))).trans
        ((cohomologyGroups R n).map_id _))
  · exact leftProjection_cohomology_isProIso R F n hprev hcurr

lemma cohomologyGroups_neg (j : ℤ) : cohomologyGroups R (-j) = groups R j := rfl

lemma diagonal_groups_isProIso (j : ℤ)
    (hnext : IsProIso (F.map (groups R (j + 1))))
    (hcurr : IsProIso (F.map (groups R j))) :
    IsProIso ((diagonalHom R F).map (groups R j)) := by
  have hp : IsProIso (F.map (cohomologyGroups R (-j - 1))) := by
    rw [show -j - 1 = -(j + 1) by omega, cohomologyGroups_neg]
    exact hnext
  have hc : IsProIso (F.map (cohomologyGroups R (-j))) := by
    rw [cohomologyGroups_neg]
    exact hcurr
  simpa only [cohomologyGroups_neg] using diagonal_cohomology_isProIso R F (-j) hp hc

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.HomotopyPullbackModel
