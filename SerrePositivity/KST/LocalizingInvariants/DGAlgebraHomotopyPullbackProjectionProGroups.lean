module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraHomotopyPullbackDiagonalPro
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraHomotopyPullbackPairHomology
public import SerrePositivity.KST.LocalizingInvariants.ProGroupPullbackProjection

/-!
概要：隣接二次数の元の pro 同型から、任意の cospan 模型の右射影の pro 同型を導く。
方針：実 cocone 接続射で eventual 核を消し、両射影を保つ対の持ち上げで像を覆う。
規約：cospan の他方の脚に準同型性を仮定しない。
使われ方：有限切断を底とする連結なレベル表示の弱同値比較。
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
variable (R : Type u) [CommRing R] {X Y Z : Tower (Mon (Complex R))}
  (F : LevelHom X Y) (G : LevelHom Z Y)

def cospanConnectingHom (n : ℤ) :
    LevelHom (Y.map (cohomologyGroups R (n - 1)))
      ((modelTower R F G).map (cohomologyGroups R n)) where
  app i := (groupForget R).map (connecting R (F.app i) (G.app i) n)
  naturality h := by
    change (groupForget R).map (homologyMap (Y.transition h).hom (n - 1)) ≫
      (groupForget R).map (connecting R (F.app _) (G.app _) n) =
      (groupForget R).map (connecting R (F.app _) (G.app _) n) ≫
        (groupForget R).map (homologyMap (map R (F.app _) (G.app _) (F.app _) (G.app _)
          (X.transition h) (Y.transition h) (Z.transition h)
          (F.naturality h) (G.naturality h)).hom n)
    have hn := congrArg ((groupForget R).map)
      (connecting_naturality R (F.app _) (G.app _) (F.app _) (G.app _)
        (X.transition h) (Y.transition h) (Z.transition h)
        (F.naturality h) (G.naturality h) n)
    simpa only [CategoryTheory.Functor.map_comp] using hn

lemma rightProjection_cohomology_isProIso (n : ℤ)
    (hprev : IsProIso (F.map (cohomologyGroups R (n - 1))))
    (hcurr : IsProIso (F.map (cohomologyGroups R n))) :
    IsProIso ((rightProjection R F G).map (cohomologyGroups R n)) := by
  let p := F.map (cohomologyGroups R (n - 1))
  let d := cospanConnectingHom R F G n
  let l := (rightProjection R F G).map (cohomologyGroups R n)
  let r := (leftProjection R F G).map (cohomologyGroups R n)
  let q := F.map (cohomologyGroups R n)
  let t := G.map (cohomologyGroups R n)
  have hp0 : ∀ i (x : (X.map (cohomologyGroups R (n - 1))).obj i),
      (d.app i).hom ((p.app i).hom x) = 1 := by
    intro i x
    exact congrArg (fun s => s x) (left_connecting_zero R (F.app i) (G.app i) n)
  have he : ∀ i (x : ((modelTower R F G).map (cohomologyGroups R n)).obj i),
      (l.app i).hom x = 1 ∧ (r.app i).hom x = 1 ↔
        ∃ z, (d.app i).hom z = x := by
    intro i x
    exact and_comm.trans (connecting_pair_exact R (F.app i) (G.app i) n x)
  have hpair : ∀ i (x : ((modelTower R F G).map (cohomologyGroups R n)).obj i),
      (t.app i).hom ((l.app i).hom x) = (q.app i).hom ((r.app i).hom x) := by
    intro i x
    let w : Path.Witness R (left R (F.app i) (G.app i) ≫ F.app i)
        (right R (F.app i) (G.app i) ≫ G.app i) :=
      ⟨path R _ _, path_source R _ _, path_target R _ _⟩
    have hh := congrArg (fun s => s x) (w.chainHomotopy.homologyMap_eq n)
    change homologyMap (G.app i).hom n (homologyMap (right R (F.app i) (G.app i)).hom n x) =
      homologyMap (F.app i).hom n (homologyMap (left R (F.app i) (G.app i)).hom n x)
    change homologyMap ((left R (F.app i) (G.app i)).hom ≫ (F.app i).hom) n x =
      homologyMap ((right R (F.app i) (G.app i)).hom ≫ (G.app i).hom) n x at hh
    simpa only [homologyMap_comp, ModuleCat.comp_apply] using hh.symm
  have himage : ∀ i (x : (X.map (cohomologyGroups R n)).obj i)
      (y : (Z.map (cohomologyGroups R n)).obj i),
      (q.app i).hom x = (t.app i).hom y →
        ∃ z : ((modelTower R F G).map (cohomologyGroups R n)).obj i,
          (r.app i).hom z = x ∧ (l.app i).hom z = y := by
    intro i x y hxy
    exact homology_pair_lift R (F.app i) (G.app i) n x y hxy
  apply ProGroup.proIso_of_kernel_image
  · exact ProGroup.eventuallyKernelTrivial_of_pullback_pair_exact p d l r q t hp0 he hpair
      (ProGroup.imageSurjective_of_proIso hprev) (ProGroup.kernelTrivial_of_proIso hcurr)
  · exact ProGroup.eventuallyImageSurjective_of_pullback_pair_exact l r q t himage
      (ProGroup.imageSurjective_of_proIso hcurr)

lemma rightProjection_groups_isProIso (j : ℤ)
    (hnext : IsProIso (F.map (groups R (j + 1))))
    (hcurr : IsProIso (F.map (groups R j))) :
    IsProIso ((rightProjection R F G).map (groups R j)) := by
  have hp : IsProIso (F.map (cohomologyGroups R (-j - 1))) := by
    rw [show -j - 1 = -(j + 1) by omega, cohomologyGroups_neg]
    exact hnext
  have hc : IsProIso (F.map (cohomologyGroups R (-j))) := by
    rw [cohomologyGroups_neg]
    exact hcurr
  simpa only [cohomologyGroups_neg] using rightProjection_cohomology_isProIso R F G (-j) hp hc

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.HomotopyPullbackModel
