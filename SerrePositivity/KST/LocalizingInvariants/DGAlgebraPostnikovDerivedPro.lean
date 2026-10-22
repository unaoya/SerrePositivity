module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovProZeroRoof
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPathInvertingFunctor
public import SerrePositivity.KST.LocalizingInvariants.ProTowerNatMap

/-!
概要：元の層群が pro 零なら、準同型を反転する圏で隣接 Postnikov 切断は pro 同型。
方針：元の遷移の実像拡大の準同型脚を逆にし、厳密な源三角形と乗法的経路を使う。
規約：元の二つの切断の塔・遷移を保持。使われ方：bounded な有限切断の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open ProExcision
variable (R : Type u) [CommRing R] (A : Tower (NonpositiveAlgebra R))

def postnikovTransitionLevelHom (a b : ℤ) (hab : b ≤ a) :
    LevelHom (A.map (postnikovFunctor R a)) (A.map (postnikovFunctor R b)) where
  app i := postnikovTransition R (A.obj i).obj a b hab
  naturality {m _i} hi :=
    postnikovTransition_naturality R (A.obj m).obj (A.transition hi).hom a b hab

variable {C : Type v} [Category.{w} C] (L : Mon (Complex R) ⥤ C)

lemma postnikovTransitionLevelHom_isProIso_succ_of_connective
    (hL : InvertsConnectiveQuasiIsos R L)
    (n : ℤ) (hn : 0 ≤ n)
    (hA : IsProZero ((A.map (nonpositiveInclusion R)).map (groups R (n + 1)))) :
    IsProIso ((postnikovTransitionLevelHom R A (n + 1) n (by omega)).map L) := by
  intro i
  obtain ⟨m, hi, hq, hs, ht⟩ := exists_postnikovProZeroRoof R n hn A hA i
  let f := (A.transition hi).hom
  let r := postnikovImageFactorisationBaseProjection R f n hn
  let t := postnikovImageFactorisationTarget R f n hn
  have hr : IsIso (L.map r) := hL
    (postnikovImageFactorisationObject_isConnective R f n hn)
    (postnikov_isConnective R (A.obj m).obj n) r hq
  refine ⟨m, hi, inv (L.map r) ≫ L.map t, ?_, ?_⟩
  · change L.map (postnikovTransition R (A.obj m).obj (n + 1) n (by omega)) ≫
      (inv (L.map r) ≫ L.map t) = L.map (postnikovMap R f (n + 1))
    rw [← hs, L.map_comp, Category.assoc, IsIso.hom_inv_id_assoc, ← L.map_comp]
    exact congrArg L.map ht
  · change (inv (L.map r) ≫ L.map t) ≫
      L.map (postnikovTransition R (A.obj i).obj (n + 1) n (by omega)) =
        L.map (postnikovMap R f n)
    have he := (postnikovImageFactorisationBaseWitness R f n hn).map_eq_of_connective R L hL
      (postnikov_isConnective R (A.obj i).obj n)
    change L.map (r ≫ postnikovMap R f n) =
      L.map (t ≫ postnikovTransition R (A.obj i).obj (n + 1) n (by omega)) at he
    rw [Category.assoc, ← L.map_comp, ← he, L.map_comp, IsIso.inv_hom_id_assoc]

lemma postnikovTransitionLevelHom_isProIso_succ (hL : InvertsQuasiIsos R L)
    (n : ℤ) (hn : 0 ≤ n)
    (hA : IsProZero ((A.map (nonpositiveInclusion R)).map (groups R (n + 1)))) :
    IsProIso ((postnikovTransitionLevelHom R A (n + 1) n (by omega)).map L) :=
  postnikovTransitionLevelHom_isProIso_succ_of_connective R A L (hL.connective R L) n hn hA

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
