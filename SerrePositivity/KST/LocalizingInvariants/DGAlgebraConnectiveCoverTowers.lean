module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraConnectiveCoverFunctor
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraInvariantConnectivity
public import SerrePositivity.KST.ProExcision.Pro

/-!
概要：connective dg 代数の塔に、非正次数 cover の実自然比較と整数群の pro 同型を供給する。
方針：同じ代数の counit をレベル射にし、各段の実準同型とその群同型を用いる。
規約：有限 Postnikov 切断や値の塔の関手性は別工程。
使われ方：Tor pro 切除の基礎模型を非正次数に揃える準備。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories SerrePositivity.DifferentialGraded
open SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra

variable (R : Type u) [CommRing R]

def coverTowerCounit (X : ProExcision.Tower (Mon (Complex R))) :
    ProExcision.LevelHom (X.map (connectiveCoverFunctor R)) X where
  app n := connectiveCoverInclusion R (X.obj n)
  naturality h := (connectiveCoverCounit R).naturality (X.transition h)

lemma coverTowerCounit_groups_proIso (X : ProExcision.Tower (Mon (Complex R)))
    (hX : ∀ m, IsConnective R (X.obj m)) (j : ℤ) :
    ProExcision.IsProIso ((coverTowerCounit R X).map (groups R j)) := by
  intro m
  let f := ((coverTowerCounit R X).map (groups R j)).app m
  haveI : IsIso f := groups_map_isIso_of_quasiIso R
    (connectiveCoverInclusion R (X.obj m))
    (connectiveCoverInclusion_quasiIso R (X.obj m) (hX m)) j
  refine ⟨m, le_refl m, inv f, ?_, ?_⟩
  · exact (IsIso.hom_inv_id f).trans
      (((X.map (connectiveCoverFunctor R)).map (groups R j)).transition_self m).symm
  · exact (IsIso.inv_hom_id f).trans ((X.map (groups R j)).transition_self m).symm

lemma IsKConnective.cover_value_isInvertible
    {Φ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u + 1} ⟶ Sp.{u + 1}} {k : ℤ} (h : IsKConnective R Φ k)
    (B : Mon (Complex R)) (hB : IsConnective R B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge
      ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (perfectMap R (connectiveCoverInclusion R B))).map Φ).toTruncated :=
  h.quasiIso_value_isInvertible R Φ (connectiveCover_isConnective R B) hB
    (connectiveCoverInclusion R B) (connectiveCoverInclusion_quasiIso R B hB)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
