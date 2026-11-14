module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroTargetSquareComparison
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberConnectingNaturality

/-! # 接続射の後の Σf との零合成

概要：cofiber 列の接続射の後に最初の射の suspension を合成すると零になる。
方針：最後の成分が零になる比較を始点成分による一意性で標準比較の合成と照合する。
規約：構成済みの suspensionFunctor を使い、三角圏の構造を仮定しない。
使われ方：S4 の cofiber 三角形の三つ目の隣接零合成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：cofiber 列の接続射と最初の射の suspension の合成は零である。
方針：始点成分が f、最後の成分が零となる比較と標準比較の合成を一意性で同定し、Σ に移す。
規約：安定な quasicategory。使われ方：cofiber 三角形の隣接零合成。 -/
lemma cofiberConnecting_comp_suspension_map_eq_zero {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    (t : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroTriangle X) (ht : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsCofiberSequence t) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberConnecting t ht ≫ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionFunctor X).map t.hoShortComplex.f = 0 := by
  let s := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.chosenSuspensionSquare (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex t.square 0 0)
  let r := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.chosenSuspensionSquare (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex t.square 1 0)
  let f := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoBottom t.square
  let b := (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionDiagramHoInclusion X).map (s.liftSourceHom r f)
  let q := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberSuspensionComparisonHom t.square ht s ≫ b
  obtain ⟨z, hzsource, hztarget⟩ := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.exists_squareToSuspension_zero_target t.square r
  have hsource : (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation X 0 0).map q = f ≫
      eqToHom (congrArg SSet.HomotopyCategory.mk r.source_eq.symm) := by
    dsimp only [q, b]
    rw [Functor.map_comp, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberSuspensionComparisonHom_source,
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionDiagramHoInclusion_evaluation, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare.liftSourceHom_source]
    simp only [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  have hqz : q = z :=
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberSuspensionComparison_hom_ext t.square ht r (hsource.trans hzsource.symm)
  have htarget := congrArg (fun a ↦ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation X 1 1).map a) hqz
  rw [hztarget] at htarget
  have h := congrArg (fun a ↦ a ≫ r.suspensionFunctorObjIso.inv) htarget
  rw [zero_comp (C := hoFunctor.obj X)] at h
  dsimp only [q, b] at h
  rw [Functor.map_comp, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberSuspensionComparisonHom_target, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionDiagramHoInclusion_evaluation,
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare.suspensionFunctorObjIso_inv_naturality,
    ← Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberConnectingToSuspension_comp_objIso_inv] at h
  exact h

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
