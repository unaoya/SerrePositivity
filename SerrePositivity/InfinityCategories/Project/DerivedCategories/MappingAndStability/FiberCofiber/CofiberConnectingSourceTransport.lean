module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FiberCofiber.CofiberConnectingDerivedImage
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSourceTransport

/-! # 標準 cofiber 接続射の始点表示の移送

概要：安定構造の接続射を標準始点の suspension に移すと、指定した suspension への接続射になる。
方針：suspension の始点変更後の対象比較を展開し、等号輸送を消す。
規約：実際の cofiber 接続射を保つ。使われ方：D7 の第三射の導来比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable {S : Type u} [CommRing S] {X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S}

/-- 標準頂点の suspension に移した実際の接続射。 -/
lemma semifreeCofiberConnecting_source_transport (f : X.val ⟶ Y.val) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberConnecting (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeCofiberZeroTriangle f)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeCofiberZeroTriangle_isCofiberSequence f) ≫
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionFunctor (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory S)).map
        (eqToHom (congrArg SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeCofiberZeroTriangle_vertex00 f))) =
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberConnectingToSuspension (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeCofiberZeroTriangle f)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeCofiberZeroTriangle_isCofiberSequence f) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeCofiberSuspensionSquare f) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionSquare X).suspensionFunctorObjIso.inv := by
  have hs := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionSquare X).changeSource_objIso_inv
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeCofiberZeroTriangle_vertex00 f).symm
  rw [← _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberConnectingToSuspension_comp_objIso_inv
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeCofiberZeroTriangle f) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeCofiberZeroTriangle_isCofiberSequence f)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeCofiberSuspensionSquare f)]
  erw [hs]
  simp only [Category.assoc, ← CategoryTheory.Functor.map_comp,
    eqToHom_trans, eqToHom_refl, CategoryTheory.Functor.map_id, Category.comp_id]

/-- 指定 suspension への接続射は終点の正規化と両立する。 -/
lemma semifreeCofiberConnecting_target_transport (f : X.val ⟶ Y.val) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberConnectingToSuspension (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeCofiberZeroTriangle f)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeCofiberZeroTriangle_isCofiberSequence f) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeCofiberSuspensionSquare f) ≫
      eqToHom (congrArg SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionSquare_vertex X)) =
    eqToHom (congrArg SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeCofiberZeroTriangle_vertex11 f)) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.normalizedSemifreeCofiberConnectingToSuspension f := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.normalizedSemifreeCofiberConnectingToSuspension,
    eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

end SerrePositivity.InfinityCategories.Project.DerivedCategories
