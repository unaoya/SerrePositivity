module
public import SerrePositivity.InfinityCategories.Derived.CofiberConnectingDerivedImage
public import SerrePositivity.InfinityCategories.Stable.SuspensionSourceTransport

/-! # 標準 cofiber 接続射の始点表示の移送

概要：安定構造の接続射を標準始点の suspension に移すと、指定した suspension への接続射になる。
方針：suspension の始点変更後の対象比較を展開し、等号輸送を消す。
規約：実際の cofiber 接続射を保つ。使われ方：D7 の第三射の導来比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable {S : Type u} [CommRing S] {X Y : Semifree S}

/-- 標準頂点の suspension に移した実際の接続射。 -/
lemma semifreeCofiberConnecting_source_transport (f : X.val ⟶ Y.val) :
    cofiberConnecting (semifreeCofiberZeroTriangle f)
        (semifreeCofiberZeroTriangle_isCofiberSequence f) ≫
      (suspensionFunctor (derivedInfinityCategory S)).map
        (eqToHom (congrArg SSet.HomotopyCategory.mk (semifreeCofiberZeroTriangle_vertex00 f))) =
    cofiberConnectingToSuspension (semifreeCofiberZeroTriangle f)
        (semifreeCofiberZeroTriangle_isCofiberSequence f) (semifreeCofiberSuspensionSquare f) ≫
      (semifreeSuspensionSquare X).suspensionFunctorObjIso.inv := by
  have hs := (semifreeSuspensionSquare X).changeSource_objIso_inv
    (semifreeCofiberZeroTriangle_vertex00 f).symm
  rw [← cofiberConnectingToSuspension_comp_objIso_inv
    (semifreeCofiberZeroTriangle f) (semifreeCofiberZeroTriangle_isCofiberSequence f)
      (semifreeCofiberSuspensionSquare f)]
  erw [hs]
  simp only [Category.assoc, ← CategoryTheory.Functor.map_comp,
    eqToHom_trans, eqToHom_refl, CategoryTheory.Functor.map_id, Category.comp_id]

/-- 指定 suspension への接続射は終点の正規化と両立する。 -/
lemma semifreeCofiberConnecting_target_transport (f : X.val ⟶ Y.val) :
    cofiberConnectingToSuspension (semifreeCofiberZeroTriangle f)
        (semifreeCofiberZeroTriangle_isCofiberSequence f) (semifreeCofiberSuspensionSquare f) ≫
      eqToHom (congrArg SSet.HomotopyCategory.mk (semifreeSuspensionSquare_vertex X)) =
    eqToHom (congrArg SSet.HomotopyCategory.mk (semifreeCofiberZeroTriangle_vertex11 f)) ≫
      normalizedSemifreeCofiberConnectingToSuspension f := by
  simp only [normalizedSemifreeCofiberConnectingToSuspension,
    eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

end SerrePositivity.InfinityCategories
