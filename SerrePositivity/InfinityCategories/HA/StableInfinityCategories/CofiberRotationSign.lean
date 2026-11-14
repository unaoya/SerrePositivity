module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberRotationComparison
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionAmbientHom
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSwapSign

/-! # 回転した cofiber 列の第三接続射の負号

概要：回転後の接続射は、懸垂の対象比較を通すと元の第一射の懸垂の負号になる。
方針：二回の回転をつなぐ射を転置した懸垂の間の射とし、二枝交換の負号を適用する。
規約：懸垂関手と前加法構造は既存のもの。使われ方：三角形の回転公理の第三射。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

section
variable {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
local instance : Preadditive X.HomotopyCategory := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.preadditive_ho (X := X)

/-- 概要：転置した懸垂から標準の懸垂への対象比較は元の比較の負号。
方針：標準比較の合成表示に二枝交換が負の恒等射であることを代入する。
規約：任意の指定懸垂を扱う。使われ方：回転比較の転置による符号の計算。 -/
lemma SuspensionSquare.transpose_objIso_inv {x : X _⦋0⦌} (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare x) :
    s.transpose.suspensionFunctorObjIso.inv = -s.suspensionFunctorObjIso.inv := by
  have h := congrArg (fun f => f ≫ s.transpose.suspensionFunctorObjIso.inv)
    s.swapIso_eq_neg_id
  change (s.comparisonIso s.transpose).hom ≫ _ = _ at h
  rw [s.comparisonIso_eq_suspensionFunctorObjIso] at h
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id,
    Category.comp_id, Preadditive.neg_comp, Category.id_comp] at h
  have hn := congrArg Neg.neg h
  simpa only [neg_neg] using hn.symm

/-- 概要：回転後の接続射は、指定懸垂の比較後には元の第一射の懸垂の負号。
方針：二回の回転の比較を懸垂関手で計算し、転置した対象比較の負号を消す。
規約：回転後の始点と元の中間対象の等号輸送を明記。使われ方：TR2 の第三射。 -/
lemma CofiberRotationRectangle.connecting_eq_neg_suspension {t : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroTriangle X}
    (r : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberRotationRectangle t) :
    r.suspensionSquare.suspensionFunctorObjIso.hom ≫
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberConnecting r.rotatedZeroTriangle r.rotated_isCofiber ≫
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionFunctor X).map
          (eqToHom (congrArg SSet.HomotopyCategory.mk r.rotated_source)) =
      -(_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionFunctor X).map (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoBottom t.square) := by
  let q := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.chosenCofiberRotationRectangle r.rotatedZeroTriangle r.rotated_isCofiber
  let f := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoBottom t.square ≫
    eqToHom (congrArg SSet.HomotopyCategory.mk r.rotated_source.symm)
  have hs : (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation X 0 0).map (r.suspensionComparison q) =
      eqToHom (congrArg SSet.HomotopyCategory.mk r.suspensionSquare.source_eq) ≫ f ≫
        eqToHom (congrArg SSet.HomotopyCategory.mk
          q.suspensionSquare.transpose.source_eq.symm) := by
    rw [r.suspensionComparison_source q]
    simp only [f, Category.assoc, eqToHom_trans]
  have h := r.suspensionSquare.ambientHom_target q.suspensionSquare.transpose
    (r.suspensionComparison q) f hs
  erw [r.suspensionComparison_target q, q.suspensionSquare.transpose_objIso_inv,
    Preadditive.comp_neg, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberConnectingToSuspension_comp_objIso_inv] at h
  have hn := congrArg (fun g => -(r.suspensionSquare.suspensionFunctorObjIso.hom ≫ g) ≫
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionFunctor X).map (eqToHom (congrArg SSet.HomotopyCategory.mk r.rotated_source))) h
  simpa only [f, Functor.map_comp, Preadditive.comp_neg, Preadditive.neg_comp, neg_neg,
    Category.assoc, Iso.hom_inv_id_assoc, ← Functor.map_comp, eqToHom_trans,
    eqToHom_refl, Functor.map_id, Category.comp_id] using hn

end
end SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "1.1.2.13"] _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberRotationRectangle.connecting_eq_neg_suspension
