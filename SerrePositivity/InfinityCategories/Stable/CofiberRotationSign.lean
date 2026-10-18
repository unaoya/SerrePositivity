module
public import SerrePositivity.InfinityCategories.Stable.CofiberRotationComparison
public import SerrePositivity.InfinityCategories.Stable.SuspensionAmbientHom
public import SerrePositivity.InfinityCategories.Stable.SuspensionSwapSign

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
namespace SerrePositivity.InfinityCategories

section
variable {X : SSet.{u}} [Quasicategory X] [IsStable X]
local instance : Preadditive X.HomotopyCategory := preadditive_ho (X := X)

/-- 概要：転置した懸垂から標準の懸垂への対象比較は元の比較の負号。
方針：標準比較の合成表示に二枝交換が負の恒等射であることを代入する。
規約：任意の指定懸垂を扱う。使われ方：回転比較の転置による符号の計算。 -/
lemma SuspensionSquare.transpose_objIso_inv {x : X _⦋0⦌} (s : SuspensionSquare x) :
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
lemma CofiberRotationRectangle.connecting_eq_neg_suspension {t : ZeroTriangle X}
    (r : CofiberRotationRectangle t) :
    r.suspensionSquare.suspensionFunctorObjIso.hom ≫
      cofiberConnecting r.rotatedZeroTriangle r.rotated_isCofiber ≫
        (suspensionFunctor X).map
          (eqToHom (congrArg SSet.HomotopyCategory.mk r.rotated_source)) =
      -(suspensionFunctor X).map (squareHoBottom t.square) := by
  let q := chosenCofiberRotationRectangle r.rotatedZeroTriangle r.rotated_isCofiber
  let f := squareHoBottom t.square ≫
    eqToHom (congrArg SSet.HomotopyCategory.mk r.rotated_source.symm)
  have hs : (squareDiagramHoEvaluation X 0 0).map (r.suspensionComparison q) =
      eqToHom (congrArg SSet.HomotopyCategory.mk r.suspensionSquare.source_eq) ≫ f ≫
        eqToHom (congrArg SSet.HomotopyCategory.mk
          q.suspensionSquare.transpose.source_eq.symm) := by
    rw [r.suspensionComparison_source q]
    simp only [f, Category.assoc, eqToHom_trans]
  have h := r.suspensionSquare.ambientHom_target q.suspensionSquare.transpose
    (r.suspensionComparison q) f hs
  erw [r.suspensionComparison_target q, q.suspensionSquare.transpose_objIso_inv,
    Preadditive.comp_neg, cofiberConnectingToSuspension_comp_objIso_inv] at h
  have hn := congrArg (fun g => -(r.suspensionSquare.suspensionFunctorObjIso.hom ≫ g) ≫
    (suspensionFunctor X).map (eqToHom (congrArg SSet.HomotopyCategory.mk r.rotated_source))) h
  simpa only [f, Functor.map_comp, Preadditive.comp_neg, Preadditive.neg_comp, neg_neg,
    Category.assoc, Iso.hom_inv_id_assoc, ← Functor.map_comp, eqToHom_trans,
    eqToHom_refl, Functor.map_id, Category.comp_id] using hn

end
end SerrePositivity.InfinityCategories
