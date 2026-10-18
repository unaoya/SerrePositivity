module
public import SerrePositivity.KST.ProExcision.ActionBarFibers
public import SerrePositivity.KST.ProExcision.SetActionMorphisms

/-!
# 係数の同変射と語を固定した包含

概要：同変射は作用 bar の語を基底の射で移し、始点を係数の射で移す。
方針：始点と語による座標の単射性を用いる。
規約：KST Lemma A.4。使われ方：線形に持ち上げた区間写像の両端の同定。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory
open SerrePositivity.KST.Comparison
variable {G G' : SimplicialObject MonCat.{u}} {X X' : SSet.{u}}
variable {A : SimplicialSetAction G X} {B : SimplicialSetAction G' X'}

/-- 概要：作用 bar の射影は同変射に自然。
方針：作用圏の誘導関手のラベルを評価する。
規約：KST Lemma A.4。使われ方：係数の写像による語の移送。 -/
lemma setActionBarMap_projection (f : SimplicialSetActionHom A B) :
    setActionBarMap f ≫ setActionBarProjection B =
      setActionBarProjection A ≫ monoidBarMap f.base := by rfl

/-- 概要：同変射は語を固定した係数包含と可換。
方針：始点と射影の語を比較する。
規約：KST Lemma A.4。使われ方：m 次区間写像の両端の同定。 -/
theorem setActionBarFiberSection_map (f : SimplicialSetActionHom A B)
    (n : SimplexCategoryᵒᵖ) (w : (monoidBar G).obj n) (x : X.obj n) :
    (setActionBarMap f).app n (setActionBarFiberSection A n w x) =
      setActionBarFiberSection B n ((monoidBarMap f.base).app n w) (f.hom.app n x) := by
  letI := A.actionStructure n
  letI := B.actionStructure n
  apply actionNerveWordCoordinates_injective (G := G'.obj n) (X := X'.obj n) n.unop.len
  apply Prod.ext
  · change f.hom.app n ((setActionBarFiberSection A n w x).obj 0).val =
      ((setActionBarFiberSection B n ((monoidBarMap f.base).app n w) (f.hom.app n x)).obj 0).val
    rw [setActionBarFiberSection_source, setActionBarFiberSection_source]
  · change (setActionBarProjection B).app n
        ((setActionBarMap f).app n (setActionBarFiberSection A n w x)) =
      (setActionBarProjection B).app n
        (setActionBarFiberSection B n ((monoidBarMap f.base).app n w) (f.hom.app n x))
    rw [setActionBarFiberSection_projection]
    have hh := congrArg (fun q ↦ q.app n (setActionBarFiberSection A n w x))
      (setActionBarMap_projection f)
    change (setActionBarProjection B).app n
        ((setActionBarMap f).app n (setActionBarFiberSection A n w x)) =
      (monoidBarMap f.base).app n
        ((setActionBarProjection A).app n (setActionBarFiberSection A n w x)) at hh
    rw [setActionBarFiberSection_projection] at hh
    exact hh

end SerrePositivity.KST.ProExcision
