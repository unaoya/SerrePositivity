module

public import SerrePositivity.KST.Spectra.FundamentalLoopHomotopyCategory
public import SerrePositivity.Spectra.PointedSimplicialSet.Basic

/-!
概要：元の基本群とホモトピー圏の loop の比較は、元の単体集合の射に自然。
方針：元の代表一単体の像を計算し、基点の等式による自己射の移送を明示する。
規約：基点を忘れない。使われ方：円 cotensor の符号反転を同じ Hom のホモトピー圏へ移す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.FundamentalLoop
variable {X Y : SSet.{u}} [KanComplex X] [KanComplex Y]
    {x : X _⦋0⦌} {y : Y _⦋0⦌}

/-- 元の基本群の誘導写像は、元のホモトピー圏の関手と基点の移送に厳密一致する。 -/
lemma toHom_map (f : X ⟶ Y) (hf : f.app (Opposite.op ⦋0⦌) x = y)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup X 0 x) :
    toHom (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map f hf a) =
      eqToHom (congrArg (SSet.HomotopyCategory.mk (X := Y)) hf).symm ≫
        (hoFunctor.map f).toFunctor.map (toHom a) ≫
        eqToHom (congrArg (SSet.HomotopyCategory.mk (X := Y)) hf) := by
  subst y
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  induction a using Quotient.inductionOn with | h s => ?_
  change SSet.HomotopyCategory.homMk (edge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex f rfl s)) =
    (hoFunctor.map f).toFunctor.map (SSet.HomotopyCategory.homMk (edge s))
  have he : edge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex f rfl s) = (edge s).map f :=
    SSet.Edge.ext (SSet.yonedaEquiv_comp s.map f)
  rw [he]
  rfl

/-- 元の点つき射によるホモトピー圏の作用を、同じ元の基点の自己射として表示する。 -/
def pointedHomMap {P Q : PointedSimplicialSet.{u}} (p : P ⟶ Q)
    (a : SSet.HomotopyCategory.mk P.basepoint ⟶ SSet.HomotopyCategory.mk P.basepoint) :
    SSet.HomotopyCategory.mk Q.basepoint ⟶ SSet.HomotopyCategory.mk Q.basepoint :=
  eqToHom (congrArg (SSet.HomotopyCategory.mk (X := Q.right))
    (PointedSimplicialSet.hom_basepointAt p (Opposite.op ⦋0⦌))).symm ≫
      (hoFunctor.map p.right).toFunctor.map a ≫
      eqToHom (congrArg (SSet.HomotopyCategory.mk (X := Q.right))
        (PointedSimplicialSet.hom_basepointAt p (Opposite.op ⦋0⦌)))

/-- 元の点つき射に関する基本群の自然性は、基点を移送した同じ自己射の作用。 -/
lemma toHom_pointed_map {P Q : PointedSimplicialSet.{u}} [KanComplex P.right]
    [KanComplex Q.right] (p : P ⟶ Q) (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup P.right 0 P.basepoint) :
    toHom (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map p.right
      (PointedSimplicialSet.hom_basepointAt p (Opposite.op ⦋0⦌)) a) =
      pointedHomMap p (toHom a) :=
  toHom_map p.right (PointedSimplicialSet.hom_basepointAt p (Opposite.op ⦋0⦌)) a

end SerrePositivity.KST.Spectra.FundamentalLoop
