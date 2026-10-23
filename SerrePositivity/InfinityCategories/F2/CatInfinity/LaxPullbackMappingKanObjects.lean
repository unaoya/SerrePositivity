module

public import SerrePositivity.InfinityCategories.F2.CatInfinity.LaxPullbackMappingProductSquare
public import SerrePositivity.InfinityCategories.F2.CatInfinity.KanTensorComplex

/-!
概要：原典の対象間写像空間の四隅を Kan 対象として束縛する。
方針：右写像空間の Kan 性と直積の Kan 性を使う。
規約：元の頂点と pinched 単体の値を保持する。
使われ方：Tamme Remark 6 の写像空間の引き戻し正方形。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

variable {A B C : SSet.{u}} (p : A ⟶ C) (q : B ⟶ C)
variable (x y : (laxPullback p q) _⦋0⦌)
/-- 概要：原典の対象間写像空間の四隅を Kan 対象として束縛する。
方針：右写像空間の Kan 性と直積の Kan 性を使う。
規約：元の四隅と対象間写像空間を保つ。
使われ方：Tamme Remark 6 のホモトピー引き戻しの公開界面。 -/
def laxPullbackMappingKanObject [Quasicategory A] [Quasicategory B] [Quasicategory C] :
    KanObject.{u} :=
  ⟨pinchedHom x y, inferInstance⟩
/-- 概要：原典の対象間写像空間の四隅を Kan 対象として束縛する。
方針：右写像空間の Kan 性と直積の Kan 性を使う。
規約：元の四隅と対象間写像空間を保つ。
使われ方：Tamme Remark 6 のホモトピー引き戻しの公開界面。 -/
def laxPullbackArrowMappingKanObject [Quasicategory C] : KanObject.{u} :=
  ⟨pinchedHom ((laxPullbackArrow p q).app (Opposite.op ⦋0⦌) x)
    ((laxPullbackArrow p q).app (Opposite.op ⦋0⦌) y), inferInstance⟩
/-- 概要：原典の対象間写像空間の四隅を Kan 対象として束縛する。
方針：右写像空間の Kan 性と直積の Kan 性を使う。
規約：元の四隅と対象間写像空間を保つ。
使われ方：Tamme Remark 6 のホモトピー引き戻しの公開界面。 -/
def laxPullbackInputsMappingKanObject [Quasicategory A] [Quasicategory B] : KanObject.{u} :=
  ⟨pinchedHom ((laxPullbackFst p q).app (Opposite.op ⦋0⦌) x)
      ((laxPullbackFst p q).app (Opposite.op ⦋0⦌) y) ⊗
    pinchedHom ((laxPullbackSnd p q).app (Opposite.op ⦋0⦌) x)
      ((laxPullbackSnd p q).app (Opposite.op ⦋0⦌) y), kanComplex_tensor _ _⟩
/-- 概要：原典の対象間写像空間の四隅を Kan 対象として束縛する。
方針：右写像空間の Kan 性と直積の Kan 性を使う。
規約：元の四隅と対象間写像空間を保つ。
使われ方：Tamme Remark 6 のホモトピー引き戻しの公開界面。 -/
def laxPullbackBaseMappingKanObject [Quasicategory C] : KanObject.{u} :=
  ⟨pinchedHom (p.app (Opposite.op ⦋0⦌) ((laxPullbackFst p q).app (Opposite.op ⦋0⦌) x))
      (p.app (Opposite.op ⦋0⦌) ((laxPullbackFst p q).app (Opposite.op ⦋0⦌) y)) ⊗
    pinchedHom (q.app (Opposite.op ⦋0⦌) ((laxPullbackSnd p q).app (Opposite.op ⦋0⦌) x))
      (q.app (Opposite.op ⦋0⦌) ((laxPullbackSnd p q).app (Opposite.op ⦋0⦌) y)),
    kanComplex_tensor _ _⟩

end SerrePositivity.InfinityCategories.F2
