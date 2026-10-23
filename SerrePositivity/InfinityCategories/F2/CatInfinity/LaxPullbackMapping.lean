module

public import SerrePositivity.InfinityCategories.F2.CatInfinity.PinchedHomPullbackIso
public import SerrePositivity.InfinityCategories.F2.CatInfinity.LaxPullbackLimit
public import SerrePositivity.InfinityCategories.Core.MappingSpaceFibration

/-!
概要：lax pullback の対象間右写像空間の引き戻し表示。
方針：右 pinched Hom と引き戻しの交換および両端評価の充填性を使う。
規約：指定された三角形と同型の値を保持する。
使われ方：引き戻し錐と指定 path の比較を簡約する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

variable {A B C : SSet.{u}}
/-- 概要：lax pullback の対象間右写像空間の引き戻し表示。
方針：右 pinched Hom と引き戻しの交換および両端評価の充填性を使う。
規約：元の頂点と右 pinched 単体の値を保持する。
使われ方：Tamme Remark 6 の対象間写像空間の具体式。 -/
def laxPullbackMappingIso (p : A ⟶ C) (q : B ⟶ C)
    (x y : (laxPullback p q) _⦋0⦌) :
    pinchedHom x y ≅ pullback
      (pinchedHomMap (arrowEndpointPair C) ((laxPullbackArrow p q).app (Opposite.op ⦋0⦌) x)
        ((laxPullbackArrow p q).app (Opposite.op ⦋0⦌) y))
      (pinchedHomPullbackBaseMap (arrowEndpointPair C) (p ⊗ₘ q) x y) :=
  pinchedHomPullbackIso _ _ _ _
/-- 概要：lax pullback の対象間右写像空間の引き戻し表示。
方針：右 pinched Hom と引き戻しの交換および両端評価の充填性を使う。
規約：元の頂点と右 pinched 単体の値を保持する。
使われ方：Tamme Remark 6 の対象間写像空間の具体式。 -/
lemma laxPullbackMappingIso_arrow (p : A ⟶ C) (q : B ⟶ C)
    (x y : (laxPullback p q) _⦋0⦌) :
    (laxPullbackMappingIso p q x y).hom ≫ pullback.fst _ _ =
      pinchedHomMap (laxPullbackArrow p q) x y := pinchedHomPullbackIso_fst _ _ _ _
/-- 概要：lax pullback の対象間右写像空間の引き戻し表示。
方針：右 pinched Hom と引き戻しの交換および両端評価の充填性を使う。
規約：元の頂点と右 pinched 単体の値を保持する。
使われ方：Tamme Remark 6 の対象間写像空間の具体式。 -/
lemma laxPullbackMappingIso_inputs (p : A ⟶ C) (q : B ⟶ C)
    (x y : (laxPullback p q) _⦋0⦌) :
    (laxPullbackMappingIso p q x y).hom ≫ pullback.snd _ _ =
      pinchedHomMap (pullback.snd (arrowEndpointPair C) (p ⊗ₘ q)) x y :=
  pinchedHomPullbackIso_snd _ _ _ _
/-- 概要：lax pullback の対象間右写像空間の引き戻し表示。
方針：右 pinched Hom と引き戻しの交換および両端評価の充填性を使う。
規約：元の頂点と右 pinched 単体の値を保持する。
使われ方：Tamme Remark 6 の対象間写像空間の具体式。 -/
instance arrowEndpointPair_pinchedHom_fibration [Quasicategory C]
    (x y : ((ihom (Δ[1] : SSet.{u})).obj C) _⦋0⦌) :
    Fibration (pinchedHomMap (arrowEndpointPair C) x y) := by
  have : Quasicategory (C ⊗ C) := quasicategory_tensor C C
  infer_instance

end SerrePositivity.InfinityCategories.F2
