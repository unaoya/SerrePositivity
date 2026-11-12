module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.PinchedHomPullbackIso
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.LaxPullbackLimit
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpaceFibration

/-!
概要：lax pullback の対象間右写像空間の引き戻し表示。
方針：右 pinched Hom と引き戻しの交換および両端評価の充填性を使う。
規約：指定された三角形と同型の値を保持する。
使われ方：引き戻し錐と指定 path の比較を簡約する。

対応節は Kerodon 5.5（Tag 01YV）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

variable {A B C : SSet.{u}}
/-- 概要：lax pullback の対象間右写像空間の引き戻し表示。
方針：右 pinched Hom と引き戻しの交換および両端評価の充填性を使う。
規約：元の頂点と右 pinched 単体の値を保持する。
使われ方：Tamme Remark 6 の対象間写像空間の具体式。 -/
def laxPullbackMappingIso (p : A ⟶ C) (q : B ⟶ C)
    (x y : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullback p q) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x y ≅ pullback
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.arrowEndpointPair C) ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackArrow p q).app (Opposite.op ⦋0⦌) x)
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackArrow p q).app (Opposite.op ⦋0⦌) y))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomPullbackBaseMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.arrowEndpointPair C) (p ⊗ₘ q) x y) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pinchedHomPullbackIso _ _ _ _
/-- 概要：lax pullback の対象間右写像空間の引き戻し表示。
方針：右 pinched Hom と引き戻しの交換および両端評価の充填性を使う。
規約：元の頂点と右 pinched 単体の値を保持する。
使われ方：Tamme Remark 6 の対象間写像空間の具体式。 -/
lemma laxPullbackMappingIso_arrow (p : A ⟶ C) (q : B ⟶ C)
    (x y : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullback p q) _⦋0⦌) :
    (laxPullbackMappingIso p q x y).hom ≫ pullback.fst _ _ =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackArrow p q) x y := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pinchedHomPullbackIso_fst _ _ _ _
/-- 概要：lax pullback の対象間右写像空間の引き戻し表示。
方針：右 pinched Hom と引き戻しの交換および両端評価の充填性を使う。
規約：元の頂点と右 pinched 単体の値を保持する。
使われ方：Tamme Remark 6 の対象間写像空間の具体式。 -/
lemma laxPullbackMappingIso_inputs (p : A ⟶ C) (q : B ⟶ C)
    (x y : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullback p q) _⦋0⦌) :
    (laxPullbackMappingIso p q x y).hom ≫ pullback.snd _ _ =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap (pullback.snd (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.arrowEndpointPair C) (p ⊗ₘ q)) x y :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pinchedHomPullbackIso_snd _ _ _ _
/-- 概要：lax pullback の対象間右写像空間の引き戻し表示。
方針：右 pinched Hom と引き戻しの交換および両端評価の充填性を使う。
規約：元の頂点と右 pinched 単体の値を保持する。
使われ方：Tamme Remark 6 の対象間写像空間の具体式。 -/
instance arrowEndpointPair_pinchedHom_fibration [Quasicategory C]
    (x y : ((ihom (Δ[1] : SSet.{u})).obj C) _⦋0⦌) :
    Fibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.arrowEndpointPair C) x y) := by
  have : Quasicategory (C ⊗ C) := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.quasicategory_tensor C C
  infer_instance

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
