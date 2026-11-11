module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.ArrowEndpointPair
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.InnerProductProjection

/-!
概要：小さい quasicategory の直積と矢印圏の束縛。
方針：直積の inner 射影と関手圏の quasicategory 性を使う。
規約：指定された三角形と同型の値を保持する。
使われ方：引き戻し錐と指定 path の比較を簡約する。

対応節は Kerodon 5.5（Tag 01YV）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

/-- 概要：小さい quasicategory の直積と矢印圏の束縛。
方針：直積の inner 射影と関手圏の quasicategory 性を使う。
規約：矢印の向きは p(a) から q(b)。
使われ方：Tamme §1 の lax pullback と安定圏への接続。 -/
lemma quasicategory_tensor (A B : SSet.{u}) [Quasicategory A] [Quasicategory B] :
    Quasicategory (A ⊗ B) := quasicategory_of_innerFibration (fst A B)
/-- 概要：小さい quasicategory の直積と矢印圏の束縛。
方針：直積の inner 射影と関手圏の quasicategory 性を使う。
規約：矢印の向きは p(a) から q(b)。
使われ方：Tamme §1 の lax pullback と安定圏への接続。 -/
def qCatTensorObject (A B : SSet.{u}) [Quasicategory A] [Quasicategory B] : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCat.{u} :=
  (⟨A ⊗ B, quasicategory_tensor A B⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QuasicategoryObject.{u})
/-- 概要：小さい quasicategory の直積と矢印圏の束縛。
方針：直積の inner 射影と関手圏の quasicategory 性を使う。
規約：矢印の向きは p(a) から q(b)。
使われ方：Tamme §1 の lax pullback と安定圏への接続。 -/
def qCatArrowObject (C : SSet.{u}) [Quasicategory C] : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCat.{u} :=
  (⟨(ihom (Δ[1] : SSet.{u})).obj C, inferInstance⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QuasicategoryObject.{u})

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
