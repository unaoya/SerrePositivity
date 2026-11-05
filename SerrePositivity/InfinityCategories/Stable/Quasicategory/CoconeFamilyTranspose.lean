module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

public import Mathlib.AlgebraicTopology.Quasicategory.Basic
public import Mathlib.AlgebraicTopology.SimplexCategory.Defs
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.CompStruct
public import Mathlib.AlgebraicTopology.SimplicialSet.CompStructTruncated
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Opposite
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Iso
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Types.Basic
public import Mathlib.CategoryTheory.NatTrans
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Combinatorics.Quiver.Basic
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Logic.Equiv.Defs
public import SerrePositivity.InfinityCategories.Core.Equivalence
public import SerrePositivity.InfinityCategories.Core.FunctorEvaluation
public import SerrePositivity.InfinityCategories.Core.InternalHomFlipAdjunction
public import SerrePositivity.InfinityCategories.Core.InternalHomSwap
public import SerrePositivity.InfinityCategories.Core.InvertibleEdgeLifting
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.FunctorPrismFiber

/-!
分割で生成：docstring を書き直すこと
概要：同じ前段上の全余錐族を、パラメータ関手圏の元の全余錐へ移す。
方針：内部 Hom の厳密転置で前段と終端脚を保ち、比較同型も同じ交換で移す。
規約：終端脚は元の実辺の一次単体のまま回収する。
使われ方：回収した実分母・次辺を指定前段経路付きの全単体比較へ貼る。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.InfinityCategories.Stable.Quasicategory
open SerrePositivity.KST.LocalizingInvariants

/-- 二変数の同じ内部 Hom の交換による全関手同型の転置。 -/
def spanFunctorIsoFlip {K L X : SSet.{u}} [Quasicategory X]
    {F G : K ⟶ (ihom L).obj X} (e : FunctorIso F G) :
    FunctorIso (internalHomFlipHomEquiv K L X F) (internalHomFlipHomEquiv K L X G) := by
  have h := VertexIso.map e (internalHomSwapIso K L X).hom
  simp only [internalHomSwapIso_functorVertex] at h
  change FunctorIso (curry ((β_ K L).hom ≫ uncurry F))
    (curry ((β_ K L).hom ≫ uncurry G))
  exact h

/-- 転置した同じ二つの全族の比較を、元の族の全関手同型へ戻す。 -/
def spanFunctorIsoUnflip {K L X : SSet.{u}} [Quasicategory X]
    {F G : K ⟶ (ihom L).obj X}
    (e : FunctorIso (internalHomFlipHomEquiv K L X F) (internalHomFlipHomEquiv K L X G)) :
    FunctorIso F G := by
  have h := spanFunctorIsoFlip e
  change FunctorIso
    ((internalHomFlipHomEquiv K L X).symm ((internalHomFlipHomEquiv K L X) F))
    ((internalHomFlipHomEquiv K L X).symm ((internalHomFlipHomEquiv K L X) G)) at h
  simpa only [Equiv.symm_apply_apply] using h

/-- 元の前段比較を商後合成し、同じパラメータの定値図式間の実比較辺にする。 -/
def spanConstantPrefixEdge {L X Y : SSet.{u}} (K : SSet.{u}) (q : X ⟶ Y)
    {D E : L ⟶ X}
    (t : Truncated.Edge (X := (truncation 2).obj ((ihom L).obj X))
      (functorVertex D) (functorVertex E)) :
    SSet.Edge (functorVertex (D ≫ q ≫ curry (snd K Y)))
      (functorVertex (E ≫ q ≫ curry (snd K Y))) :=
  (SSet.Edge.ofTruncated (X := (ihom L).obj X) t).map
    ((ihom L).map (q ≫ curry (snd K Y)))

lemma spanConstantPrefixEdge_component {L X Y : SSet.{u}} (K : SSet.{u}) (q : X ⟶ Y)
    {D E : L ⟶ X}
    (t : Truncated.Edge (X := (truncation 2).obj ((ihom L).obj X))
      (functorVertex D) (functorVertex E)) (k : L _⦋0⦌) :
    (functorEdgeAt (spanConstantPrefixEdge K q t) k).edge =
      (curry (snd K Y)).app (Opposite.op ⦋1⦌)
        (q.app (Opposite.op ⦋1⦌)
          ((evaluateFunctorAt (Y := X) k).app (Opposite.op ⦋1⦌) t.edge)) := by
  have hn : (ihom L).map (q ≫ curry (snd K Y)) ≫
      evaluateFunctorAt (Y := (ihom K).obj Y) k =
      evaluateFunctorAt (Y := X) k ≫ q ≫ curry (snd K Y) := rfl
  exact ConcreteCategory.congr_hom (C := Type u)
    (NatTrans.congr_app hn (Opposite.op ⦋1⦌)) t.edge

lemma spanConstantPrefixEdge_isInvertible {L X Y : SSet.{u}} [Quasicategory Y]
    (K : SSet.{u}) (q : X ⟶ Y) {D E : L ⟶ X}
    (t : Truncated.Edge (X := (truncation 2).obj ((ihom L).obj X))
      (functorVertex D) (functorVertex E))
    (ht : IsInvertibleEdge (X := (ihom L).obj Y)
      (t.map ((truncation 2).map ((ihom L).map q)))) :
    IsInvertibleEdge (X := (ihom L).obj ((ihom K).obj Y))
      (spanConstantPrefixEdge K q t).toTruncated := by
  have hi := ht.map ((ihom L).map (curry (snd K Y)))
  exact (isInvertibleEdge_congr
    (e := (t.map ((truncation 2).map ((ihom L).map q))).map
      ((truncation 2).map ((ihom L).map (curry (snd K Y)))))
    (f := (spanConstantPrefixEdge K q t).toTruncated) rfl).mp hi

end SerrePositivity.InfinityCategories.Stable.Quasicategory

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.spanConstantPrefixEdge (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.spanConstantPrefixEdge := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.spanConstantPrefixEdge

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.spanConstantPrefixEdge_component := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.spanConstantPrefixEdge_component

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.spanConstantPrefixEdge_isInvertible := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.spanConstantPrefixEdge_isInvertible

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.spanFunctorIsoFlip (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.spanFunctorIsoFlip := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.spanFunctorIsoFlip

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.spanFunctorIsoUnflip (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.spanFunctorIsoUnflip := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.spanFunctorIsoUnflip

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.spanFunctorIsoFlip._proof_1 := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.spanFunctorIsoFlip._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.spanFunctorIsoUnflip._proof_1 := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.spanFunctorIsoUnflip._proof_1
