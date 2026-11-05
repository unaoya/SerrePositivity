module
public import SerrePositivity.KST.Fibration.CofiberFamilyTranspose

/-! # 関手圏の cofiber 列から全四角形の族への復元

関手圏の実 cofiber 列を転置し、点ごとの普遍性で全 cofiber 図式へ持ち上げる。
元の実四角形を各パラメーターで厳密に回収する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Fibration

/-- 関手圏内の実 cofiber 列を、全パラメーターを保つ四角形の族へ復元する。 -/
def cofiberFamilyUntranspose {A : SSet.{u}} {B : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}}
    (t : ZeroTriangle ((ihom A).obj B.obj)) (ht : IsCofiberSequence t) :
    A ⟶ cofiberDiagrams B.obj :=
  fullSubcomplexLift IsCofiberDiagramVertex
    (internalHomFlipHomEquiv (Δ[1] ⊗ Δ[1]) A B.obj t.square) (by
      intro a
      rw [internalHomFlipHomEquiv_app_zero]
      change IsZeroVertex (squareVertex (t.square ≫ evaluateFunctorAt a) 0 1) ∧
        IsPushoutSquare (t.square ≫ evaluateFunctorAt a)
      exact ⟨isZeroVertex_evaluateFunctorAt t.zero_corner a,
        (functor_zeroTriangle_pushout_iff t).1 ht a⟩)

/-- 復元した全四角形の包含は、元の族の転置そのもの。 -/
lemma cofiberFamilyUntranspose_ι {A : SSet.{u}} {B : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}}
    (t : ZeroTriangle ((ihom A).obj B.obj)) (ht : IsCofiberSequence t) :
    cofiberFamilyUntranspose t ht ≫ (fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι =
      internalHomFlipHomEquiv (Δ[1] ⊗ Δ[1]) A B.obj t.square := rfl

/-- 元の実四角形は各点で厳密に回収される。 -/
lemma cofiberFamilyUntranspose_vertex {A : SSet.{u}} {B : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}}
    (t : ZeroTriangle ((ihom A).obj B.obj)) (ht : IsCofiberSequence t) (a : A _⦋0⦌) :
    squareDiagram ((cofiberFamilyUntranspose t ht).app (Opposite.op ⦋0⦌) a).val =
      t.square ≫ evaluateFunctorAt a := by
  change (functorVertexEquiv (Δ[1] ⊗ Δ[1]) B.obj).symm
    ((internalHomFlipHomEquiv (Δ[1] ⊗ Δ[1]) A B.obj t.square).app (Opposite.op ⦋0⦌) a) = _
  rw [internalHomFlipHomEquiv_app_zero]
  exact (functorVertexEquiv _ _).symm_apply_apply _

/-- 復元した全四角形の各角の族は、元の関手圏の頂点が表す関手である。 -/
lemma cofiberFamilyUntranspose_corner {A : SSet.{u}} {B : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}}
    (t : ZeroTriangle ((ihom A).obj B.obj)) (ht : IsCofiberSequence t)
    (a : (Δ[1] ⊗ Δ[1] : SSet.{u}) _⦋0⦌) :
    cofiberFamilyUntranspose t ht ≫ (cofiberStableEvaluation (sInputModel B) a).val =
      (functorVertexEquiv A B.obj).symm (t.square.app (Opposite.op ⦋0⦌) a) :=
  flipFamily_evaluate t.square a

end SerrePositivity.KST.Fibration
