module
public import SerrePositivity.KST.SConstruction.FunctorInitialVertices
public import SerrePositivity.InfinityCategories.Stable.InitialTransport

/-! # 関手圏の零対象の点ごとの評価
概要：零対象を持つ quasicategory の関手圏では評価が零対象を保つ。
方針：定値零関手との同型を各点で評価する。
規約：パラメーターは任意。使われ方：点ごとの安定性の反映。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：定値零関手は関手圏の零対象。
方針：点ごとの零対象判定を使う。
規約：quasicategory 性は不要。使われ方：評価による零対象の保存。 -/
lemma functor_const_isZeroVertex {A C : SSet.{u}} (z : C _⦋0⦌) (hz : IsZeroVertex z) :
    IsZeroVertex (functorVertex (SSet.const z : A ⟶ C)) := by
  apply isZeroVertex_functorVertex_of_pointwise
  intro a
  change IsZeroVertex (PinchedHom.constant z 0)
  rw [pinchedConstant_zero]
  exact hz

/-- 概要：零対象の存在は任意の関手圏へ移る。
方針：選んだ零対象への定値関手を使う。
規約：標的は零対象を持てばよい。使われ方：関手圏の安定性。 -/
instance functor_hasZeroVertex (A C : SSet.{u}) [HasZeroVertex C] :
    HasZeroVertex ((ihom A).obj C) :=
  ⟨⟨functorVertex (SSet.const (chosenZeroVertex C).vertex : A ⟶ C),
    functor_const_isZeroVertex _ (chosenZeroVertex C).isZero⟩⟩

/-- 概要：関手圏の零頂点の各点での評価は零頂点。
方針：定値零関手との同型を評価し、零対象性を移す。
規約：標的は零対象を持つ quasicategory。使われ方：零角の点ごとの判定。 -/
lemma isZeroVertex_evaluateFunctorAt {A C : SSet.{u}} [Quasicategory C] [HasZeroVertex C]
    {v : ((ihom A).obj C) _⦋0⦌} (hv : IsZeroVertex v) (a : A _⦋0⦌) :
    IsZeroVertex ((evaluateFunctorAt a).app (Opposite.op ⦋0⦌) v) := by
  let z := chosenZeroVertex C
  have hz := functor_const_isZeroVertex (A := A) z.vertex z.isZero
  let e := zeroVertexIso (⟨_, hz.1, hz.2⟩ : ZeroVertex ((ihom A).obj C)) ⟨v, hv.1, hv.2⟩
  have he := VertexIso.map e (evaluateFunctorAt a)
  have ht : IsZeroVertex ((evaluateFunctorAt a).app (Opposite.op ⦋0⦌)
      (functorVertex (SSet.const z.vertex : A ⟶ C))) := by
    rw [evaluateFunctorAt_functorVertex]
    change IsZeroVertex (PinchedHom.constant z.vertex 0)
    rw [pinchedConstant_zero]
    exact z.isZero
  exact ht.of_vertexIso he

end SerrePositivity.KST.SConstruction
