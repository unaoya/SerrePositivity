module

public import Mathlib.CategoryTheory.Monoidal.Closed.Functor
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
public import Mathlib.AlgebraicTopology.SimplicialSet.Op
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes

/-!
概要：単体順序の反転と内部 Hom の厳密な比較を両変数の自然性とともに構成する。
方針：反転の圏同値は積と指数を保つので、標準の指数比較を同型として使う。
規約：単体の反転と通常の反対圏を区別する。Kan 性・モデル構造は不要。
使われ方：HTT 4.2.4.1、重み付き end の反転と coherent な余錐の係数の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.OppositeInternalHom
noncomputable section

local instance : SSet.opFunctor.{u}.IsEquivalence := SSet.opEquivalence.isEquivalence_functor

local instance : MonoidalClosedFunctor SSet.opFunctor.{u} :=
  cartesianClosedFunctorOfLeftAdjointPreservesBinaryProducts _ SSet.opEquivalence.toAdjunction

/-- 内部 Hom の反転と、両対象を反転した内部 Hom の終域に自然な同型。 -/
def oppositeInternalHomNatIso (A : SSet.{u}) :
    ihom A ⋙ SSet.opFunctor ≅ SSet.opFunctor ⋙ ihom A.op :=
  asIso (expComparison SSet.opFunctor A).natTrans

/-- 反転前後の内部 Hom の実際の同型。 -/
def oppositeInternalHomIso (A B : SSet.{u}) :
    ((ihom A).obj B).op ≅ (ihom A.op).obj B.op :=
  (oppositeInternalHomNatIso A).app B

/-- 内部 Hom の反転比較は終域の全ての射に自然。 -/
lemma oppositeInternalHom_post (A : SSet.{u}) {B B' : SSet.{u}} (g : B ⟶ B') :
    SSet.opFunctor.map ((ihom A).map g) ≫ (oppositeInternalHomIso A B').hom =
      (oppositeInternalHomIso A B).hom ≫ (ihom A.op).map (SSet.opFunctor.map g) :=
  (oppositeInternalHomNatIso A).hom.naturality g

/-- 内部 Hom の反転比較は始域の前合成にも自然。 -/
lemma oppositeInternalHom_pre {A A' : SSet.{u}} (f : A' ⟶ A) (B : SSet.{u}) :
    SSet.opFunctor.map ((pre f).app B) ≫ (oppositeInternalHomIso A' B).hom =
      (oppositeInternalHomIso A B).hom ≫ (pre (SSet.opFunctor.map f)).app B.op := by
  have h := expComparison_whiskerLeft SSet.opFunctor f
  exact (congrArg (fun s ↦ s.natTrans.app B) h).symm

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.OppositeInternalHom
