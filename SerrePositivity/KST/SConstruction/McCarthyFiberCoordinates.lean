module
public import SerrePositivity.KST.SConstruction.McCarthyFiberSection
public import SerrePositivity.KST.SConstruction.ObjectSVertices
public import SerrePositivity.KST.SConstruction.McCarthySpanEvaluations

/-! # McCarthy の左 fiber の単体座標
概要：左 fiber の単体を実際の gapped cofiber 図式と Ar の添字で読む。
方針：pullback の二射影と object S の実図式への対応を使う。
規約：元の strict pullback を保持する。使われ方：ρ の単体的な族の構成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：左 fiber の単体の実際の gapped cofiber 図式。
方針：元の図式への射影を object S の図式に戻す。
規約：単体の次元を保持する。使われ方：ρ の入力 E。 -/
def mcCarthyFiberDiagram (X : StableModel.{u}) {m n : ℕ}
    (a : (objectSConstruction X.carrier) _⦋m⦌) (e : (cofiberSubobjectLeftFiber X a) _⦋n⦌) :
    arNerve n ⟶ cofiberDiagrams X.carrier :=
  gappedDiagram ((simplexLeftFiberProjection
    (objectSConstructionFunctor.map (cofiberStableSubobject X)) a).app (Opposite.op ⦋n⦌) e)

/-- 概要：左 fiber の単体の標準単体パラメーター。
方針：pullback の第二射影。
規約：元の単体をそのまま保持。使われ方：ρ の添字 α。 -/
def mcCarthyFiberParameter (X : StableModel.{u}) {m n : ℕ}
    (a : (objectSConstruction X.carrier) _⦋m⦌) (e : (cofiberSubobjectLeftFiber X a) _⦋n⦌) :
    (Δ[m] : SSet.{u}) _⦋n⦌ :=
  (simplexLeftFiberParameter (objectSConstructionFunctor.map (cofiberStableSubobject X)) a).app
    (Opposite.op ⦋n⦌) e

/-- 概要：左 fiber の元の subobject はパラメーターで制限した固定単体。
方針：pullback の可換性を gapped 図式への単射な対応で読む。
規約：図式全体の厳密な等号。使われ方：ρ の入力条件。 -/
lemma mcCarthyFiberDiagram_source (X : StableModel.{u}) {m n : ℕ}
    (a : (objectSConstruction X.carrier) _⦋m⦌) (e : (cofiberSubobjectLeftFiber X a) _⦋n⦌) :
    mcCarthyFiberDiagram X a e ≫ cofiberProjection X.carrier ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      arNerveMap (stdSimplex.objEquiv (mcCarthyFiberParameter X a e)).toOrderHom ≫
        gappedDiagram a := by
  have he := ConcreteCategory.congr_hom (NatTrans.congr_app
    (simplexLeftFiber_condition (objectSConstructionFunctor.map (cofiberStableSubobject X)) a)
      (Opposite.op ⦋n⦌)) e
  change (objectSConstructionFunctor.map (cofiberStableSubobject X)).app (Opposite.op ⦋n⦌)
    ((simplexLeftFiberProjection _ a).app (Opposite.op ⦋n⦌) e) =
      (SSet.yonedaEquiv.symm a).app (Opposite.op ⦋n⦌) (mcCarthyFiberParameter X a e) at he
  rw [SSet.yonedaEquiv_symm_app] at he
  have hd := congrArg gappedDiagram he
  rw [gappedDiagram_objectSFunctor_map, gappedDiagram_objectS_map] at hd
  change mcCarthyFiberDiagram X a e ≫ (cofiberStableSubobject X).val = _ at hd
  rw [cofiberProjection_source]
  exact hd

/-- 概要：左 fiber の図式は元の単体の面・退化に沿って前合成される。
方針：第一射影の自然性と object S の制限の式。
規約：全ての単体作用素を許す。使われ方：ρ の自然性。 -/
lemma mcCarthyFiberDiagram_map (X : StableModel.{u}) {m n l : ℕ}
    (a : (objectSConstruction X.carrier) _⦋m⦌) (e : (cofiberSubobjectLeftFiber X a) _⦋n⦌)
    (σ : ⦋l⦌ ⟶ ⦋n⦌) :
    mcCarthyFiberDiagram X a ((cofiberSubobjectLeftFiber X a).map σ.op e) =
      arNerveMap σ.toOrderHom ≫ mcCarthyFiberDiagram X a e := by
  have hn := ConcreteCategory.congr_hom
    ((simplexLeftFiberProjection
      (objectSConstructionFunctor.map (cofiberStableSubobject X)) a).naturality σ.op) e
  symm at hn
  change (objectSConstruction (cofiberDiagrams X.carrier)).map σ.op
      ((simplexLeftFiberProjection _ a).app (Opposite.op ⦋n⦌) e) =
    (simplexLeftFiberProjection _ a).app (Opposite.op ⦋l⦌)
      ((cofiberSubobjectLeftFiber X a).map σ.op e) at hn
  dsimp only [mcCarthyFiberDiagram]
  rw [← hn, gappedDiagram_objectS_map]
  rfl

/-- 概要：左 fiber のパラメーターは元の単体作用素で制限される。
方針：第二射影の自然性。
規約：標準単体の実際の射。使われ方：動かした添字の自然性。 -/
lemma mcCarthyFiberParameter_map (X : StableModel.{u}) {m n l : ℕ}
    (a : (objectSConstruction X.carrier) _⦋m⦌) (e : (cofiberSubobjectLeftFiber X a) _⦋n⦌)
    (σ : ⦋l⦌ ⟶ ⦋n⦌) :
    mcCarthyFiberParameter X a ((cofiberSubobjectLeftFiber X a).map σ.op e) =
      (Δ[m] : SSet.{u}).map σ.op (mcCarthyFiberParameter X a e) :=
  (ConcreteCategory.congr_hom
    ((simplexLeftFiberParameter
      (objectSConstructionFunctor.map (cofiberStableSubobject X)) a).naturality σ.op) e)

end SerrePositivity.KST.SConstruction
