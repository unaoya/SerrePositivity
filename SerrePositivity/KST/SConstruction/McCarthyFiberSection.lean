module
public import SerrePositivity.KST.SConstruction.ObjectSConstantRestriction

/-! # McCarthy の左 fiber の quotient 射の厳密な切断
概要：固定単体の最後の対角零対象を用いて、quotient への射の切断を実際に構成する。
方針：零対象からの射の標準 cofiber 関手を使い、基底の等号で pullback に持ち上げる。
規約：切断だけでは弱同値性は結論しない。使われ方：Fiore–Pieper Lemma 4.24 の ι。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：ι 型の標準零 cofiber の subobject は指定零対象への定値完全関手。
方針：底の射の評価式と部分型の外延性。
規約：保存条件の証明の選択によらない。使われ方：左 fiber への切断の持ち上げ。 -/
lemma zeroCofiberStableFunctor_subobject_true (X : StableModel.{u}) (z : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroVertex X.carrier) :
    zeroCofiberStableFunctor X z true ≫ cofiberStableSubobject X = stableConstantZero X z :=
  Subtype.ext (zeroCofiberStableFunctor_subobject X z true)

/-- 概要：固定単体の左 fiber に quotient の object S を含める実際の切断。
方針：零対象からの射の cofiber 関手と、最後の頂点で一定なパラメーターを組にする。
規約：元の固定単体の最後の対角を零対象に使う。使われ方：McCarthy の ι の射。 -/
def mcCarthyFiberSection (X : StableModel.{u}) {m : ℕ}
    (a : (objectSConstruction X.carrier) _⦋m⦌) :
    objectSConstruction X.carrier ⟶ cofiberSubobjectLeftFiber X a :=
  simplexLeftFiberLift _ a
    (objectSConstructionFunctor.map
      (zeroCofiberStableFunctor X (objectSLastDiagonalZeroVertex a) true))
    (SSet.const (stdSimplex.obj₀Equiv.symm (Fin.last m))) (by
      rw [← CategoryTheory.Functor.map_comp, zeroCofiberStableFunctor_subobject_true,
        objectS_lastVertex_constantZero])

/-- 概要：切断が返す cofiber 図式は標準の零対象からの射の図式。
方針：左 fiber の持ち上げの第一射影の式。
規約：全ての単体で厳密に一致。使われ方：二つ目のホモトピーの終端。 -/
lemma mcCarthyFiberSection_projection (X : StableModel.{u}) {m : ℕ}
    (a : (objectSConstruction X.carrier) _⦋m⦌) :
    mcCarthyFiberSection X a ≫
      simplexLeftFiberProjection (objectSConstructionFunctor.map (cofiberStableSubobject X)) a =
      objectSConstructionFunctor.map
        (zeroCofiberStableFunctor X (objectSLastDiagonalZeroVertex a) true) :=
  simplexLeftFiberLift_projection _ _ _ _ _

/-- 概要：切断のパラメーターは固定単体の最後の頂点に定値。
方針：左 fiber の持ち上げの第二射影の式。
規約：実際の標準単体への射の等号。使われ方：基底の収縮の終端。 -/
lemma mcCarthyFiberSection_parameter (X : StableModel.{u}) {m : ℕ}
    (a : (objectSConstruction X.carrier) _⦋m⦌) :
    mcCarthyFiberSection X a ≫
      simplexLeftFiberParameter (objectSConstructionFunctor.map (cofiberStableSubobject X)) a =
      SSet.const (stdSimplex.obj₀Equiv.symm (Fin.last m)) :=
  simplexLeftFiberLift_parameter _ _ _ _ _

/-- 概要：McCarthy の左 fiber の quotient 射は構成した射を厳密な切断として持つ。
方針：標準零 cofiber の商の評価の厳密な等号を object S に送る。
規約：弱同値性や収縮はまだ含まない。使われ方：二つのホモトピーで左 fiber の弱同値を証明する。 -/
lemma mcCarthyFiberSection_quotient (X : StableModel.{u}) {m : ℕ}
    (a : (objectSConstruction X.carrier) _⦋m⦌) :
    mcCarthyFiberSection X a ≫ cofiberLeftFiberQuotient X a =
      𝟙 (objectSConstruction X.carrier) := by
  rw [cofiberLeftFiberQuotient, ← Category.assoc, mcCarthyFiberSection_projection,
    ← CategoryTheory.Functor.map_comp, zeroCofiberStableFunctor_quotient,
    CategoryTheory.Functor.map_id]
  rfl

end SerrePositivity.KST.SConstruction
