module

public import Mathlib.Algebra.Homology.Opposite
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic

/-!
概要：通常の鎖複体から係数への反変 Hom による cochain とホモトピー同値の保存。
方針：鎖複体を反対圏へ移し、加法的 Yoneda 関手で群の複体へ送る。
規約：H_* の計算は行わず、cochain の比較に必要な通常の Hom の構成だけを使う。
使われ方：Goerss–Jardine III §2。正規化と非正規化 cochain のホモトピー比較。
-/

@[expose] public section

universe v u

open CategoryTheory Opposite

namespace SerrePositivity.KST.Spectra.ContravariantChainHom

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- 概要：鎖複体の各段から係数への Hom による cochain 複体。
方針：複体の反対と加法的 Yoneda 関手を合成する。
規約：微分は鎖の微分への前合成。
使われ方：Goerss–Jardine III §2。正規化比較を反変 Hom へ送る。 -/
def obj (P : ChainComplex C ℕ) (M : C) : CochainComplex AddCommGrpCat.{v} ℕ :=
  ((preadditiveYoneda.obj M).mapHomologicalComplex ((ComplexShape.down ℕ).symm)).obj P.op

/-- 概要：鎖複体の射への前合成による cochain の射。
方針：反対圏の複体の射を加法的 Yoneda へ送る。
規約：向きは反転する。
使われ方：Goerss–Jardine III §2。通常の正規化の cochain の比較射。 -/
def map {P Q : ChainComplex C ℕ} (f : P ⟶ Q) (M : C) : obj Q M ⟶ obj P M :=
  ((preadditiveYoneda.obj M).mapHomologicalComplex ((ComplexShape.down ℕ).symm)).map
    ((HomologicalComplex.opFunctor C (ComplexShape.down ℕ)).map f.op)

/-- 概要：鎖複体のホモトピー同値は反対複体のホモトピー同値を与える。
方針：順逆の射を交換して反対を取り、Mathlib のホモトピーの反対を使う。
規約：順射は元の逆射の反対。
使われ方：Goerss–Jardine III §2。反変 Hom が正規化の同値を保存するための入力。 -/
def oppositeHomotopyEquiv {P Q : ChainComplex C ℕ} (e : HomotopyEquiv P Q) :
    HomotopyEquiv P.op Q.op where
  hom := (HomologicalComplex.opFunctor C (ComplexShape.down ℕ)).map e.inv.op
  inv := (HomologicalComplex.opFunctor C (ComplexShape.down ℕ)).map e.hom.op
  homotopyHomInvId := by
    simpa only [op_comp, CategoryTheory.Functor.map_comp, op_id,
      CategoryTheory.Functor.map_id, HomologicalComplex.opFunctor_obj] using e.homotopyHomInvId.op
  homotopyInvHomId := by
    simpa only [op_comp, CategoryTheory.Functor.map_comp, op_id,
      CategoryTheory.Functor.map_id, HomologicalComplex.opFunctor_obj] using e.homotopyInvHomId.op

/-- 概要：鎖複体のホモトピー同値は係数への Hom の cochain のホモトピー同値を与える。
方針：反対複体の同値へ加法的 Yoneda 関手のホモトピー同値の保存を適用する。
規約：係数の入射性や完全性は不要。
使われ方：Goerss–Jardine III §2。正規化 cochain と通常の交代 cochain の比較。 -/
def homotopyEquiv {P Q : ChainComplex C ℕ} (e : HomotopyEquiv P Q) (M : C) :
    HomotopyEquiv (obj P M) (obj Q M) :=
  (preadditiveYoneda.obj M).mapHomotopyEquiv (oppositeHomotopyEquiv e)

end

end SerrePositivity.KST.Spectra.ContravariantChainHom
