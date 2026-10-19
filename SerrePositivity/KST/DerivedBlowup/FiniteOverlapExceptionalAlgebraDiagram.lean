module

public import SerrePositivity.KST.DerivedBlowup.FiniteOverlapExceptionalBaseFunctoriality
public import SerrePositivity.KST.DerivedBlowup.DGEndMonoid
public import SerrePositivity.KST.DerivedBlowup.FiniteOverlapDiagram

/-!
概要：KST v4 Lemma 3.6（pp.11–14）の例外因子の全有限重なりの dg 代数関手。
方針：共通基底環上の一対象 dg 模型の自己 Hom をモノイド対象にし、指定遷移を使う。
規約：係数 dg 代数の図式であり、dg 加群の厳密な貼り合わせを課すものではない。
使われ方：例外因子の cartesian dg 加群模型と blowup への局所射。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory DifferentialGraded

variable (R : Type u) [CommRing R] {I : Type} [DecidableEq I]

/-- 概要：例外因子の有限重なりの dg 代数を共通基底環のモノイド対象にする。
方針：基底制限した一対象 dg 圏の自己 Hom を使う。
規約：KST Lemma 3.6。使われ方：全有限重なり関手の対象。 -/
def finiteOverlapExceptionalDGAlgebra (a : I → R) (i : I) (T : Finset I) : Mon (Complex R) :=
  dgEndMonoid R (FiniteOverlapExceptionalBaseObject R a i T) .point

set_option maxHeartbeats 2000000 in
-- 局所化環の dg 関手と共通基底環上のモノイド対象の構造射を照合するために必要。
set_option synthInstance.maxHeartbeats 100000 in
-- 局所化環と基底環上の複体のモノイダル構造を照合するために必要。
/-- 概要：例外因子の有限重なり dg 遷移をモノイド対象の射にする。
方針：指定 dg 遷移の Hom 写像と単位・積保存を使う。
規約：KST Lemma 3.6。使われ方：全有限重なり関手の射。 -/
def finiteOverlapExceptionalDGAlgebraMap (a : I → R) (i k : I) {T U : Finset I}
    (h : T ⊆ U) (hi : i ∈ T) :
    finiteOverlapExceptionalDGAlgebra R a i T ⟶ finiteOverlapExceptionalDGAlgebra R a k U :=
  Mon.Hom.mk' ((finiteOverlapExceptionalBaseDGTransition R a i k h hi).map .point .point)
    ((finiteOverlapExceptionalBaseDGTransition R a i k h hi).map_id .point)
    ((finiteOverlapExceptionalBaseDGTransition R a i k h hi).map_comp .point .point .point)

set_option maxHeartbeats 4000000 in
-- 三つの局所化環の遷移の Hom を共通基底環上で照合するために必要。
set_option synthInstance.maxHeartbeats 100000 in
-- 局所化環と基底環上の複体のモノイダル構造を照合するために必要。
/-- 概要：例外因子の有限重なりの dg 代数射は合成を保つ。
方針：Hom の各次数で元の半線形遷移の合成則を使う。
規約：KST Lemma 3.6。使われ方：係数図式の合成則。 -/
theorem finiteOverlapExceptionalDGAlgebraMap_comp (a : I → R) (i k l : I)
    {T U V : Finset I} (h : T ⊆ U) (g : U ⊆ V) (hi : i ∈ T) (hk : k ∈ U) :
    finiteOverlapExceptionalDGAlgebraMap R a i k h hi ≫
        finiteOverlapExceptionalDGAlgebraMap R a k l g hk =
      finiteOverlapExceptionalDGAlgebraMap R a i l (h.trans g) hi := by
  apply Mon.Hom.ext
  apply HomologicalComplex.Hom.ext
  funext q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change (((finiteOverlapExceptionalBaseDGTransition R a k l g hk).map .point .point).f q)
      ((((finiteOverlapExceptionalBaseDGTransition R a i k h hi).map .point .point).f q) z) =
    (((finiteOverlapExceptionalBaseDGTransition R a i l (h.trans g) hi).map .point .point).f q) z
  rw [finiteOverlapExceptionalBaseDGTransition_apply,
    finiteOverlapExceptionalBaseDGTransition_apply,
    finiteOverlapExceptionalBaseDGTransition_apply]
  exact finiteOverlapExceptionalDGTransition_comp_apply R a i k l h g hi hk .point .point q z

set_option maxHeartbeats 2000000 in
-- 局所化環の恒等遷移と共通基底環上の Hom を照合するために必要。
set_option synthInstance.maxHeartbeats 100000 in
-- 局所化環と基底環上の複体のモノイダル構造を照合するために必要。
/-- 概要：例外因子の有限重なり dg 代数射は恒等を保つ。
方針：全次数の元で恒等遷移の公式を使う。
規約：KST Lemma 3.6。使われ方：係数図式の単位条件。 -/
theorem finiteOverlapExceptionalDGAlgebraMap_id (a : I → R) (i : I)
    (T : Finset I) (hi : i ∈ T) :
    finiteOverlapExceptionalDGAlgebraMap R a i i (Finset.Subset.refl T) hi = 𝟙 _ := by
  apply Mon.Hom.ext
  apply HomologicalComplex.Hom.ext
  funext q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change (((finiteOverlapExceptionalBaseDGTransition R a i i
    (Finset.Subset.refl T) hi).map .point .point).f q) z = z
  rw [finiteOverlapExceptionalBaseDGTransition_apply]
  exact finiteOverlapExceptionalDGTransition_id_apply R a i T hi .point .point q z

/-- 概要：例外因子の全非空有限重なりの指定 dg 代数関手。
方針：各有限集合の選択 pivot と実際の局所化環射に沿う遷移を使う。
規約：KST Lemma 3.6、層の降下や共通 Koszul 表示との図式同値は後続の比較。
使われ方：例外因子の大域 cartesian dg 加群模型の係数。 -/
def finiteOverlapExceptionalDGAlgebraDiagram (a : I → R) :
    FiniteOverlapIndex I ⥤ Mon (Complex R) where
  obj T := finiteOverlapExceptionalDGAlgebra R a (finiteOverlapIndexPivot T) T.val
  map {T U} f := finiteOverlapExceptionalDGAlgebraMap R a
    (finiteOverlapIndexPivot T) (finiteOverlapIndexPivot U)
    (leOfHom f) (finiteOverlapIndexPivot_mem T)
  map_id T := finiteOverlapExceptionalDGAlgebraMap_id R a _ T.val (finiteOverlapIndexPivot_mem T)
  map_comp {T U _V} f g := (finiteOverlapExceptionalDGAlgebraMap_comp R a _ _ _
    (leOfHom f) (leOfHom g) (finiteOverlapIndexPivot_mem T) (finiteOverlapIndexPivot_mem U)).symm

end SerrePositivity.KST.DerivedBlowup
