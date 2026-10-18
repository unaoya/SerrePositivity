module

public import SerrePositivity.KST.DerivedBlowup.DGEndMonoid
public import SerrePositivity.KST.DerivedBlowup.FiniteOverlapBaseDGFunctoriality

/-!
概要：KST §3.1 の全非空有限重なりの dg 代数を実際の関手に束ねる。
方針：共通基底環へ制限した一対象 dg 圏の自己 Hom を Mon(Complex R) に送り、
実際の有限重なり遷移の恒等・合成公式で関手性を証明する。
規約：dg 代数の図式であり、加群の厳密な貼り合わせを定義するものではない。
使われ方：cartesian な coherent dg 加群模型の係数図式。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory
open DifferentialGraded

variable (R : Type u) [CommRing R] {I : Type} [DecidableEq I]

/-- 概要：有限重なりの Koszul dg 代数を共通基底環の複体のモノイド対象にする。
方針：基底制限した一対象 dg 圏の自己 Hom を使う。
規約：KST §3.1。使われ方：全有限重なり関手の対象。 -/
def finiteOverlapDGAlgebra (a : I → R) (i : I) (T : Finset I) : Mon (Complex R) :=
  dgEndMonoid R (FiniteOverlapBaseKoszulObject R a i T) .point

set_option maxHeartbeats 2000000 in
-- 局所化環の dg 遷移と共通基底環のモノイド対象の構造射を照合するために必要。
set_option synthInstance.maxHeartbeats 100000 in
-- 局所化環と基底環の複体のモノイダル構造を照合するために必要。
/-- 概要：有限重なりの実際の dg 遷移からモノイド対象の射を作る。
方針：共通基底環上の Hom 写像と dg 関手の単位・積保存を使う。
規約：KST §3.1。使われ方：全有限重なり関手の射。 -/
def finiteOverlapDGAlgebraMap (a : I → R) (i k : I) {T U : Finset I}
    (h : T ⊆ U) (hi : i ∈ T) : finiteOverlapDGAlgebra R a i T ⟶ finiteOverlapDGAlgebra R a k U :=
  Mon.Hom.mk' ((finiteOverlapBaseDGTransition R a i k h hi).map .point .point)
    ((finiteOverlapBaseDGTransition R a i k h hi).map_id .point)
    ((finiteOverlapBaseDGTransition R a i k h hi).map_comp .point .point .point)

set_option maxHeartbeats 4000000 in
-- 三つの局所化環の遷移の Hom を基底環の複体上で照合するために必要。
set_option synthInstance.maxHeartbeats 100000 in
-- 局所化環と基底環の複体のモノイダル構造を照合するために必要。
/-- 概要：有限重なりの dg 代数射は合成を保つ。
方針：モノイド対象の射を各次数の元で比較し、元の半線形遷移の合成公式を使う。
規約：KST §3.1。使われ方：全有限重なりの dg 代数関手の合成律。 -/
theorem finiteOverlapDGAlgebraMap_comp (a : I → R) (i k l : I) {T U V : Finset I}
    (h : T ⊆ U) (g : U ⊆ V) (hi : i ∈ T) (hk : k ∈ U) :
    finiteOverlapDGAlgebraMap R a i k h hi ≫ finiteOverlapDGAlgebraMap R a k l g hk =
      finiteOverlapDGAlgebraMap R a i l (h.trans g) hi := by
  apply Mon.Hom.ext
  apply HomologicalComplex.Hom.ext
  funext q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change (((finiteOverlapBaseDGTransition R a k l g hk).map .point .point).f q)
      ((((finiteOverlapBaseDGTransition R a i k h hi).map .point .point).f q) z) =
    (((finiteOverlapBaseDGTransition R a i l (h.trans g) hi).map .point .point).f q) z
  rw [finiteOverlapBaseDGTransition_apply, finiteOverlapBaseDGTransition_apply,
    finiteOverlapBaseDGTransition_apply]
  exact finiteOverlapDGTransition_comp_apply R a i k l h g hi hk .point .point q z

set_option maxHeartbeats 2000000 in
-- 局所化環の恒等遷移を基底環の複体上で照合するために必要。
set_option synthInstance.maxHeartbeats 100000 in
-- 局所化環と基底環の複体のモノイダル構造を照合するために必要。
/-- 概要：有限重なりの dg 代数射は恒等を保つ。
方針：各次数の元で恒等遷移の公式を使う。
規約：KST §3.1。使われ方：全有限重なりの dg 代数関手の恒等律。 -/
theorem finiteOverlapDGAlgebraMap_id (a : I → R) (i : I) (T : Finset I) (hi : i ∈ T) :
    finiteOverlapDGAlgebraMap R a i i (Finset.Subset.refl T) hi = 𝟙 _ := by
  apply Mon.Hom.ext
  apply HomologicalComplex.Hom.ext
  funext q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change (((finiteOverlapBaseDGTransition R a i i (Finset.Subset.refl T) hi).map .point .point).f q)
    z = z
  rw [finiteOverlapBaseDGTransition_apply]
  exact finiteOverlapDGTransition_id_apply R a i T hi .point .point q z

/-- 概要：全非空有限重なりを共通基底環上の dg 代数へ送る実際の関手。
方針：各重なりで選択した pivot の模型を使い、証明済みの恒等・合成則を束ねる。
規約：KST §3.1、添字は有限集合の包含順序。
使われ方：coherent な homotopy-cartesian dg 加群の係数図式。 -/
def finiteOverlapDGAlgebraDiagram (a : I → R) : FiniteOverlapIndex I ⥤ Mon (Complex R) where
  obj T := finiteOverlapDGAlgebra R a (finiteOverlapIndexPivot T) T.val
  map {T U} f := finiteOverlapDGAlgebraMap R a
    (finiteOverlapIndexPivot T) (finiteOverlapIndexPivot U)
    (leOfHom f) (finiteOverlapIndexPivot_mem T)
  map_id T := finiteOverlapDGAlgebraMap_id R a _ T.val (finiteOverlapIndexPivot_mem T)
  map_comp {T U _V} f g := (finiteOverlapDGAlgebraMap_comp R a _ _ _ (leOfHom f) (leOfHom g)
    (finiteOverlapIndexPivot_mem T) (finiteOverlapIndexPivot_mem U)).symm

end SerrePositivity.KST.DerivedBlowup
