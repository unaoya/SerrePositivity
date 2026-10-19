module

public import SerrePositivity.KST.DerivedBlowup.FiniteOverlapExceptionalBaseTransition

/-!
概要：KST v4 Lemma 3.6（pp.11–14）の共通基底環上の例外因子 dg 遷移の関手性。
方針：基底制限後の成分を元の半線形遷移へ戻し、全次数の恒等・合成則を使う。
規約：同じ基底環上の実際の dg 関手の等式として述べる。
使われ方：例外因子の全有限重なりの係数図式を組み立てる。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory DifferentialGraded

variable (R : Type u) [CommRing R] {I : Type} [DecidableEq I]

set_option maxHeartbeats 4000000 in
-- 三つの局所化環の Hom と共通基底環での制限を照合するために必要。
set_option synthInstance.maxHeartbeats 100000 in
-- 局所化環と基底環上の複体のモノイダル構造を照合するために必要。
/-- 概要：共通基底環上の例外因子 dg 遷移は合成を保つ。
方針：一対象性で対象をそろえ、元の半線形遷移の各次数の合成公式を使う。
規約：KST Lemma 3.6。使われ方：全有限重なり dg 代数関手の合成律。 -/
theorem finiteOverlapExceptionalBaseDGTransition_comp (a : I → R) (i k l : I)
    {T U V : Finset I} (h : T ⊆ U) (g : U ⊆ V) (hi : i ∈ T) (hk : k ∈ U) :
    (finiteOverlapExceptionalBaseDGTransition R a i k h hi).comp
        (finiteOverlapExceptionalBaseDGTransition R a k l g hk) =
      finiteOverlapExceptionalBaseDGTransition R a i l (h.trans g) hi := by
  have hsingle : Subsingleton (FiniteOverlapExceptionalKoszulObject R a l V) :=
    ⟨fun x y => by cases x; cases y; rfl⟩
  refine EnrichedFunctor.ext (Complex R)
    (F := (finiteOverlapExceptionalBaseDGTransition R a i k h hi).comp
      (finiteOverlapExceptionalBaseDGTransition R a k l g hk))
    (G := finiteOverlapExceptionalBaseDGTransition R a i l (h.trans g) hi)
    (fun _ => hsingle.elim _ _) ?_
  intro v w
  simp only [eqToHom_refl, Category.comp_id]
  apply HomologicalComplex.Hom.ext
  funext q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change (((finiteOverlapExceptionalBaseDGTransition R a k l g hk).map _ _).f q)
      ((((finiteOverlapExceptionalBaseDGTransition R a i k h hi).map v w).f q) z) =
    (((finiteOverlapExceptionalBaseDGTransition R a i l (h.trans g) hi).map v w).f q) z
  rw [finiteOverlapExceptionalBaseDGTransition_apply,
    finiteOverlapExceptionalBaseDGTransition_apply,
    finiteOverlapExceptionalBaseDGTransition_apply, finiteOverlapExceptionalBaseDGTransition_obj,
    finiteOverlapExceptionalBaseDGTransition_obj]
  exact finiteOverlapExceptionalDGTransition_comp_apply R a i k l h g hi hk v w q z

set_option maxHeartbeats 2000000 in
-- 局所化環の恒等遷移と共通基底環の Hom を照合するために必要。
set_option synthInstance.maxHeartbeats 100000 in
-- 局所化環と基底環上の複体のモノイダル構造を照合するために必要。
/-- 概要：共通基底環上の例外因子 dg 遷移は恒等を保つ。
方針：一対象性で対象を比較し、元の半線形恒等遷移の成分公式を使う。
規約：KST Lemma 3.6。使われ方：全有限重なり dg 代数関手の恒等律。 -/
theorem finiteOverlapExceptionalBaseDGTransition_id (a : I → R) (i : I)
    (T : Finset I) (hi : i ∈ T) :
    finiteOverlapExceptionalBaseDGTransition R a i i (Finset.Subset.refl T) hi =
      DGFunctor.id (FiniteOverlapExceptionalBaseObject R a i T) := by
  have hsingle : Subsingleton (FiniteOverlapExceptionalKoszulObject R a i T) :=
    ⟨fun x y => by cases x; cases y; rfl⟩
  refine EnrichedFunctor.ext (Complex R)
    (F := finiteOverlapExceptionalBaseDGTransition R a i i (Finset.Subset.refl T) hi)
    (G := DGFunctor.id (FiniteOverlapExceptionalBaseObject R a i T))
    (fun _ => hsingle.elim _ _) ?_
  intro v w
  simp only [eqToHom_refl, Category.comp_id]
  apply HomologicalComplex.Hom.ext
  funext q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change (((finiteOverlapExceptionalBaseDGTransition R a i i
    (Finset.Subset.refl T) hi).map v w).f q) z = z
  rw [finiteOverlapExceptionalBaseDGTransition_apply]
  exact finiteOverlapExceptionalDGTransition_id_apply R a i T hi v w q z

end SerrePositivity.KST.DerivedBlowup
