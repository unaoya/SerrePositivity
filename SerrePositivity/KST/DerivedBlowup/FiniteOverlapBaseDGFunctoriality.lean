module

public import SerrePositivity.KST.DerivedBlowup.FiniteOverlapBaseDGTransition

/-!
概要：KST §3.1 の共通基底環上の有限重なり dg 遷移の関手性。
方針：各 Hom の元の像を元の半線形遷移へ戻し、証明済みの合成・恒等公式を使う。
規約：同じ基底環上の dg 関手の等式として述べる。
使われ方：全有限重なりの dg 代数関手への組立て。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory
open DifferentialGraded DifferentialGraded.ScalarExtension

variable (R : Type u) [CommRing R] {I : Type} [DecidableEq I]

set_option maxHeartbeats 4000000 in
-- 三つの局所化環の Hom と基底制限の対象を照合するために必要。
set_option synthInstance.maxHeartbeats 100000 in
-- 局所化環と基底環の複体のモノイダル構造を照合するために必要。
/-- 概要：共通基底環上の有限重なり dg 遷移は合成を保つ。
方針：対象を一対象性で比較し、Hom の各次数で元の半線形遷移の合成公式を使う。
規約：KST §3.1。使われ方：共通基底環上の dg 代数図式の合成律。 -/
theorem finiteOverlapBaseDGTransition_comp (a : I → R) (i k l : I) {T U V : Finset I}
    (h : T ⊆ U) (g : U ⊆ V) (hi : i ∈ T) (hk : k ∈ U) :
    EnrichedFunctor.comp (Complex R) (finiteOverlapBaseDGTransition R a i k h hi)
      (finiteOverlapBaseDGTransition R a k l g hk) =
      finiteOverlapBaseDGTransition R a i l (h.trans g) hi := by
  have hsingle : Subsingleton (FiniteOverlapKoszulObject R a l V) :=
    ⟨fun x y => by cases x; cases y; rfl⟩
  refine EnrichedFunctor.ext (Complex R)
    (F := EnrichedFunctor.comp (Complex R) (finiteOverlapBaseDGTransition R a i k h hi)
      (finiteOverlapBaseDGTransition R a k l g hk))
    (G := finiteOverlapBaseDGTransition R a i l (h.trans g) hi) (fun _ => hsingle.elim _ _) ?_
  intro v w
  simp only [eqToHom_refl, Category.comp_id]
  apply HomologicalComplex.Hom.ext
  funext q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change (((finiteOverlapBaseDGTransition R a k l g hk).map _ _).f q)
      ((((finiteOverlapBaseDGTransition R a i k h hi).map v w).f q) z) =
    (((finiteOverlapBaseDGTransition R a i l (h.trans g) hi).map v w).f q) z
  rw [finiteOverlapBaseDGTransition_apply, finiteOverlapBaseDGTransition_apply,
    finiteOverlapBaseDGTransition_apply, finiteOverlapBaseDGTransition_obj,
    finiteOverlapBaseDGTransition_obj]
  exact finiteOverlapDGTransition_comp_apply R a i k l h g hi hk v w q z

set_option maxHeartbeats 4000000 in
-- 局所化環の恒等遷移と基底制限の Hom を照合するために必要。
set_option synthInstance.maxHeartbeats 100000 in
-- 局所化環と基底環の複体のモノイダル構造を照合するために必要。
/-- 概要：共通基底環上の有限重なり dg 遷移は恒等を保つ。
方針：対象を一対象性で比較し、Hom の各次数で恒等遷移の元の公式を使う。
規約：KST §3.1。使われ方：共通基底環上の dg 代数図式の恒等律。 -/
theorem finiteOverlapBaseDGTransition_id (a : I → R) (i : I) (T : Finset I) (hi : i ∈ T) :
    finiteOverlapBaseDGTransition R a i i (Finset.Subset.refl T) hi =
      EnrichedFunctor.id (Complex R) (FiniteOverlapBaseKoszulObject R a i T) := by
  have hsingle : Subsingleton (FiniteOverlapKoszulObject R a i T) :=
    ⟨fun x y => by cases x; cases y; rfl⟩
  refine EnrichedFunctor.ext (Complex R)
    (F := finiteOverlapBaseDGTransition R a i i (Finset.Subset.refl T) hi)
    (G := EnrichedFunctor.id (Complex R) (FiniteOverlapBaseKoszulObject R a i T))
    (fun _ => hsingle.elim _ _) ?_
  intro v w
  simp only [eqToHom_refl, Category.comp_id]
  apply HomologicalComplex.Hom.ext
  funext q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change (((finiteOverlapBaseDGTransition R a i i (Finset.Subset.refl T) hi).map v w).f q) z = z
  rw [finiteOverlapBaseDGTransition_apply]
  exact finiteOverlapDGTransition_id_apply R a i T hi v w q z

end SerrePositivity.KST.DerivedBlowup
