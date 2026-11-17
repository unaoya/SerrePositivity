module

public import SerrePositivity.InfinityCategories.HA.Monads.NondegenerateFaceDegeneracy
public import SerrePositivity.InfinityCategories.HA.Monads.ComposableArrowRefinementPositions
public import SerrePositivity.InfinityCategories.HA.Monads.NerveDegeneracyEdges

/-!
概要：非退化な実全鎖の細分は、左対象が異なり右因子が非同型なら非退化。
方針：指定面の非退化性で退化を両隣へ限定し、挿入対象と右因子で排除する。
規約：元のnerveの宇宙持ち上げの実単体作用を使う。
使われ方：Riehl–Verity §4.1–§4.2の実親の非退化性、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前のcoherentな随伴の実構成。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u w

open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：元の非退化な実鎖の二つの隣接退化を排除すれば細分も非退化。
方針：左の退化は挿入対象の相違、右の退化は実右因子の非同型性で排除する。
規約：全鎖の非退化性を結論として得る。使われ方：Riehl–Verity §4.1の実親の検収。 -/
lemma composableArrowRefinement_nondegenerate {C : Type u} [Category.{v} C] {n : ℕ}
    (F : ComposableArrows C (n + 1)) (k : Fin (n + 1))
    (B : C) (q : F.obj k.castSucc ⟶ B) (g : B ⟶ F.obj k.succ)
    (fac : q ≫ g = F.map (homOfLE (Fin.castSucc_le_succ k)))
    (hnd : ULift.up F ∈ (SSet.uliftFunctor.{w, max u v}.obj (nerve C)).nonDegenerate (n + 1))
    (hq : F.obj k.castSucc ≠ B) (hg : ¬ IsIso g) :
    ULift.up (composableArrowRefinement F k B q g) ∈
      (SSet.uliftFunctor.{w, max u v}.obj (nerve C)).nonDegenerate (n + 2) := by
  let X := SSet.uliftFunctor.{w, max u v}.obj (nerve C)
  let G := composableArrowRefinement F k B q g
  let d := k.succ.castSucc
  have hface : X.δ d (ULift.up G) = ULift.up F := by
    apply ULift.ext
    exact composableArrowRefinement_face n F k B q g fac
  have hface_nd : X.δ d (ULift.up G) ∈ X.nonDegenerate (n + 1) := by
    rw [hface]
    exact hnd
  apply nondegenerate_of_face_and_no_adjacent_degeneracy (X := X) (ULift.up G) d hface_nd
  intro j hpos he
  rw [hface] at he
  have hh : (nerve C).σ j F = G := congrArg ULift.down he
  rcases hpos with hpos | hpos
  · have hj : j = k.succ := by
      apply Fin.ext
      have hv := congrArg Fin.val hpos
      change k.val + 1 = j.val at hv
      exact hv.symm
    subst j
    have hG : G = (nerve C).σ k.succ F := hh.symm
    have : IsIso (G.map (homOfLE (Fin.castSucc_le_succ k.succ))) := by
      rw [hG]
      exact nerve_degeneracy_edge_isIso F k.succ
    have hmiddle : G.obj d = B := composableArrowRefinement_middle n F k B q g
    have hafter : G.obj k.succ.succ = F.obj k.succ := by
      have ho := CategoryTheory.Functor.congr_obj (composableArrowRefinement_face n F k B q g fac)
        k.succ
      change G.obj (k.succ.castSucc.succAbove k.succ) = F.obj k.succ at ho
      rw [Fin.succAbove_castSucc_self] at ho
      exact ho
    exact hg (isIso_of_equal_objects_hom_heq hmiddle hafter _ g
      (composableArrowRefinement_right_edge n F k B q g))
  · have hj : j = k.castSucc := by
      apply Fin.ext
      have hv := congrArg Fin.val hpos
      change k.val + 1 = j.val + 1 at hv
      change j.val = k.val
      omega
    subst j
    have hm := congrArg (fun H : ComposableArrows C (n + 2) => H.obj d) hh
    rw [nerve.σ_obj] at hm
    have hp : k.castSucc.predAbove d = k.castSucc := by
      have hd : d = k.castSucc.succ := Fin.ext rfl
      rw [hd, Fin.predAbove_succ_self]
    rw [hp] at hm
    exact hq (hm.trans (composableArrowRefinement_middle n F k B q g))

end SerrePositivity.InfinityCategories.HA.Monads
