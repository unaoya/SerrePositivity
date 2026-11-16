module

public import Mathlib.AlgebraicTopology.SimplicialSet.Degenerate
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve

/-!
概要：実鎖の一辺が恒等射の輸送なら、元のnerveでその辺を退化として縮約できる。
方針：その点だけを後続点へ動かす順序関手と、恒等射の輸送になる自然な比較を使う。
規約：元の実関手と元の単体集合の退化の等式を構成する。
使われ方：Riehl–Verity §3.1・§4.1–§4.2の実親の非退化性、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の同型な実辺の検出。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u w

open CategoryTheory
open scoped Simplicial

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：恒等射の輸送になる一辺を縮約し退化させると元の実全鎖へ戻る。
方針：縮約の順序自己関手への点ごとの比較が、元の関手で恒等射の輸送になることを示す。
規約：全射を含む実関手の等式。使われ方：Riehl–Verity §3.1の元のnerveの退化。 -/
lemma nerve_sigma_delta_of_eqToHom_edge {C : Type u} [Category.{v} C] {n : ℕ}
    (F : ComposableArrows C (n + 1)) (j : Fin (n + 1))
    (hobj : F.obj j.castSucc = F.obj j.succ)
    (hedge : F.map (homOfLE (Fin.castSucc_le_succ j)) = eqToHom hobj) :
    (nerve C).σ j ((nerve C).δ j.castSucc F) = F := by
  classical
  let S := (SimplexCategory.σ j).toOrderHom.monotone.functor
  let D := (SimplexCategory.δ j.castSucc).toOrderHom.monotone.functor
  let Q := S ⋙ D
  have hle (i : Fin (n + 2)) : i ≤ Q.obj i := by
    change i ≤ j.castSucc.succAbove (j.predAbove i)
    by_cases hi : i = j.castSucc
    · subst i
      rw [Fin.predAbove_castSucc_self, Fin.succAbove_castSucc_self]
      exact Fin.castSucc_le_succ j
    · rw [Fin.succAbove_predAbove hi]
  have hh (i : Fin (n + 2)) : ∃ h : F.obj i = F.obj (Q.obj i),
      F.map (homOfLE (hle i)) = eqToHom h := by
    by_cases hi : i = j.castSucc
    · subst i
      have hq : Q.obj j.castSucc = j.succ := by
        change j.castSucc.succAbove (j.predAbove j.castSucc) = j.succ
        rw [Fin.predAbove_castSucc_self, Fin.succAbove_castSucc_self]
      have hm : homOfLE (hle j.castSucc) =
          homOfLE (Fin.castSucc_le_succ j) ≫ eqToHom hq.symm := Subsingleton.elim _ _
      refine ⟨hobj.trans (congrArg F.obj hq.symm), ?_⟩
      rw [hm, F.map_comp, hedge, eqToHom_map, eqToHom_trans]
    · have hq : Q.obj i = i := Fin.succAbove_predAbove hi
      have hm : homOfLE (hle i) = eqToHom hq.symm := Subsingleton.elim _ _
      refine ⟨congrArg F.obj hq.symm, ?_⟩
      rw [hm, eqToHom_map]
  choose ho hm using hh
  have hF : F = Q ⋙ F := by
    refine CategoryTheory.Functor.ext ho ?_
    intro a b f
    have hn : F.map f ≫ F.map (homOfLE (hle b)) =
        F.map (homOfLE (hle a)) ≫ F.map (Q.map f) := by
      rw [← F.map_comp, ← F.map_comp]
      exact congrArg (fun q => F.map q) (Subsingleton.elim _ _)
    rw [hm a, hm b] at hn
    calc
      F.map f = (F.map f ≫ eqToHom (ho b)) ≫ eqToHom (ho b).symm := by simp
      _ = (eqToHom (ho a) ≫ F.map (Q.map f)) ≫ eqToHom (ho b).symm :=
        congrArg (fun q => q ≫ eqToHom (ho b).symm) hn
      _ = _ := Category.assoc _ _ _
  exact hF.symm

/-- 概要：恒等射の輸送になる一辺を持つ実全単体は元のnerveの宇宙持ち上げでも退化。
方針：実面を低次の単体に取り、元の実退化の像として元を回収する。
規約：元の単体集合のdegenerateを結論とする。使われ方：Riehl–Verity §4.1の非退化性。 -/
lemma uliftNerve_degenerate_of_eqToHom_edge {C : Type u} [Category.{v} C] {n : ℕ}
    (F : ComposableArrows C (n + 1)) (j : Fin (n + 1))
    (hobj : F.obj j.castSucc = F.obj j.succ)
    (hedge : F.map (homOfLE (Fin.castSucc_le_succ j)) = eqToHom hobj) :
    ULift.up F ∈ (SSet.uliftFunctor.{w, max u v}.obj (nerve C)).degenerate (n + 1) := by
  let X := SSet.uliftFunctor.{w, max u v}.obj (nerve C)
  have he : X.σ j (ULift.up ((nerve C).δ j.castSucc F)) = ULift.up F := by
    apply ULift.ext
    exact nerve_sigma_delta_of_eqToHom_edge F j hobj hedge
  have hd := X.σ_mem_degenerate j (ULift.up ((nerve C).δ j.castSucc F))
  exact he ▸ hd

end SerrePositivity.InfinityCategories.HA.Monads
