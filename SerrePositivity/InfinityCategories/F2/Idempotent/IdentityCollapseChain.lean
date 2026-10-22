module

public import SerrePositivity.InfinityCategories.F2.Idempotent.IdentityCollapse

/-!
概要：元の恒等値を持つ隣接射を潰しても、元の全 nerve 単体を回収する。
方針：元の順序比較の各成分を対象の等式による恒等輸送と照合する。
規約：元の全射・合成を保つ自然変換から単体全体の等式を証明する。
使われ方：元の非退化単体の全隣接射が吸収射であることの判定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Idempotent

/-- 非分裂対象を始点とする元の恒等輸送は、元の恒等値を持つ。 -/
lemma walkingScalar_eqToHom_source {P Q : WalkingSplit.{u}} (h : P = Q)
    (hp : P = walkingSource) : walkingScalar (eqToHom h).f = 1 := by
  subst Q
  subst P
  rfl

/-- 元の恒等値の射は、元の両対象の等式による恒等輸送そのもの。 -/
lemma walkingHom_eqToHom_of_one {P Q : WalkingSplit.{u}} (f : P ⟶ Q)
    (h : walkingScalar f.f = 1) :
    f = eqToHom ((walkingHom_one_endpoints f h).1.trans (walkingHom_one_endpoints f h).2.symm) := by
  apply CategoryTheory.Idempotents.Karoubi.Hom.ext
  exact h.trans (walkingScalar_eqToHom_source _ (walkingHom_one_endpoints f h).1).symm

/-- 元の恒等値の隣接射を潰した全単体の対象は、元の対象そのもの。 -/
lemma identityCollapse_obj_eq {n : ℕ} (i : Fin (n + 1))
    (F : ComposableArrows WalkingSplit.{u} (n + 1))
    (h : walkingScalar (F.map (homOfLE i.castSucc_le_succ)).f = 1) (j : Fin (n + 2)) :
    F.obj (identityCollapse i j) = F.obj j := by
  by_cases hj : j = i.succ
  · subst j
    rw [identityCollapse_succ]
    exact (walkingHom_one_endpoints _ h).1.trans (walkingHom_one_endpoints _ h).2.symm
  · exact congrArg F.obj (identityCollapse_of_ne i j hj)

/-- 元の順序比較は、元の全単体に沿うと恒等輸送そのもの。 -/
lemma identityCollapseComparison_app {n : ℕ} (i : Fin (n + 1))
    (F : ComposableArrows WalkingSplit.{u} (n + 1))
    (h : walkingScalar (F.map (homOfLE i.castSucc_le_succ)).f = 1) (j : Fin (n + 2)) :
    (identityCollapseComparison i F).app j = eqToHom (identityCollapse_obj_eq i F h j) := by
  change F.map (homOfLE (identityCollapse_le i j)) = _
  by_cases hj : j = i.succ
  · subst j
    have hr : homOfLE (identityCollapse_le i i.succ) =
        eqToHom (identityCollapse_succ i) ≫ homOfLE i.castSucc_le_succ :=
      Subsingleton.elim _ _
    rw [hr, F.map_comp, walkingHom_eqToHom_of_one _ h, eqToHom_map, eqToHom_trans]
  · have hr : homOfLE (identityCollapse_le i j) = eqToHom (identityCollapse_of_ne i j hj) :=
      Subsingleton.elim _ _
    rw [hr, eqToHom_map]

/-- 元の恒等値の隣接射を潰しても、元の全 nerve 単体は厳密に同じ。 -/
lemma identityCollapse_chain_eq {n : ℕ} (i : Fin (n + 1))
    (F : ComposableArrows WalkingSplit.{u} (n + 1))
    (h : walkingScalar (F.map (homOfLE i.castSucc_le_succ)).f = 1) :
    (identityCollapse i).monotone.functor ⋙ F = F := by
  refine CategoryTheory.Functor.ext_of_iso
    (NatIso.ofComponents (fun j ↦ eqToIso (identityCollapse_obj_eq i F h j)) ?_)
    (identityCollapse_obj_eq i F h) (fun _ ↦ rfl)
  intro j k f
  simpa only [eqToIso.hom, ← identityCollapseComparison_app i F h] using
    (identityCollapseComparison i F).naturality f

end SerrePositivity.InfinityCategories.F2.Idempotent
