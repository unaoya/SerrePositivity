module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ArrowIdentityComposition

/-!
概要：同じ実比較辺を元の θ と照合し、対角の可逆性から入力面の普遍性へ戻す。
方針：全錐の写像と射影辺を保つ等号輸送、錐の圏の終性、右 fibration の反映を使う。
規約：一般安定性は仮定しない。使われ方：HA 1.4.2.15 の二条件からの切除判定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

lemma isIso_comp_of_arrowMk_eq {C : Type*} [Category C] {x y x' y' z : C}
    (f : x ⟶ y) (g : x' ⟶ y') (v : y ⟶ z) (h : Arrow.mk f = Arrow.mk g)
    (hv : IsIso (f ≫ v)) :
    IsIso (g ≫ eqToHom (congrArg Arrow.right h).symm ≫ v) := by
  have hx : x = x' := congrArg Arrow.left h
  have hy : y = y' := congrArg Arrow.right h
  cases hx
  cases hy
  have hfg : f = g := Arrow.mk_injective _ _ h
  simpa only [eqToHom_refl, Category.id_comp, ← hfg] using hv

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
