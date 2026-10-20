module

public import SerrePositivity.EInfinity.Hammock.WordForwardCore

/-!
# forward 部分語の元の像と交わり

概要：forward 部分語の写像の像は元の列の像への所属を反映し、交わりを保つ。
方針：元の包含への因子分解と色の保存から原像も forward であることを回収する。
規約：全写像の像を扱い、交わりの等式に単射性を追加しない。
使われ方：forward 部分語で前合成した図式の proper 性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.Word
open CategoryTheory

lemma forwardMap_apply_fac {a b : Word} (f : a ⟶ b) (i : Fin (forwardCore a).length) :
    (forwardInclusion b).orderHom ((forwardMap f).orderHom i) =
      f.orderHom ((forwardInclusion a).orderHom i) :=
  congrArg (fun g : forwardCore a ⟶ b => g.orderHom i) (forwardMap_fac f)

lemma forwardMap_injective {a b : Word} (f : a ⟶ b) (hf : Function.Injective f.orderHom) :
    Function.Injective (forwardMap f).orderHom := by
  intro i j hij
  apply forwardInclusion_injective a
  apply hf
  rw [← forwardMap_apply_fac, ← forwardMap_apply_fac, hij]

lemma forwardMap_range_iff {a b : Word} (f : a ⟶ b) (j : Fin (forwardCore b).length) :
    j ∈ Set.range (forwardMap f).orderHom ↔
      (forwardInclusion b).orderHom j ∈ Set.range f.orderHom := by
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨(forwardInclusion a).orderHom i, (forwardMap_apply_fac f i).symm⟩
  · rintro ⟨i, hi⟩
    have hd : a.direction i = .forward := (f.direction_eq i).symm.trans
      ((congrArg b.direction hi).trans (forwardCore_direction b j))
    obtain ⟨k, hk⟩ := (forwardInclusion_range a i).2 hd
    refine ⟨k, forwardInclusion_injective b ?_⟩
    rw [forwardMap_apply_fac, hk, hi]

lemma forwardMap_intersection_range {a b c : Word} (f : a ⟶ c) (g : b ⟶ c) :
    Set.range (forwardMap (intersectionInclusion f g)).orderHom =
      Set.range (forwardMap f).orderHom ∩ Set.range (forwardMap g).orderHom := by
  ext j
  simp only [Set.mem_inter_iff, forwardMap_range_iff, intersectionInclusion_range]

end SerrePositivity.EInfinity.Hammock.Word
