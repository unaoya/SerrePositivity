module

public import SerrePositivity.EInfinity.FrameHom.AnodyneWeakDetection

/-!
# 元の弱ホモトピー同値の二対六則と可縮な因子

概要：隣接する二つの合成が弱同値なら中間も弱同値となる。
方針：元の Kan 標的の反変 π₀ で単射性と全射性を別々に回収する。
規約：任意の単体集合に適用し、始終域の充填性を要求しない。
使われ方：葉の合成の弱同値と残りの有限木の可縮性の接続。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock
open CategoryTheory Limits SerrePositivity.InfinityCategories

lemma weak_middle_of_composites {A B C D : SSet.{u}}
    (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D)
    (hfg : IsWeakHomotopyEquivalence (f ≫ g))
    (hgh : IsWeakHomotopyEquivalence (g ≫ h)) : IsWeakHomotopyEquivalence g := by
  intro Z hZ
  let K := FrameHom.AnodyneWeakDetection.homComponents Z
  have h₁ : Function.Bijective (fun x => (K.map f.op) ((K.map g.op) x)) := by
    change Function.Bijective (K.map g.op ≫ K.map f.op)
    rw [← K.map_comp]
    exact hfg Z
  have h₂ : Function.Bijective (fun x => (K.map g.op) ((K.map h.op) x)) := by
    change Function.Bijective (K.map h.op ≫ K.map g.op)
    rw [← K.map_comp]
    exact hgh Z
  change Function.Bijective (K.map g.op)
  constructor
  · intro x y he
    apply h₁.1
    exact congrArg (K.map f.op) he
  · intro x
    obtain ⟨y, hy⟩ := h₂.2 x
    exact ⟨(K.map h.op) y, hy⟩

lemma contractible_of_weak_factor {A B C : SSet.{u}} (f : A ⟶ B) (g : B ⟶ C)
    (hfg : IsWeakHomotopyEquivalence (f ≫ g)) (hB : IsWeaklyContractible B) :
    IsWeaklyContractible A := by
  have hgh : IsWeakHomotopyEquivalence (g ≫ terminal.from C) := by
    have he : g ≫ terminal.from C = terminal.from B := terminal.hom_ext _ _
    rw [he]
    exact hB
  have hg := weak_middle_of_composites f g (terminal.from C) hfg hgh
  have hf := hg.cancel_right hfg
  have he : terminal.from A = f ≫ terminal.from B := terminal.hom_ext _ _
  change IsWeakHomotopyEquivalence (terminal.from A)
  rw [he]
  exact hf.comp hB

end SerrePositivity.EInfinity.Hammock
