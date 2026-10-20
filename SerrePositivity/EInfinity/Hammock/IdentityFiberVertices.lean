module

public import SerrePositivity.EInfinity.Hammock.IdentityColumn
public import SerrePositivity.EInfinity.Hammock.WordEmbeddingMapComponents

/-!
# 恒等列による切断の fiber 内の元の頂点の同定

概要：像の外が恒等列なら、同じ切断を持つ元の全頂点は等しい。
方針：切断の単調性と隣接恒等列を使い、有限区間で帰納する。
規約：任意の zigzag の元の頂点について証明し、既に像にあるとは仮定しない。
使われ方：恒等列の条件からの原像対象の構成。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.EInfinity.Hammock
open CategoryTheory

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C} {a b : Word} {X Y : C}
  (f : a ⟶ b) (R : Zigzag W b X Y) (hR : IdentityOutside f R)
include hR

lemma identityFiber_vertex_of_le (p q : Fin (b.length + 1)) (hpq : p ≤ q)
    (h : f.cut p = f.cut q) : R.vertex p = R.vertex q := by
  induction q using Fin.induction generalizing p with
  | zero =>
    have hp : p = 0 := le_antisymm hpq (Fin.zero_le p)
    subst p
    rfl
  | succ q ih =>
    by_cases hp : p = q.succ
    · subst p
      rfl
    · have hp' : p ≤ q.castSucc := by
        have hne : p.val ≠ q.val + 1 := fun he => hp (Fin.ext he)
        change p.val ≤ q.val + 1 at hpq
        change p.val ≤ q.val
        omega
      have hmid : f.cut q.castSucc = f.cut q.succ := by
        apply le_antisymm (f.cut_monotone (Fin.castSucc_le_succ q))
        rw [← h]
        exact f.cut_monotone hp'
      exact (ih p hp' (h.trans hmid.symm)).trans
        (hR q (f.no_image_of_cut_eq q hmid)).vertex_eq

/-- 任意の原像候補の同じ切断の fiber 内の元の頂点は等しい。 -/
lemma identityFiber_vertex (p q : Fin (b.length + 1)) (h : f.cut p = f.cut q) :
    R.vertex p = R.vertex q := by
  rcases le_total p q with hpq | hqp
  · exact identityFiber_vertex_of_le f R hR p q hpq h
  · exact (identityFiber_vertex_of_le f R hR q p hqp h.symm).symm

/-- 既存の切断の切断写像で選んだ頂点は、同じ fiber 内のどの元の頂点とも一致。 -/
lemma identityFiber_embeddingVertex (hf : Function.Injective f.orderHom)
    (i : Fin (a.length + 1)) (j : Fin (b.length + 1)) (h : f.cut j = i) :
    R.vertex (WordAction.embeddingVertex f hf i) = R.vertex j :=
  identityFiber_vertex f R hR _ j ((WordAction.cut_embeddingVertex f hf i).trans h.symm)

end SerrePositivity.EInfinity.Hammock
