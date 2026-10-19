module

public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import Mathlib.CategoryTheory.Abelian.Basic

/-!
概要：零延長は非輪状性と各項の固定対象からの全射呈示を保つ。
方針：像の中では標準成分同型、像の外では零対象の性質を使う。
規約：任意の複体形状の埋め込み。
使われ方：Stacks Lemma 19.12.2、TT §3・§8、Toën §3.2 の小さい整数複体の構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits
namespace SerrePositivity.KST.DerivedGeometry
variable {C : Type*} [Category* C] [Abelian C]
  {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  (K : HomologicalComplex C c) (e : c.Embedding c')

/--
概要：非輪状な複体の零延長は非輪状。
方針：像の中では延長のコホモロジー比較、像の外では零項を使う。
規約：全ての次数。
使われ方：Stacks 19.12.2、TT §3 の上に有界な整数複体。
-/
lemma extended_acyclic (hK : K.Acyclic) : (K.extend e).Acyclic := by
  intro i'
  by_cases hi : ∃ i, e.f i = i'
  · obtain ⟨i, hi⟩ := hi
    exact (K.extend_exactAt_iff e hi).mpr (hK i)
  · exact K.extend_exactAt e i' (by simpa using hi)

/--
概要：固定対象から各項へ全射があれば、零延長の各項もその固定対象の商。
方針：像の中では成分同型を合成し、外では零対象への零射を用いる。
規約：同じ固定対象を全ての次数で用いる。
使われ方：Stacks 19.12.2、TT §3 の小さい商の複体族への所属。
-/
lemma exists_epi_to_extended_term (P : C) (hK : ∀ i, ∃ p : P ⟶ K.X i, Epi p) (i' : ι') :
    ∃ p : P ⟶ (K.extend e).X i', Epi p := by
  by_cases hi : ∃ i, e.f i = i'
  · obtain ⟨i, hi⟩ := hi
    obtain ⟨p, hp⟩ := hK i
    have := hp
    exact ⟨p ≫ (K.extendXIso e hi).inv, inferInstance⟩
  · refine ⟨0, ?_⟩
    constructor
    intro Z f g hfg
    exact (K.isZero_extend_X e i' (by simpa using hi)).eq_of_src f g

end SerrePositivity.KST.DerivedGeometry
