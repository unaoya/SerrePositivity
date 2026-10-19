module

public import SerrePositivity.KST.DerivedGeometry.LargerAcyclicSubobject

/-!
概要：非輪状部分対象を拡大する包含の余核は、小さい試験対象または零となる。
方針：拡大関数の選択した存在証明と、等しい部分対象への包含の余核同型を使う。
規約：全体に到達した後の余核は零として扱う。
使われ方：Stacks Lemma 19.12.3、TT §3・§8、Toën §3.2 の超限列の後続商。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe w u
open CategoryTheory Limits
namespace SerrePositivity.KST.DerivedGeometry

/--
概要：等しい終域部分対象への包含の余核を比較する。
方針：部分対象の等式を除去し、証明の無関係性で恒等同型へ帰着する。
規約：包含の不等式の証明の選択に依存しない。
使われ方：Stacks 19.12.3、TT §3 の選択した後続商の比較。
-/
def subobjectInclusionCokernelIsoOfEq {D : Type*} [Category* D] [Abelian D]
    {X : D} (S B B' : Subobject X) (h : B = B') (hSB : S ≤ B) (hSB' : S ≤ B') :
    cokernel (Subobject.ofLE S B hSB) ≅ cokernel (Subobject.ofLE S B' hSB') := by
  subst B'
  exact Iso.refl _

variable {C : Type u} [Category.{w} C] [Abelian C] [IsGrothendieckAbelian.{w} C]

/--
概要：非輪状部分対象の選んだ拡大の余核は、零または固定した小さい試験対象と同型。
方針：真の部分対象では存在証明の商同型、全体では恒等包含の零余核を使う。
規約：余核は元の複体の圏で取る。
使われ方：Stacks 19.12.3、TT §3 の零ホモトピー直交性の後続商への移送。
-/
lemma largerAcyclicSubobject_cokernel (G : C) (hG : IsSeparator G)
    (M : CochainComplex C ℤ) (hM : M.Acyclic) (S : Subobject M)
    (hS : (S : CochainComplex C ℤ).Acyclic) :
    IsZero (cokernel (Subobject.ofLE S (largerAcyclicSubobject G hG M hM S)
      (le_largerAcyclicSubobject G hG M hM S))) ∨
    ∃ s : SmallAcyclicTestIndex G, Nonempty (cokernel
      (Subobject.ofLE S (largerAcyclicSubobject G hG M hM S)
        (le_largerAcyclicSubobject G hG M hM S)) ≅ smallAcyclicTestFamily G s) := by
  classical
  by_cases hne : S = ⊤
  · subst S
    apply Or.inl
    let E := subobjectInclusionCokernelIsoOfEq (⊤ : Subobject M) _ ⊤
      (largerAcyclicSubobject_top G hG M hM) (le_largerAcyclicSubobject G hG M hM ⊤) le_rfl
    have : Epi (Subobject.ofLE (⊤ : Subobject M) ⊤ le_rfl) := by
      rw [Subobject.ofLE_refl]
      infer_instance
    exact (isZero_cokernel_of_epi _).of_iso E
  · let h := exists_larger_acyclic_subobject G hG M hM S hS hne
    have hh : largerAcyclicSubobject G hG M hM S = h.choose := by
      rw [largerAcyclicSubobject, dite_eq_right hne, dite_eq_left hS]
    let E := subobjectInclusionCokernelIsoOfEq S _ h.choose hh
      (le_largerAcyclicSubobject G hG M hM S) h.choose_spec.choose.le
    obtain ⟨s, hs⟩ := h.choose_spec.choose_spec
    exact Or.inr ⟨s, ⟨E ≪≫ hs.2.some⟩⟩

end SerrePositivity.KST.DerivedGeometry
