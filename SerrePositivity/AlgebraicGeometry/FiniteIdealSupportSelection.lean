module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic

/-!
概要：イデアル層の支持を指定した開集合に収めるための有限個の切断を選ぶ。
方針：支持の外の基本開で開集合の閉補集合を覆い、コンパクト性を使う。
規約：選ぶ切断は元のイデアル層の切断であり、有限型性を先には仮定しない。
使われ方：Stacks 01PF・01PG による有限表示閉包絡の支持の制御。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry
universe u

/-- 支持を開集合へ収める条件を、アフィン切断の有限個の所属条件へ帰着する。 -/
theorem exists_finite_affine_sections_support_subset
    {X : Scheme.{u}} [CompactSpace X] (K : X.IdealSheafData) (V : X.Opens)
    (hKV : (K.support : Set X) ⊆ V) :
    ∃ t : Finset (Σ U : X.affineOpens, K.ideal U),
      ∀ J : X.IdealSheafData,
        (∀ a ∈ t, (a.2 : Γ(X, a.1.1)) ∈ J.ideal a.1) →
        (J.support : Set X) ⊆ V := by
  classical
  let D (a : Σ U : X.affineOpens, K.ideal U) : Set X := X.basicOpen (a.2 : Γ(X, a.1.1))
  have hcover : (V : Set X)ᶜ ⊆ ⋃ a, D a := by
    intro x hx
    have hxK : x ∉ K.support := fun h ↦ hx (hKV h)
    simp only [Scheme.IdealSheafData.mem_support_iff, Scheme.mem_zeroLocus_iff] at hxK
    push Not at hxK
    obtain ⟨U, f, hf, hxf⟩ := hxK
    exact Set.mem_iUnion.mpr ⟨⟨U, ⟨f, hf⟩⟩, hxf⟩
  obtain ⟨t, ht⟩ := V.isOpen.isClosed_compl.isCompact.elim_finite_subcover D
    (fun a ↦ (X.basicOpen (a.2 : Γ(X, a.1.1))).isOpen) hcover
  refine ⟨t, ?_⟩
  intro J hJ x hxJ
  by_contra hxV
  obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.mp (ht hxV)
  have hz : x ∈ X.zeroLocus (U := a.1.1) (J.ideal a.1) :=
    J.supportSet_subset_zeroLocus a.1 hxJ
  exact (X.mem_zeroLocus_iff _ _).mp hz a.2 (hJ a ha) hxa

end SerrePositivity.AlgebraicGeometry
