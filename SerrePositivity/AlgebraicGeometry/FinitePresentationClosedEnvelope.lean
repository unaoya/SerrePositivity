module

public import SerrePositivity.AlgebraicGeometry.FiniteTypeIdealApproximation
public import SerrePositivity.AlgebraicGeometry.FiniteIdealSupportSelection
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
概要：指定閉部分スキームを含み指定開に入る有限表示の閉包絡を作る。
方針：支持条件の有限選択、有限型部分イデアルの延長、有限型閉包含の有限表示性をつなぐ。
規約：Stacks 01PF・01PG・01TV。固有射の型は射影的な場合に制限しない。
使われ方：Rydh 3.10 の非 Noether 基底の fppf–proper 細分。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry
universe u

/-- qcqs スキーム上で、指定閉部分スキームを含み指定開に入る有限表示閉包絡が存在する。 -/
theorem exists_finitePresentation_closedEnvelope
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (K : X.IdealSheafData) (V : X.Opens) (hKV : (K.support : Set X) ⊆ V) :
    ∃ J : X.IdealSheafData, J ≤ K ∧ LocallyOfFinitePresentation J.subschemeι ∧
      (J.support : Set X) ⊆ V := by
  classical
  obtain ⟨t, ht⟩ := exists_finite_affine_sections_support_subset K V hKV
  let U (a : t) : X.affineOpens := a.1.1
  let s (a : t) : Finset Γ(X, (U a).1) := {(a.1.2 : Γ(X, (U a).1))}
  have hs : ∀ a x, x ∈ s a → x ∈ K.ideal (U a) := by
    intro a x hx
    rcases Finset.mem_singleton.mp (show x ∈ {(a.1.2 : Γ(X, (U a).1))} from hx) with rfl
    exact a.1.2.2
  obtain ⟨J, hJK, hJ, hcontains⟩ :=
    exists_finiteType_subideal_containing_affine_sections K U s hs
  refine ⟨J, hJK, locallyOfFinitePresentation_subschemeι_of_finiteType J hJ, ht J ?_⟩
  intro a ha
  exact hcontains ⟨a, ha⟩ a.2 (by simp [s])

/-- 一般の固有・局所有限表示射の始域上での有限表示閉包絡（C02）。 -/
theorem exists_finitePresentation_closedEnvelope_of_proper
    {R : CommRingCat.{u}} {Y : Scheme.{u}} (p : Y ⟶ Spec R)
    [IsProper p] [LocallyOfFinitePresentation p]
    (K : Y.IdealSheafData) (V : Y.Opens) (hKV : (K.support : Set Y) ⊆ V) :
    ∃ J : Y.IdealSheafData, J ≤ K ∧ LocallyOfFinitePresentation J.subschemeι ∧
      (J.support : Set Y) ⊆ V := by
  letI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace p
  letI : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated p
  exact exists_finitePresentation_closedEnvelope K V hKV

end SerrePositivity.AlgebraicGeometry
