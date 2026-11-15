module

public import SerrePositivity.AlgebraicGeometry.FiniteTypeIdealSheaf
public import Mathlib.RingTheory.Localization.Finiteness
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-!
概要：有限型イデアル層のアフィン開被覆による判定と開への制限。
方針：交叉の基本開細分と、既存の局所化による有限生成性の判定を使う。
規約：被覆の有限性と Noether 性は要求しない。
使われ方：Stacks 01PF の有限型部分イデアルの延長・貼り合わせ。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory
universe u v

set_option backward.isDefEq.respectTransparency false in
/-- アフィン開被覆上の切断イデアルが有限生成なら、イデアル層は有限型。 -/
theorem isFiniteTypeIdealSheaf_of_affineCover
    {X : Scheme.{u}} (K : X.IdealSheafData) {ι : Type v}
    (U : ι → X.affineOpens) (hU : ⨆ i, (U i).1 = ⊤)
    (hK : ∀ i, (K.ideal (U i)).FG) : IsFiniteTypeIdealSheaf K := by
  classical
  intro V
  have hloc : ∀ x : V.1, ∃ (i : ι) (r : Γ(X, V.1)) (rU : Γ(X, U i)),
      X.basicOpen r = X.basicOpen rU ∧ x.1 ∈ X.basicOpen r := by
    intro ⟨x, hxV⟩
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (hU.ge (Set.mem_univ x))
    exact ⟨i, exists_basicOpen_le_affine_inter V.2 (U i).2 _ ⟨hxV, hi⟩⟩
  choose i r rU e hxr using hloc
  have hspan : Ideal.span (Set.range r) = ⊤ := by
    rw [← V.2.self_le_iSup_basicOpen_iff]
    exact fun x hxV ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨_, _, rfl⟩, hxr ⟨x, hxV⟩⟩
  have inst := V.2.isLocalization_basicOpen
  apply Submodule.of_localizationSpan' (N := K.ideal V) (Set.range r) hspan
    (Rₚ := fun g ↦ Γ(X, X.basicOpen g.1))
    (fun g ↦ Algebra.linearMap Γ(X, V.1) Γ(X, X.basicOpen g.1))
  rintro ⟨_, j, rfl⟩
  simp only [Ideal.localized'_eq_map, RingHom.algebraMap_toAlgebra]
  erw [K.map_ideal (U := ⟨_, V.2.basicOpen _⟩) (X.basicOpen_le (r j))]
  rw! [e]
  rw [← K.map_ideal (V := U (i j)) (X.basicOpen_le (rU j))]
  exact (hK (i j)).map _

set_option backward.isDefEq.respectTransparency false in
/-- 開埋め込みへの逆像は有限型イデアル層を保つ。 -/
theorem IsFiniteTypeIdealSheaf.comap_openImmersion
    {X Y : Scheme.{u}} {K : Y.IdealSheafData}
    (hK : IsFiniteTypeIdealSheaf K) (j : X ⟶ Y) [IsOpenImmersion j] :
    IsFiniteTypeIdealSheaf (K.comap j) := by
  intro U
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]
  let e := (j.appIso U).commRingCatIsoToRingEquiv
  change ((K.ideal ⟨j ''ᵁ U, U.2.image_of_isOpenImmersion j⟩).comap e.symm).FG
  rw [Ideal.comap_symm]
  exact (hK _).map _

end SerrePositivity.AlgebraicGeometry
