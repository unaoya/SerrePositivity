module

public import SerrePositivity.AlgebraicGeometry.FiniteTypeIdealSheafCover

/-!
概要：開被覆への逆像から有限型イデアル層を判定する。
方針：被覆の既存のアフィン細分を取り、切断環の同型で有限生成性を戻す。
規約：被覆の添字集合の有限性は不要。
使われ方：Stacks 01PF の延長を二つの開集合から貼る。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory
universe u

set_option backward.isDefEq.respectTransparency false in
/-- 開埋め込みの逆像の切断イデアルの有限生成性を、像のアフィン開へ戻す。 -/
theorem fg_ideal_image_of_comap_openImmersion
    {X Y : Scheme.{u}} (K : Y.IdealSheafData) (j : X ⟶ Y)
    [IsOpenImmersion j] (U : X.affineOpens)
    (h : ((K.comap j).ideal U).FG) :
    (K.ideal ⟨j ''ᵁ U, U.2.image_of_isOpenImmersion j⟩).FG := by
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion] at h
  have hmap := h.map (j.appIso U).inv.hom
  rw [Ideal.map_comap_of_surjective _
    (ConcreteCategory.bijective_of_isIso (j.appIso U).inv).2] at hmap
  exact hmap

set_option backward.isDefEq.respectTransparency false in
/-- 開被覆への逆像がすべて有限型なら、大域のイデアル層も有限型。 -/
theorem isFiniteTypeIdealSheaf_of_openCover
    {X : Scheme.{u}} (K : X.IdealSheafData) (𝒰 : X.OpenCover)
    (hK : ∀ i, IsFiniteTypeIdealSheaf (K.comap (𝒰.f i))) : IsFiniteTypeIdealSheaf K := by
  let A := Σ i : 𝒰.I₀, (𝒰.X i).affineOpens
  let V (a : A) : X.affineOpens :=
    ⟨𝒰.f a.1 ''ᵁ a.2.1, a.2.2.image_of_isOpenImmersion (𝒰.f a.1)⟩
  have hcover : ⨆ a, (V a).1 = ⊤ := by
    apply top_unique
    intro x hx
    obtain ⟨i, y, rfl⟩ := 𝒰.exists_eq x
    have hy : y ∈ ⨆ W : (𝒰.X i).affineOpens, W.1 := by
      rw [iSup_affineOpens_eq_top]
      trivial
    obtain ⟨W, hyW⟩ := TopologicalSpace.Opens.mem_iSup.mp hy
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨i, W⟩, y, hyW, rfl⟩
  apply isFiniteTypeIdealSheaf_of_affineCover K V hcover
  intro a
  exact fg_ideal_image_of_comap_openImmersion K (𝒰.f a.1) a.2 (hK a.1 a.2)

end SerrePositivity.AlgebraicGeometry
