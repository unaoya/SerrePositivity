module

public import SerrePositivity.AlgebraicGeometry.AffineFiniteTypeSubidealOpen
public import SerrePositivity.AlgebraicGeometry.IdealSheafOpenPairGluing

/-!
概要：有限型部分イデアル層を、一つのアフィン開を追加して延長する。
方針：準コンパクトな重なりで元のイデアルと一致するアフィンの有限型部分を選んで貼る。
規約：二つの開埋め込みの準コンパクト性を明示し、Noether 性を仮定しない。
使われ方：Stacks 01PF の有限アフィン被覆による帰納。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u

set_option backward.isDefEq.respectTransparency false in
/-- 元の準コンパクト開への制限を保ち、別のアフィン開上で有限型な部分イデアルを選ぶ。 -/
theorem exists_subideal_extending_to_affine_open
    {W X Y S : Scheme.{u}} [IsAffine Y]
    (a : W ⟶ X) (b : W ⟶ Y) (j : X ⟶ S) (v : Y ⟶ S)
    [IsOpenImmersion j] [QuasiCompact j] [IsOpenImmersion v] [QuasiCompact v]
    (h : IsPullback a b j v)
    (K : S.IdealSheafData) (H : X.IdealSheafData)
    (hHK : H ≤ K.comap j) (hH : IsFiniteTypeIdealSheaf H) :
    ∃ J : S.IdealSheafData, J ≤ K ∧
      IsFiniteTypeIdealSheaf (J.comap v) ∧ J.comap j = H := by
  classical
  letI : IsOpenImmersion a := MorphismProperty.of_isPullback h.flip inferInstance
  letI : IsOpenImmersion b := MorphismProperty.of_isPullback h inferInstance
  letI : QuasiCompact b := MorphismProperty.of_isPullback h inferInstance
  letI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace b
  let E := K ⊓ H.map j
  have hE : E ≤ K := inf_le_left
  have hEj : E.comap j = H := by
    rw [idealSheaf_comap_inf_of_openImmersion, idealSheaf_comap_map_openImmersion]
    exact inf_eq_right.mpr hHK
  have hEq : (E.comap v).comap b = H.comap a := by
    rw [← Scheme.IdealSheafData.comap_comp, ← h.w,
      Scheme.IdealSheafData.comap_comp, hEj]
  have hlocal : IsFiniteTypeIdealSheaf ((E.comap v).comap b.opensRange.ι) := by
    rw [← b.isoOpensRange_inv_comp, Scheme.IdealSheafData.comap_comp, hEq]
    exact (hH.comap_openImmersion a).comap_openImmersion _
  have hbcompact : IsCompact (b.opensRange : Set Y) := by
    change IsCompact (Set.range b)
    exact isCompact_range b.continuous
  obtain ⟨N, hNE, hN, hNrestr⟩ :=
    exists_finiteType_subideal_eq_on_quasiCompact_open_of_isAffine
      (E.comap v) b.opensRange hbcompact hlocal
  have hNb : N.comap b = (E.comap v).comap b := by
    have heq := congrArg (fun I : b.opensRange.toScheme.IdealSheafData ↦
      I.comap b.isoOpensRange.hom) hNrestr
    simpa only [← Scheme.IdealSheafData.comap_comp, b.isoOpensRange_hom_ι,
      Scheme.Hom.isoOpensRange_hom_ι_assoc] using heq
  have hNK : N ≤ K.comap v := hNE.trans (Scheme.IdealSheafData.comap_mono v hE)
  obtain ⟨J, hJK, hJj, hJv⟩ := exists_subideal_gluing_open_pair a b j v h K H N
    hHK hNK (hEq.symm.trans hNb.symm)
  exact ⟨J, hJK, by rwa [hJv], hJj⟩

set_option backward.isDefEq.respectTransparency false in
/-- 有限型部分イデアルを、アフィンな開を一つ追加して延長する。 -/
theorem exists_finiteType_subideal_extending_open_pair
    {W X Y S : Scheme.{u}} [IsAffine Y]
    (a : W ⟶ X) (b : W ⟶ Y) (j : X ⟶ S) (v : Y ⟶ S)
    [IsOpenImmersion j] [QuasiCompact j] [IsOpenImmersion v] [QuasiCompact v]
    (h : IsPullback a b j v)
    (hcover : ∀ s : S, (∃ x, j x = s) ∨ (∃ y, v y = s))
    (K : S.IdealSheafData) (H : X.IdealSheafData)
    (hHK : H ≤ K.comap j) (hH : IsFiniteTypeIdealSheaf H) :
    ∃ J : S.IdealSheafData, J ≤ K ∧ IsFiniteTypeIdealSheaf J ∧ J.comap j = H := by
  classical
  obtain ⟨J, hJK, hJv, hJj⟩ :=
    exists_subideal_extending_to_affine_open a b j v h K H hHK hH
  refine ⟨J, hJK, ?_, hJj⟩
  let Z : Bool → Scheme.{u} := fun t ↦ match t with | false => X | true => Y
  let q : ∀ t, Z t ⟶ S := fun t ↦ match t with | false => j | true => v
  let 𝒰 : S.OpenCover := Scheme.Cover.mkOfCovers Bool Z q (by
    intro s
    rcases hcover s with ⟨x, hx⟩ | ⟨y, hy⟩
    · exact ⟨false, x, hx⟩
    · exact ⟨true, y, hy⟩) (by
      intro t
      cases t <;> infer_instance)
  apply isFiniteTypeIdealSheaf_of_openCover J 𝒰
  intro t
  cases t with
  | false => change IsFiniteTypeIdealSheaf (J.comap j); rwa [hJj]
  | true => exact hJv

end SerrePositivity.AlgebraicGeometry
