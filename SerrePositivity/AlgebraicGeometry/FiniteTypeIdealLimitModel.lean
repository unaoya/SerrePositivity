module

public import SerrePositivity.AlgebraicGeometry.AffineOpenLimitIdealModel
public import SerrePositivity.AlgebraicGeometry.FiniteTypeIdealAffineGeneratorModel
public import SerrePositivity.AlgebraicGeometry.IdealModelRestrictionComparison

/-!
概要：affine な遷移射を持つ qcqs スキームの極限の有限型イデアル層を有限段へ降ろす。
方針：有限アフィン被覆の局所イデアルを同じ段へ戻し、有限型部分イデアルへ同時に含める。
規約：Stacks 0B8W (3)。底変換の忠実平坦性・Noether 性は仮定しない。
使われ方：G1 の閉包絡の模型および G2 の Noether 近似。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u

set_option backward.isDefEq.respectTransparency false in
/-- qcqs スキームの affine 遷移の逆極限上の有限型イデアル層は、有限段に模型を持つ。
Stacks 32.10.3 (3), Tag 0B8W のイデアル層の場合。 -/
theorem exists_finiteType_ideal_model_of_isLimit
    {J : Type u} [SmallCategory J] [IsCofiltered J]
    (D : J ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    (K : c.pt.IdealSheafData) (hK : IsFiniteTypeIdealSheaf K) :
    ∃ (j : J) (L : (D.obj j).IdealSheafData),
      IsFiniteTypeIdealSheaf L ∧ L.comap (c.π.app j) = K := by
  classical
  have (j : J) : IsAffineHom (c.π.app j) := isAffineHom_π_app D c hc j
  obtain ⟨i⟩ := IsCofiltered.nonempty (C := J)
  obtain ⟨s, hs, hscover⟩ :=
    (isCompact_iff_finite_and_eq_biUnion_affineOpens (U := (⊤ : (D.obj i).Opens))).mp
      (by simpa only [TopologicalSpace.Opens.coe_top] using
        (isCompact_univ : IsCompact (Set.univ : Set (D.obj i))))
  letI : Fintype s := hs.fintype
  let U (a : s) : (D.obj i).affineOpens := a.1
  have hU : ⨆ a : s, (U a).1 = ⊤ := by
    simpa only [U, iSup_subtype] using hscover.symm
  let W (a : s) : c.pt.affineOpens :=
    ⟨c.π.app i ⁻¹ᵁ (U a).1, (U a).2.preimage (c.π.app i)⟩
  let H (a : s) : Ideal Γ((W a).1.toScheme, ⊤) :=
    (K.ideal (W a)).map (W a).1.topIso.inv.hom
  have hH (a : s) : (H a).FG := (hK (W a)).map _
  obtain ⟨j, M, hM, hMj⟩ :=
    exists_fg_ideal_family_model_of_affineOpen_limit D c hc i U H hH
  let V (a : s) : (D.obj j.left).affineOpens :=
    ⟨D.map j.hom ⁻¹ᵁ (U a).1, (U a).2.preimage (D.map j.hom)⟩
  let N (a : s) : Ideal Γ(D.obj j.left, (V a).1) :=
    (M a).map (V a).1.topIso.hom.hom
  have hN (a : s) : (N a).FG := (hM a).map _
  have hgen (a : s) : (N a).map ((c.π.app j.left).app (V a).1).hom =
      K.ideal ⟨c.π.app j.left ⁻¹ᵁ (V a).1, (V a).2.preimage (c.π.app j.left)⟩ := by
    have e : (W a).1 = c.π.app j.left ⁻¹ᵁ (V a).1 := by
      dsimp only [W, V]
      rw [← Scheme.Hom.comp_preimage, c.w]
    apply ideal_model_appLE_of_eq_preimage (c.π.app j.left) (V a) (W a) e (N a) K
    apply ideal_model_resLE_top_comparison (c.π.app j.left) (V a).1 (W a).1 e.le (M a)
    exact hMj a
  have hV : ⨆ a : s, (V a).1 = ⊤ := (D.map j.hom).iSup_preimage_eq_top hU
  obtain ⟨L, hL, heq⟩ :=
    exists_finiteType_ideal_model_of_affine_ideal_models (c.π.app j.left) K V hV N hN hgen
  exact ⟨j.left, L, hL, heq⟩

end SerrePositivity.AlgebraicGeometry
