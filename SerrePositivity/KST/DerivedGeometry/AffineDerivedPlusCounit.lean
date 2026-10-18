module

public import SerrePositivity.KST.DerivedGeometry.AffineDerivedBoundedCounit

/-!
概要：下に有界なアフィン Dqc の全対象で実際の導来余単位は同型。
方針：各固定次数で上側切断の有限区間の余単位へ帰着し、高い下限を右導来と tilde が保つ。
規約：非有界下側への拡張とは区別する。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 の bounded below 本質的全射性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory AlgebraicGeometry
namespace SerrePositivity.KST.DerivedGeometry
variable {R : CommRingCat.{u}} (H : Type u) [Ring H] [Algebra R H]
  [HasDerivedCategory (ModuleCat.{u} H)]
  [HasDerivedCategory (tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).Modules]

/--
概要：実際の bounded below Dqc の全対象でアフィン導来余単位は同型。
方針：上側切断の比較を各コホモロジー次数で使い、自然性の可換正方形で結論する。
規約：対象の準連接コホモロジーだけを入力する。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 のアフィン同値の本質的全射性。
-/
lemma affineDerivedPlus_counit_isIso
    (K : DerivedCategory.Plus (tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).Modules)
    (hK : (tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).hasQuasicoherentCohomology K.obj) :
    IsIso ((affineDerivedPlusAdjunction (R := R) H).counit.app K) := by
  obtain ⟨a, ha⟩ := K.property
  have : K.IsGE a := (DerivedCategory.Plus.isGE_ι_obj_iff K a).mp ha
  let B := tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom
  let t := DerivedCategory.Plus.TStructure.t (C := B.Modules)
  let F := affineDerivedTildePlus (R := R) H
  let G := affineDerivedΓPlus (R := R) H
  let adj := affineDerivedPlusAdjunction (R := R) H
  apply (DerivedCategory.Plus.isIso_iff _).mpr
  intro n
  let d := (n - a).toNat
  let b : ℤ := a + d
  have hnb : n ≤ b := by dsimp [b, d]; omega
  let T := (t.triangleLEGT b).obj K
  have hT := t.triangleLEGT_distinguished b K
  have hLge : T.obj₁.IsGE a := by change t.IsGE ((t.truncLE b).obj K) a; infer_instance
  have hLle : T.obj₁.IsLE (a + d) := by
    change t.IsLE ((t.truncLE b).obj K) b
    infer_instance
  have hε : IsIso (adj.counit.app T.obj₁) :=
    affineDerivedPlus_counit_amplitude_isIso H d a T.obj₁ (affineDqcPlus_truncLE H K hK b)
  have hUge : T.obj₃.IsGE (b + 1) := by
    change t.IsGE ((t.truncGT b).obj K) (b + 1)
    infer_instance
  have : T.obj₃.IsGE (n + 1) := t.isGE_of_ge _ _ (b + 1) (by omega)
  have hf : IsIso ((DerivedCategory.Plus.homologyFunctor _ n).map T.mor₁) :=
    plusTriangle_homology_mor₁_isIso T hT n
  have hGU : (G.obj T.obj₃).IsGE (b + 1) :=
    rightDerivedPlus_isGE (affineCoefficientΓ (R := R) H) T.obj₃ (b + 1)
  have hFGU : ((G ⋙ F).obj T.obj₃).IsGE (b + 1) := by
    apply (DerivedCategory.Plus.isGE_ι_obj_iff _ (b + 1)).mp
    exact exactDerived_isGE (affineCoefficientTildeFunctor (R := R) H)
      (G.obj T.obj₃).obj (b + 1) ((DerivedCategory.Plus.isGE_ι_obj_iff _ _).mpr hGU)
  have : ((G ⋙ F).mapTriangle.obj T).obj₃.IsGE (n + 1) :=
    t.isGE_of_ge ((G ⋙ F).obj T.obj₃) (n + 1) (b + 1) (by omega)
  have hFf : IsIso ((DerivedCategory.Plus.homologyFunctor _ n).map ((G ⋙ F).map T.mor₁)) :=
    plusTriangle_homology_mor₁_isIso ((G ⋙ F).mapTriangle.obj T)
      ((G ⋙ F).map_distinguished T hT) n
  have h := congrArg ((DerivedCategory.Plus.homologyFunctor _ n).map)
    (adj.counit.naturality T.mor₁)
  simp only [Functor.map_comp, Functor.id_map] at h
  have : IsIso ((DerivedCategory.Plus.homologyFunctor _ n).map ((G ⋙ F).map T.mor₁) ≫
      (DerivedCategory.Plus.homologyFunctor _ n).map (adj.counit.app T.obj₂)) := by
    rw [h]
    infer_instance
  exact (isIso_comp_left_iff ((DerivedCategory.Plus.homologyFunctor _ n).map ((G ⋙ F).map T.mor₁))
    ((DerivedCategory.Plus.homologyFunctor _ n).map (adj.counit.app T.obj₂))).mp this

end SerrePositivity.KST.DerivedGeometry
