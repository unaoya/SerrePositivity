module

public import SerrePositivity.KST.DerivedGeometry.AffineDerivedSingleCounit
public import SerrePositivity.KST.DerivedGeometry.AffineDqcPlusTruncation
public import SerrePositivity.KST.DerivedGeometry.TriangulatedCounitLocus
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful

/-!
概要：有限区間にコホモロジーを持つ実際のアフィン Dqc 対象で導来余単位は同型。
方針：純粋次数の準連接層との比較を基底とし、切断三角で振幅に帰納する。
規約：準連接コホモロジー条件を元の全層導来圏で判定する。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 の本質的全射性。
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
概要：一つの次数に集中する Dqc 対象で導来余単位は同型。
方針：純粋対象を単一層にし、その層の準連接性をコホモロジーの同型で得る。
規約：単一層の準連接性を別の未証明条件にしない。
使われ方：TT §3、Toën §3.2 の有限振幅の帰納の基底。
-/
lemma affineDerivedPlus_counit_pure_isIso
    (K : DerivedCategory.Plus (tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).Modules)
    (hK : (tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).hasQuasicoherentCohomology K.obj)
    (n : ℤ) [K.IsGE n] [K.IsLE n] :
    IsIso ((affineDerivedPlusAdjunction (R := R) H).counit.app K) := by
  let B := tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom
  obtain ⟨M, ⟨e⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE
    (DerivedCategory.Plus.ι.obj K) n
  let eH : (DerivedCategory.homologyFunctor B.Modules n).obj K.obj ≅ M :=
    (DerivedCategory.homologyFunctor B.Modules n).mapIso e ≪≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso B.Modules n).app M
  let F : B.QCoh := ⟨M,
    (SheafOfModules.isQuasicoherent (Scheme.Spec.obj (.op R)).ringCatSheaf).prop_of_iso
      (B.forget.mapIso eH) (hK n)⟩
  let e' : K ≅ (DerivedCategory.Plus.singleFunctor B.Modules n).obj F.obj :=
    ObjectProperty.isoMk _ e
  exact (NatTrans.isIso_app_iff_of_iso (affineDerivedPlusAdjunction (R := R) H).counit e').mpr
    (affineDerivedPlus_counit_single_isIso H F n)

/--
概要：有限コホモロジー区間を持つ Dqc 対象でアフィン導来余単位は同型。
方針：最下次数を切り出し、残りの振幅と三角の余単位の同型判定を使う。
規約：切断での準連接コホモロジーの保存は証明済みの補題を用いる。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 のアフィン本質的全射性。
-/
lemma affineDerivedPlus_counit_amplitude_isIso (d : ℕ) (a : ℤ)
    (K : DerivedCategory.Plus (tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).Modules)
    (hK : (tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).hasQuasicoherentCohomology K.obj)
    [K.IsGE a] [K.IsLE (a + d)] :
    IsIso ((affineDerivedPlusAdjunction (R := R) H).counit.app K) := by
  induction d generalizing a K with
  | zero =>
      have : K.IsLE a := by simpa using (inferInstance : K.IsLE (a + (0 : ℕ)))
      exact affineDerivedPlus_counit_pure_isIso H K hK a
  | succ d ih =>
      let t := DerivedCategory.Plus.TStructure.t
        (C := (tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).Modules)
      let L := (t.truncLE a).obj K
      let U := (t.truncGT a).obj K
      have : L.IsGE a := by dsimp [L, t]; infer_instance
      have : L.IsLE a := by dsimp [L, t]; infer_instance
      have hL := affineDerivedPlus_counit_pure_isIso H L (affineDqcPlus_truncLE H K hK a) a
      have : U.IsGE (a + 1) := by dsimp [U, t]; infer_instance
      have hU : U.IsLE (a + (Nat.succ d : ℕ)) := by
        change t.IsLE ((t.truncGT a).obj K) (a + (Nat.succ d : ℕ))
        infer_instance
      have : U.IsLE ((a + 1) + d) := by
        convert hU using 1 <;> push_cast <;> ring
      have hUi := ih (a + 1) U (affineDqcPlus_truncGT H K hK a)
      have : IsIso ((affineDerivedPlusAdjunction (R := R) H).counit.app
          ((t.triangleLEGT a).obj K).obj₁) := hL
      have : IsIso ((affineDerivedPlusAdjunction (R := R) H).counit.app
          ((t.triangleLEGT a).obj K).obj₃) := hUi
      exact adjunction_counit_triangle_isIso₂ (affineDerivedPlusAdjunction (R := R) H)
        ((t.triangleLEGT a).obj K) (t.triangleLEGT_distinguished a K)

end SerrePositivity.KST.DerivedGeometry
