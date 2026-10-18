module

public import SerrePositivity.KST.DerivedGeometry.RingedExtLocalVanishing
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
概要：実際の環層加群層圏の Ext 消滅から右導来切断の消滅を導く。
方針：元の環層上の injective 分解と自由開加群の Hom 表示で cocycle と境界を比較する。
規約：固定環への忘却による injective の保存を仮定しない。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 の係数アフィン消滅。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits TopologicalSpace Abelian
namespace SerrePositivity.KST.DerivedGeometry
variable (X : TopCat.{u}) (B : Sheaf (Opens.grothendieckTopology X) RingCat.{u})

/--
概要：環層上の加群層の固定した開の切断をその開の係数環の加群として取る関手。
方針：加群前層への忘却と評価を合成する。
規約：係数環は実際の B(U)。
使われ方：TT §3、Toën §3.2 の係数右導来切断。
-/
def ringedModuleSections (U : Opens X) : SheafOfModules.{u} B ⥤ ModuleCat.{u} (B.obj.obj (.op U)) :=
  SheafOfModules.forget B ⋙ PresheafOfModules.evaluation B.obj (.op U)

/-- 概要：環層上の切断は加法的。方針：忘却と評価の加法性を合成する。
規約：右完全性は要求しない。使われ方：TT §3、Toën §3.2 の右導来関手。 -/
instance ringedModuleSections_additive (U : Opens X) : (ringedModuleSections X B U).Additive :=
  inferInstanceAs (SheafOfModules.forget B ⋙ PresheafOfModules.evaluation B.obj (.op U)).Additive

/-- 概要：環層上の切断は有限極限を保つ。方針：忘却と評価の極限保存を合成する。
規約：切断の右完全性は仮定しない。使われ方：TT §3、Toën §3.2 のサイクル。 -/
instance ringedModuleSections_preservesFiniteLimits (U : Opens X) :
    PreservesFiniteLimits (ringedModuleSections X B U) := by
  dsimp [ringedModuleSections]
  infer_instance

/--
概要：自由開加群からの Ext 消滅により実際の環層上の injective 分解の切断複体は完全。
方針：切断 cocycle を Ext の代表へ移し、零の類の境界表示を切断へ戻す。
規約：元の環層の加群圏で構成した分解を使う。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 の係数右導来切断の消滅。
-/
lemma ringedInjectiveSections_exactAt_of_ext_subsingleton (F : SheafOfModules.{u} B)
    (U : Opens X) (n : ℕ)
    (h : Subsingleton (Ext ((ringedFreeSheafOnOpen X B).obj U) F (n + 1))) :
    (((ringedModuleSections X B U).mapHomologicalComplex (.up ℕ)).obj
      (ringedInjectiveResolution X B F).cocomplex).ExactAt (n + 1) := by
  let I := ringedInjectiveResolution X B F
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp),
    ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
  intro z
  constructor
  · intro hz
    change (I.cocomplex.d (n + 1) (n + 2)).val.app (.op U) z = 0 at hz
    let f := (ringedFreeSheafOnOpenHomEquiv X B U (I.cocomplex.X (n + 1))).symm z
    have hf : f ≫ I.cocomplex.d (n + 1) (n + 2) = 0 := by
      apply (ringedFreeSheafOnOpenHomEquiv X B U (I.cocomplex.X (n + 2))).injective
      rw [ringedFreeSheafHomEquiv_postcomp, ringedFreeSheafHomEquiv_zero]
      simpa only [f, Equiv.apply_symm_apply] using hz
    have hzero : I.extMk f (n + 2) rfl hf = 0 := h.elim _ _
    obtain ⟨g, hg⟩ := (I.extMk_eq_zero_iff f (n + 2) rfl hf n rfl).mp hzero
    refine ⟨ringedFreeSheafOnOpenHomEquiv X B U (I.cocomplex.X n) g, ?_⟩
    change (I.cocomplex.d n (n + 1)).val.app (.op U)
      (ringedFreeSheafOnOpenHomEquiv X B U (I.cocomplex.X n) g) = z
    rw [← ringedFreeSheafHomEquiv_postcomp, hg]
    exact (ringedFreeSheafOnOpenHomEquiv X B U (I.cocomplex.X (n + 1))).apply_symm_apply z
  · rintro ⟨y, rfl⟩
    exact congrArg (fun k => k.val.app (.op U) y) (I.cocomplex.d_comp_d n (n + 1) (n + 2))

/--
概要：実際の環層加群層圏の自由開加群からの Ext 消滅は右導来切断の零を与える。
方針：分解の切断複体の完全性を右導来関手と分解コホモロジーの比較で移す。
規約：結論は元の環層上の右導来関手についての主張。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 の係数アフィン消滅。
-/
lemma ringedRightDerivedSections_isZero_of_ext_subsingleton (F : SheafOfModules.{u} B)
    (U : Opens X) (n : ℕ)
    (h : Subsingleton (Ext ((ringedFreeSheafOnOpen X B).obj U) F (n + 1))) :
    IsZero (((ringedModuleSections X B U).rightDerived (n + 1)).obj F) := by
  have he := ringedInjectiveSections_exactAt_of_ext_subsingleton X B F U n h
  exact IsZero.of_iso he.isZero_homology
    ((ringedInjectiveResolution X B F).isoRightDerivedObj (ringedModuleSections X B U) (n + 1))

end SerrePositivity.KST.DerivedGeometry
