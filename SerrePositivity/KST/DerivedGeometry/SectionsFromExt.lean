module

public import SerrePositivity.KST.DerivedGeometry.SheafExtLocalVanishing
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
概要：自由層を始域とする Ext 消滅から実際の右導来切断の消滅を導く。
方針：切断 cocycle の Hom 表示と injective 分解の Ext の境界判定を用いる。
規約：比較の存在を未証明のフィールドにしない。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 のアフィン消滅。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits TopologicalSpace Abelian
namespace SerrePositivity.KST.DerivedGeometry
variable {R : Type u} [Ring R] {X : TopCat.{u}}

/--
概要：自由層からの Ext 消滅により injective 分解の切断複体は対応する正次数で完全。
方針：切断 cocycle を Ext の代表にし、零である類の境界表示を切断へ戻す。
規約：選んだ実際の injective 分解について証明する。
使われ方：TT §3、Toën §3.2 の右導来切断の計算。
-/
lemma injectiveSections_exactAt_of_ext_subsingleton
    (F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) (U : Opens X) (n : ℕ)
    (h : Subsingleton (Ext ((freeModuleSheafOnOpen R X).obj U) F (n + 1))) :
    (((sheafModuleSections U).mapHomologicalComplex (.up ℕ)).obj
      (moduleSheafInjectiveResolution F).cocomplex).ExactAt (n + 1) := by
  let I := moduleSheafInjectiveResolution F
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp),
    ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
  intro z
  constructor
  · intro hz
    change (I.cocomplex.d (n + 1) (n + 2)).hom.app (.op U) z = 0 at hz
    let f := (freeModuleSheafOnOpenHomEquiv R X U (I.cocomplex.X (n + 1))).symm z
    have hf : f ≫ I.cocomplex.d (n + 1) (n + 2) = 0 := by
      apply (freeModuleSheafOnOpenHomEquiv R X U (I.cocomplex.X (n + 2))).injective
      rw [freeModuleSheafOnOpenHomEquiv_postcomp, freeModuleSheafOnOpenHomEquiv_zero]
      simpa only [f, Equiv.apply_symm_apply] using hz
    have hzero : I.extMk f (n + 2) rfl hf = 0 := h.elim _ _
    obtain ⟨g, hg⟩ := (I.extMk_eq_zero_iff f (n + 2) rfl hf n rfl).mp hzero
    refine ⟨freeModuleSheafOnOpenHomEquiv R X U (I.cocomplex.X n) g, ?_⟩
    change (I.cocomplex.d n (n + 1)).hom.app (.op U)
      (freeModuleSheafOnOpenHomEquiv R X U (I.cocomplex.X n) g) = z
    rw [← freeModuleSheafOnOpenHomEquiv_postcomp, hg]
    exact (freeModuleSheafOnOpenHomEquiv R X U (I.cocomplex.X (n + 1))).apply_symm_apply z
  · rintro ⟨y, rfl⟩
    exact congrArg (fun k => k.hom.app (.op U) y) (I.cocomplex.d_comp_d n (n + 1) (n + 2))

/--
概要：自由層からの正次数 Ext が零なら、同じ開上の実際の右導来切断は零対象。
方針：injective 分解の切断複体の完全性と分解による右導来切断の比較同型を使う。
規約：固定環の加群層圏における右導来関手の結論。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 の層コホモロジー消滅。
-/
lemma rightDerivedSections_isZero_of_ext_subsingleton
    (F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) (U : Opens X) (n : ℕ)
    (h : Subsingleton (Ext ((freeModuleSheafOnOpen R X).obj U) F (n + 1))) :
    IsZero (((sheafModuleSections U).rightDerived (n + 1)).obj F) := by
  have he := injectiveSections_exactAt_of_ext_subsingleton F U n h
  exact IsZero.of_iso he.isZero_homology (moduleSheafRightDerivedSectionsIso F U n)

end SerrePositivity.KST.DerivedGeometry
