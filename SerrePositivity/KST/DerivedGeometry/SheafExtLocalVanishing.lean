module

public import SerrePositivity.KST.DerivedGeometry.OpenSheafHom
public import Mathlib.CategoryTheory.Abelian.Injective.Ext
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives

/-!
概要：開上の自由層を始域とする正次数 Ext 類の局所消滅。
方針：実際の injective 分解で類を表し、層の完全性による局所境界へ還元する。
規約：Ext と右導来切断の未証明の同一視は用いない。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 のアフィン消滅への入力。
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
概要：固定環の加群層の Ext は Hom と同じ宇宙で存在する。
方針：Grothendieck 性からの十分な injective と局所小性を使う。
規約：存在を構造体の未証明フィールドにしない。
使われ方：TT §3、Toën §3.2 の自由層を始域とする Ext。
-/
instance moduleSheaf_hasExt :
    HasExt.{u} (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) :=
  hasExt_of_enoughInjectives _

/--
概要：開上の自由層からの正次数 Ext の類は各点の近傍へ制限すると零。
方針：injective 分解の cocycle の切断表示を局所境界へ直し、Ext の境界判定を使う。
規約：係数環の可換性も平坦性も要求しない。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 の有限被覆の局所消滅。
-/
lemma moduleSheafExt_locallyZero
    (F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) (n : ℕ) (U : Opens X)
    (α : Ext ((freeModuleSheafOnOpen R X).obj U) F (n + 1)) (x : X) (hx : x ∈ U) :
    ∃ (V : Opens X) (hVU : V ≤ U), x ∈ V ∧
      (Ext.mk₀ ((freeModuleSheafOnOpen R X).map (homOfLE hVU))).comp α
        (zero_add (n + 1)) = 0 := by
  let I := moduleSheafInjectiveResolution F
  obtain ⟨f, hf, rfl⟩ := I.extMk_surjective α (n + 2) rfl
  let z := freeModuleSheafOnOpenHomEquiv R X U (I.cocomplex.X (n + 1)) f
  have hz : (I.cocomplex.d (n + 1) (n + 2)).hom.app (.op U) z = 0 := by
    rw [← freeModuleSheafOnOpenHomEquiv_postcomp, hf, freeModuleSheafOnOpenHomEquiv_zero]
  have he := (HomologicalComplex.exactAt_iff' I.cocomplex n (n + 1) (n + 2)
    (by simp) (by simp)).mp (I.cocomplex_exactAt_succ n)
  obtain ⟨V, hVU, ⟨y, hy⟩, hxV⟩ := sheafExact_localCocycleBoundary
    (I.cocomplex.sc' n (n + 1) (n + 2)) he U z hz x hx
  refine ⟨V, hVU, hxV, ?_⟩
  rw [I.mk₀_comp_extMk]
  apply (I.extMk_eq_zero_iff _ _ _ _ n rfl).mpr
  refine ⟨(freeModuleSheafOnOpenHomEquiv R X V (I.cocomplex.X n)).symm y, ?_⟩
  apply (freeModuleSheafOnOpenHomEquiv R X V (I.cocomplex.X (n + 1))).injective
  rw [freeModuleSheafOnOpenHomEquiv_postcomp, Equiv.apply_symm_apply,
    freeModuleSheafOnOpenHomEquiv_naturality]
  exact hy

/--
概要：開上の自由層を始域とする Ext を開に反変な前層へ束ねる。
方針：実際の自由層関手と Ext の反変関手を合成し標的で評価する。
規約：制限は自由層の包含への Ext の前合成。
使われ方：TT §3・§8、Toën §3.2 の有限基本開での局所消滅。
-/
def openSheafExtPresheaf
    (F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) (n : ℕ) :
    (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  { obj U := AddCommGrpCat.of (Ext ((freeModuleSheafOnOpen R X).obj U.unop) F n)
    map f := AddCommGrpCat.ofHom
      ((Ext.mk₀ ((freeModuleSheafOnOpen R X).map f.unop)).precomp F (zero_add n))
    map_id U := by
      ext α
      simp
    map_comp f g := by
      ext α
      simp [Ext.comp_assoc_of_second_deg_zero] }


end SerrePositivity.KST.DerivedGeometry
