module
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Homology.ComplexShape
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.EssentialImage
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.HomCongr
public import Mathlib.CategoryTheory.Iso
public import Mathlib.CategoryTheory.NatIso
public import Mathlib.CategoryTheory.NatTrans
public import Mathlib.CategoryTheory.Preadditive.Basic
public import Mathlib.Combinatorics.Quiver.Basic
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Function.Basic
public import Mathlib.Logic.Function.Defs
public import SerrePositivity.HomologicalAlgebra.Complex.Basic
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.BoundedAboveCompletion
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ComplexCompletion.Basic
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ComplexCompletion.Reconstruction
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Koszul.Complete
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModuleComplete.Basic
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PDCompletion
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Pair.Iteration
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Pair.Koszul
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Reflection
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Tower.HolimModel

/-!
# 二つの主元完備化の H⁰ と PD 完備化の比較

概要：一般の構成とその比較をまとめる。
方針：元の型・本体・局所的な文脈を、機械的な名前の追従だけで保存する。
規約：特殊な包絡の存在や追加の仮定を導入しない。
使われ方：Bhatt–Scholze の包絡または perfectoid 化の比較。
-/

universe u

/-! ## BSの二つの実主元完備化H0と実PD H0の共有反射比較 -/

@[expose] public noncomputable section IteratedPDH0Reflection

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.SerrePositivity.DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R] (f d : R)
local notation "M" => CategoryTheory.Functor.obj
  (DerivedCategory.singleFunctor (ModuleCat R) 0) (ModuleCat.of R R)
local notation "Y" => CategoryTheory.Functor.obj (derivedComplexCompletionFunctor R f) M

/-- BSで使う元のp,d逐次実完備化対象。 -/
abbrev _root_.SerrePositivity.DerivedCompletion.IteratedPDCompletionObject := (derivedComplexCompletionFunctor R d).obj Y

local notation "Z" => _root_.SerrePositivity.DerivedCompletion.IteratedPDCompletionObject R f d
local notation "H" => CategoryTheory.Functor.obj (DerivedCategory.homologyFunctor (ModuleCat R) 0)
local notation "U" => CategoryTheory.NatTrans.app (derivedComplexCompletionUnit R f) M ≫
  CategoryTheory.NatTrans.app (derivedComplexCompletionUnit R d) Y

/-- raw自身の実逐次完備化から誘導される、元のRaw線形標準単位。 -/
def _root_.SerrePositivity.DerivedCompletion.iteratedPDH0Unit : R →ₗ[R] H Z :=
  (((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) 0).inv.app
    (ModuleCat.of R R)) ≫ (DerivedCategory.homologyFunctor (ModuleCat R) 0).map U).hom

/-- raw自身の実逐次対象は、二つ目の完備化後にも最初の座標について完備。 -/
theorem _root_.SerrePositivity.DerivedCompletion.iteratedPDCompletion_isComplete_first : IsComplete R f Z := by
  have hY : IsComplete R f Y := derivedComplexCompletionFunctor_isComplete R f M
  let K := DerivedCategory.Q.objPreimage Y
  let eK : DerivedCategory.Q.obj K ≅ Y := DerivedCategory.Q.objObjPreimageIso Y
  have hK := isComplete_of_iso R f eK.symm hY
  have hstage (n : ℕ) : IsComplete R f
      (DerivedCategory.Q.obj (complexPowerKoszulStage R d K n)) :=
    isComplete_Q_mappingCone R f (_root_.SerrePositivity.smulId (d ^ n) K) hK hK
  have hC := isComplete_complexTowerHomotopyLimitObject_of_stages R f
    (complexPowerKoszulStage R d K) (complexPowerKoszulTransition R d K) hstage
  let e : complexCompletionObject R d K ≅ Z :=
    (derivedComplexCompletionComparison R d).symm.app K ≪≫
      (derivedComplexCompletionFunctor R d).mapIso eK
  exact isComplete_of_iso R f e hC

/-- raw自身の実逐次H0は両座標について導来完備。 -/
theorem _root_.SerrePositivity.DerivedCompletion.iteratedPDH0_isComplete :
    ∀ j : Fin 2, IsModuleComplete R (pairKoszulCoordinates R f d j) (H Z) := by
  intro j
  fin_cases j
  · exact isComplete_homology_isModuleComplete R f Z
      (_root_.SerrePositivity.DerivedCompletion.iteratedPDCompletion_isComplete_first R f d) 0
  · exact derivedComplexCompletionFunctor_homology_isModuleComplete R d Y 0

/-- 同じ標準単位は、両座標について完備な加群への写像を一意に決定する。 -/
theorem _root_.SerrePositivity.DerivedCompletion.iteratedPDH0_isCompleteModuleReflection :
    IsCompleteModuleReflection R (pairKoszulCoordinates R f d) (H Z)
      (_root_.SerrePositivity.DerivedCompletion.iteratedPDH0Unit R f d 1) where
  isComplete := _root_.SerrePositivity.DerivedCompletion.iteratedPDH0_isComplete R f d
  universal N hN := by
    have hp : IsModuleComplete R f N := by simpa [pairKoszulCoordinates] using hN 0
    have hd : IsModuleComplete R d N := by
      simpa only [pairKoszulCoordinates, Fin.snoc_last] using hN (Fin.last 1)
    have hM : (M).IsLE 0 := inferInstance
    let := hM
    let := derivedComplexCompletionFunctor_isLE R f M 0 hM
    let eqv := ModuleCat.homEquiv.symm |>.trans
      (completionH0HomEquiv R d Y N hd) |>.trans
      (completionH0HomEquiv R f M N hp) |>.trans
      (Iso.homCongr
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) 0).app
          (ModuleCat.of R R)) (Iso.refl N)) |>.trans
      ModuleCat.homEquiv |>.trans (LinearMap.ringLmapEquivSelf R R N).toEquiv
    have he (g : H Z →ₗ[R] N) : eqv g = g (_root_.SerrePositivity.DerivedCompletion.iteratedPDH0Unit R f d 1) := by
      simp only [eqv, Equiv.trans_apply, completionH0HomEquiv_apply,
        Iso.homCongr_apply, Iso.refl_hom, Category.comp_id]
      simp only [_root_.SerrePositivity.DerivedCompletion.iteratedPDH0Unit, Functor.map_comp]
      rfl
    have hf : (eqv : _ → _) = (fun g => g (_root_.SerrePositivity.DerivedCompletion.iteratedPDH0Unit R f d 1)) := funext he
    rw [← hf]
    exact eqv.bijective

variable (p : ℕ) (hp : f = (p : R))
include hp

/-- 二つの実H0反射の間には、元の線形標準単位を保つ同型がある。 -/
theorem _root_.SerrePositivity.DerivedCompletion.exists_iteratedPDH0LinearEquiv :
    ∃ e : H Z ≃ₗ[R] PDCompletionH0 R p d,
      ∀ x : R, e (_root_.SerrePositivity.DerivedCompletion.iteratedPDH0Unit R f d x) =
        pairCompletionH0Unit R (p : R) d x := by
  let B := ModuleCat.of R (PDCompletionH0 R p d)
  let u := pairCompletionH0Unit R (p : R) d
  let v := _root_.SerrePositivity.DerivedCompletion.iteratedPDH0Unit R f d
  let h := _root_.SerrePositivity.DerivedCompletion.iteratedPDH0_isCompleteModuleReflection R f d
  have hB : IsCompleteModuleReflection R (pairKoszulCoordinates R f d) B (u 1) := by
    rw [hp]
    exact pairCompletionH0_isCompleteModuleReflection R (p : R) d
  obtain ⟨f, hf⟩ := (h.universal B hB.isComplete).surjective (u 1)
  obtain ⟨g, hg⟩ := (hB.universal (H Z) h.isComplete).surjective (v 1)
  change f (v 1) = u 1 at hf
  change g (u 1) = v 1 at hg
  have hgf : g.comp f = LinearMap.id := by
    apply (h.universal (H Z) h.isComplete).injective
    change g (f (v 1)) = v 1
    rw [hf, hg]
  have hfg : f.comp g = LinearMap.id := by
    apply (hB.universal B hB.isComplete).injective
    change f (g (u 1)) = u 1
    rw [hg, hf]
  let e : H Z ≃ₗ[R] PDCompletionH0 R p d :=
    { f with
      invFun := g
      left_inv := fun x => LinearMap.congr_fun hgf x
      right_inv := fun x => LinearMap.congr_fun hfg x }
  refine ⟨e, ?_⟩
  intro x
  have hx : v x = x • v 1 := by simpa only [smul_eq_mul, mul_one] using v.map_smul x (1 : R)
  have hu : u x = x • u 1 := by simpa only [smul_eq_mul, mul_one] using u.map_smul x (1 : R)
  change e (v x) = u x
  rw [hx, hu, map_smul]
  exact congrArg (fun t => x • t) hf

/-- 元のRaw線形単位で正規化した、実逐次H0から実PD完備化H0への同型。 -/
def _root_.SerrePositivity.DerivedCompletion.iteratedPDH0LinearEquiv : H Z ≃ₗ[R] PDCompletionH0 R p d :=
  (_root_.SerrePositivity.DerivedCompletion.exists_iteratedPDH0LinearEquiv R f d p hp).choose

/-- 比較は全raw係数の元の完備化像を保つ。 -/
theorem _root_.SerrePositivity.DerivedCompletion.iteratedPDH0LinearEquiv_unit (x : R) :
    _root_.SerrePositivity.DerivedCompletion.iteratedPDH0LinearEquiv R f d p hp (_root_.SerrePositivity.DerivedCompletion.iteratedPDH0Unit R f d x) =
      pairCompletionH0Unit R (p : R) d x :=
  (_root_.SerrePositivity.DerivedCompletion.exists_iteratedPDH0LinearEquiv R f d p hp).choose_spec x

end SerrePositivity.BhattScholze

end IteratedPDH0Reflection
