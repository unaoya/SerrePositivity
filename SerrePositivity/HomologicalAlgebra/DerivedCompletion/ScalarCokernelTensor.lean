module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PowerCokernelEquivalence
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed

/-!
# スカラーの余核の同値とテンソル積

## 概要
スカラーの余核で同型になる写像は、任意の加群とテンソルしても同じ余核で同型になる。

## 方針
テンソル関手が余核を保つことと、標準の余核比較の自然性を使う。

## 規約
元の加群の平坦性は要らない。

## 使われ方
BS 著者版 Theorem 6.4 の分冪係数の有限冪商の同型を微分形式の各項へ移す。
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u

namespace SerrePositivity.DerivedCompletion

set_option backward.isDefEq.respectTransparency false

private theorem isIso_map_cokernelMap_iff
    {C D : Type*} [Category* C] [Category* D] [HasZeroMorphisms C] [HasZeroMorphisms D]
    (F : C ⥤ D) [F.PreservesZeroMorphisms]
    {X Y X' Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y')
    [HasCokernel f] [HasCokernel g] [HasCokernel (F.map f)] [HasCokernel (F.map g)]
    [PreservesColimit (parallelPair f 0) F] [PreservesColimit (parallelPair g 0) F]
    (a : X ⟶ X') (b : Y ⟶ Y') (h : f ≫ b = a ≫ g) :
    IsIso (F.map (cokernel.map f g a b h)) ↔
      IsIso (cokernel.map (F.map f) (F.map g) (F.map a) (F.map b)
        (by rw [← F.map_comp, h, F.map_comp])) := by
  have he := preserves_cokernel_iso_comp_cokernel_map F f g a b h
  constructor
  · intro hh
    have := hh
    have hc : IsIso ((PreservesCokernel.iso F f).hom ≫
        cokernel.map (F.map f) (F.map g) (F.map a) (F.map b)
          (by rw [← F.map_comp, h, F.map_comp])) := by
      rw [he]
      infer_instance
    exact IsIso.of_isIso_comp_left (PreservesCokernel.iso F f).hom _
  · intro hh
    have := hh
    have hc : IsIso (F.map (cokernel.map f g a b h) ≫ (PreservesCokernel.iso F g).hom) := by
      rw [← he]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (PreservesCokernel.iso F g).hom

private theorem cokernelMap_isIso_of_eq
    {C : Type*} [Category* C] [HasZeroMorphisms C] {M N : C}
    (f f' : M ⟶ M) (g g' : N ⟶ N)
    [HasCokernel f] [HasCokernel f'] [HasCokernel g] [HasCokernel g']
    (hf : f = f') (hg : g = g') (h : M ⟶ N)
    (w : f ≫ h = h ≫ g) (w' : f' ≫ h = h ≫ g')
    (hh : IsIso (cokernel.map f g h h w)) : IsIso (cokernel.map f' g' h h w') := by
  subst f'
  subst g'
  exact hh

variable {R : Type u} [CommRing R] (a : R) {M N : ModuleCat.{u} R}

/-- スカラーの作用の通常の余核を、加群について関手化する。 -/
def scalarCokernelFunctor : ModuleCat.{u} R ⥤ ModuleCat.{u} R where
  obj M := cokernel (a • 𝟙 M)
  map {M N} f := cokernel.map (a • 𝟙 M) (a • 𝟙 N) f f
    (by simp [Linear.smul_comp, Linear.comp_smul])
  map_id M := by simp
  map_comp {M N P} f g := by
    apply (cancel_epi (cokernel.π (a • 𝟙 M))).mp
    simp [cokernel.map, Category.assoc]

/-- 任意の加群との右テンソル積は、スカラーの余核での同値を保つ。 -/
theorem tensorRight_scalarCokernelMap_isIso (f : M ⟶ N) (V : ModuleCat.{u} R)
    (hf : IsIso (cokernel.map (a • 𝟙 M) (a • 𝟙 N) f f
      (by simp [Linear.smul_comp, Linear.comp_smul]))) :
    IsIso (cokernel.map (a • 𝟙 (M ⊗ V)) (a • 𝟙 (N ⊗ V))
      ((tensorRight V).map f) ((tensorRight V).map f)
      (by simp [Linear.smul_comp, Linear.comp_smul])) := by
  let F := tensorRight V
  have := hf
  let w : (a • 𝟙 M) ≫ f = f ≫ (a • 𝟙 N) := by
    simp [Linear.smul_comp, Linear.comp_smul]
  have hm : IsIso (F.map (cokernel.map (a • 𝟙 M) (a • 𝟙 N) f f w)) := inferInstance
  have h := (isIso_map_cokernelMap_iff F (a • 𝟙 M) (a • 𝟙 N) f f w).mp hm
  change IsIso (cokernel.map (a • 𝟙 (F.obj M)) (a • 𝟙 (F.obj N)) (F.map f) (F.map f) _)
  have hM : F.map (a • 𝟙 M) = a • 𝟙 (F.obj M) := by
    simp [F]
  have hN : F.map (a • 𝟙 N) = a • 𝟙 (F.obj N) := by
    simp [F]
  exact cokernelMap_isIso_of_eq _ _ _ _ hM hN (F.map f) _ _ h

/-- 余鎖写像のスカラーの余核が各次数で同型なら、複体の余核でも同型。 -/
theorem powerCokernelMap_isIso_of_components
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} (f : K ⟶ L) (n : ℕ)
    (hf : ∀ i, IsIso (cokernel.map (a ^ n • 𝟙 (K.X i)) (a ^ n • 𝟙 (L.X i))
      (f.f i) (f.f i) (by
        simp [Linear.smul_comp, Linear.comp_smul]))) :
    IsIso (powerCokernelMap a f n) := by
  have h (i : ℤ) : IsIso ((powerCokernelMap a f n).f i) := by
    let F := HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.up ℤ) i
    have he := (isIso_map_cokernelMap_iff F (smulId (a ^ n) K) (smulId (a ^ n) L) f f
      (by simp [smulId, Linear.smul_comp, Linear.comp_smul])).mpr (by
        have hM : F.map (smulId (a ^ n) K) = a ^ n • 𝟙 (K.X i) := rfl
        have hN : F.map (smulId (a ^ n) L) = a ^ n • 𝟙 (L.X i) := rfl
        exact cokernelMap_isIso_of_eq _ _ _ _ hM.symm hN.symm (f.f i) _ _ (hf i))
    exact he
  exact HomologicalComplex.Hom.isIso_of_components _


end SerrePositivity.DerivedCompletion
