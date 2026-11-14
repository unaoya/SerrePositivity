module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.DifferentialGraded.Tensor.BalancedElements
public import SerrePositivity.DifferentialGraded.Functor.QuasiEquivalence
public import SerrePositivity.DifferentialGraded.Bimodule.Tensor
public import SerrePositivity.DifferentialGraded.Module.Hom.HomotopyAndOperations

public import SerrePositivity.DifferentialGraded.Module.Hom.ColimitsAndRightHom
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Adjunction.Limits
public import SerrePositivity.DifferentialGraded.Tensor.Parameter
public import Mathlib.Algebra.Homology.QuasiIso
public import SerrePositivity.HomologicalAlgebra.CochainTensor.Cone
public import SerrePositivity.DifferentialGraded.Module.ActionLimits
public import SerrePositivity.DifferentialGraded.Complexes.Perturbation
public import Mathlib.Algebra.Category.ModuleCat.AB
public import SerrePositivity.DifferentialGraded.Complexes.MaurerCartanCurrying
public import SerrePositivity.DifferentialGraded.Module.TensorFree


public import SerrePositivity.DifferentialGraded.Module.Hom.ConeComparison

public import SerrePositivity.DifferentialGraded.Complexes.Cone


public import SerrePositivity.DifferentialGraded.Module.Graded



public import Mathlib.CategoryTheory.Adjunction.Unique
public import SerrePositivity.DifferentialGraded.Module.ShiftResolution


/-!
# Tensor.Enriched

## 概要
22 本に分かれていた同主題の構成と比較をまとめる。

## 方針
対応表の依存順に連結し、元の宣言・証明・名前空間を保持する。

## 規約
各元ファイルの section を分離し、variable・option の局所的な作用を保つ。

## 使われ方
DifferentialGraded の入口と、この主題を使う検査・下流モジュールから import する。
-/

/-! ## HomUnits（旧 SerrePositivity/DifferentialGraded/Tensor/HomUnits.lean） -/

/-! # balanced tensorの主Hom写像の単位保存 -/

@[expose] public section HomUnits
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma moduleHom_unit_π (M : RightModule A D) (x : D) :
    (moduleHomπ A D M M x).f 0 (unitElement A M).val = Cochain.ofHom (𝟙 (M.obj (op x))) := by
  have h := DGFunctor.map_unitElement A (moduleEvaluationDG A D x) M
  rw [Bimodule.complex_unitElement] at h
  exact h

lemma leftModuleHom_unit_π (N : LeftModule A D) (x : D) :
    (leftModuleHomπ A D N N x).f 0 (unitElement A N).val = Cochain.ofHom (𝟙 (N.obj x)) := by
  have h := DGFunctor.map_unitElement A (leftModuleEvaluationDG A D x) N
  rw [Bimodule.complex_unitElement] at h
  exact h

lemma rightHomMap_unit (M : RightModule A D) (N : LeftModule A D) :
    (rightHomMap A D M M N).f 0 (unitElement A M).val =
      (unitElement A (obj A D M N)).val := by
  rw [Bimodule.complex_unitElement]
  apply cochain_zero_element_ext A D M N
  intro x r s a ha m v
  rw [rightHomMap_element_of_sum A D N _ x m v ha (zero_add r) (add_zero a),
    moduleHom_unit_π]
  simp only [Cochain.ofHom_v, HomologicalComplex.id_f, ModuleCat.id_apply]

lemma leftHomMap_unit (M : RightModule A D) (N : LeftModule A D) :
    (leftHomMap A D M N N).f 0 (unitElement A N).val =
      (unitElement A (obj A D M N)).val := by
  rw [Bimodule.complex_unitElement]
  apply cochain_zero_element_ext A D M N
  intro x r s a ha m v
  rw [leftHomMap_element_of_sum A D M _ x m v ha (zero_add s) (add_zero a),
    leftModuleHom_unit_π]
  simp only [zero_mul, Int.negOnePow_zero, one_smul, Cochain.ofHom_v,
    HomologicalComplex.id_f, ModuleCat.id_apply]

end SerrePositivity.DifferentialGraded.BalancedTensor
end

end HomUnits

/-! ## HomComposition（旧 SerrePositivity/DifferentialGraded/Tensor/HomComposition.lean） -/

/-! # balanced tensorの主Hom写像の合成保存 -/

@[expose] public section HomComposition
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma rightHomMap_forward {M M' M'' : RightModule A D} (N : LeftModule A D)
    {p q k : ℤ} (τ : (moduleHom A D M M').X p) (σ : (moduleHom A D M' M'').X q)
    (hk : p + q = k) :
    (rightHomMap A D M M'' N).f k
      (forward A (D := RightModule A D) (x := M) (y := M') (z := M'') τ σ hk) =
      forward A (D := Complex A) (x := obj A D M N) (y := obj A D M' N)
        (z := obj A D M'' N) ((rightHomMap A D M M' N).f p τ)
        ((rightHomMap A D M' M'' N).f q σ) hk := by
  change _ = (enrichedComposition (obj A D M N) (obj A D M' N) (obj A D M'' N)).f k
    (ιTensorObj (homComplex A (obj A D M N) (obj A D M' N))
      (homComplex A (obj A D M' N) (obj A D M'' N)) p q k hk
      (((rightHomMap A D M M' N).f p τ) ⊗ₜ[A] ((rightHomMap A D M' M'' N).f q σ)))
  rw [enrichedComposition_apply]
  apply cochain_element_ext A D M N
  intro x r s a n ha hn m v
  rw [rightHomMap_element_of_sum A D N _ x m v ha (show k + r = q + (p + r) by omega) hn,
    moduleHomForward_π, Cochain.units_smul_v,
    Cochain.comp_v _ _ hk r (p + r) (q + (p + r)) (by omega) (by omega),
    Cochain.units_smul_v,
    Cochain.comp_v _ _ hk a (p + r + s) n (by omega) (by omega)]
  change element A D M'' N x
      ((p * q).negOnePow • (((moduleHomπ A D M' M'' x).f q σ).v (p + r)
        (q + (p + r)) (by omega)
        (((moduleHomπ A D M M' x).f p τ).v r (p + r) (by omega) m))) v (by omega) =
    (p * q).negOnePow • (((rightHomMap A D M' M'' N).f q σ).v (p + r + s) n
      (by omega) ((((rightHomMap A D M M' N).f p τ).v a (p + r + s) (by omega))
        (element A D M N x m v ha)))
  rw [rightHomMap_element_of_sum A D N τ x m v ha rfl (by omega),
    rightHomMap_element_of_sum A D N σ x _ v rfl rfl (by omega)]
  simp only [element, Units.smul_def, ← TensorProduct.smul_tmul', map_zsmul]

lemma leftModuleHomForward_π {N N' N'' : LeftModule A D} {p q k : ℤ}
    (τ : (leftModuleHom A D N N').X p) (σ : (leftModuleHom A D N' N'').X q)
    (hk : p + q = k) (x : D) :
    (leftModuleHomπ A D N N'' x).f k
      (forward A (D := LeftModule A D) (x := N) (y := N') (z := N'') τ σ hk) =
    (p * q).negOnePow • (((leftModuleHomπ A D N N' x).f p τ).comp
      ((leftModuleHomπ A D N' N'' x).f q σ) hk) :=
  DGFunctor.map_forward_cochain A (leftModuleEvaluationDG A D x) τ σ hk

lemma leftHomMap_forward (M : RightModule A D) {N N' N'' : LeftModule A D}
    {p q k : ℤ} (τ : (leftModuleHom A D N N').X p) (σ : (leftModuleHom A D N' N'').X q)
    (hk : p + q = k) :
    (leftHomMap A D M N N'').f k
      (forward A (D := LeftModule A D) (x := N) (y := N') (z := N'') τ σ hk) =
    forward A (D := Complex A) (x := obj A D M N) (y := obj A D M N')
      (z := obj A D M N'') ((leftHomMap A D M N N').f p τ)
        ((leftHomMap A D M N' N'').f q σ) hk := by
  change _ = (enrichedComposition (obj A D M N) (obj A D M N') (obj A D M N'')).f k
    (ιTensorObj (homComplex A (obj A D M N) (obj A D M N'))
      (homComplex A (obj A D M N') (obj A D M N'')) p q k hk
      (((leftHomMap A D M N N').f p τ) ⊗ₜ[A] ((leftHomMap A D M N' N'').f q σ)))
  rw [enrichedComposition_apply]
  apply cochain_element_ext A D M N
  intro x r s a n ha hn m v
  rw [leftHomMap_element_of_sum A D M _ x m v ha (show k + s = q + (p + s) by omega) hn,
    leftModuleHomForward_π, Cochain.units_smul_v,
    Cochain.comp_v _ _ hk s (p + s) (q + (p + s)) (by omega) (by omega),
    Cochain.units_smul_v,
    Cochain.comp_v _ _ hk a (r + (p + s)) n (by omega) (by omega)]
  change (k * r).negOnePow • element A D M N'' x m
      ((p * q).negOnePow • (((leftModuleHomπ A D N' N'' x).f q σ).v (p + s)
        (q + (p + s)) (by omega) (((leftModuleHomπ A D N N' x).f p τ).v s (p + s)
          (by omega) v))) (by omega) =
    (p * q).negOnePow • (((leftHomMap A D M N' N'').f q σ).v (r + (p + s)) n
      (by omega) ((((leftHomMap A D M N N').f p τ).v a (r + (p + s)) (by omega))
        (element A D M N x m v ha)))
  rw [element_units_smul_right,
    leftHomMap_element_of_sum A D M τ x m v ha rfl (by omega)]
  simp only [Units.smul_def, map_zsmul]
  change (k * r).negOnePow • ((p * q).negOnePow • _) =
    (p * q).negOnePow • ((p * r).negOnePow •
      (((leftHomMap A D M N' N'').f q σ).v (r + (p + s)) n (by omega)
        (element A D M N' x m
          (((leftModuleHomπ A D N N' x).f p τ).v s (p + s) (by omega) v) rfl)))
  rw [leftHomMap_element_of_sum A D M σ x m _ rfl rfl (by omega)]
  simp only [smul_smul, ← Int.negOnePow_add]
  congr 1
  congr 1
  rw [← hk]
  ring

end SerrePositivity.DifferentialGraded.BalancedTensor
end

end HomComposition

/-! ## HomAdjunctionFamilies（旧 SerrePositivity/DifferentialGraded/Tensor/HomAdjunctionFamilies.lean） -/

/-! # balanced族の転置と全dg自然な右Hom加群への射の族 -/

@[expose] public section HomAdjunctionFamilies
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

lemma curryBalancedFamily_action {M : RightModule A D} {N : LeftModule A D} {T : Complex A}
    (a : BalancedFamily A D M N T) (x y : Dᵒᵖ) (p r n : ℤ) (hn : r + p = n)
    (f : GradedHom A x y p) (m : (M.obj x).X r) :
    (curryRight (a.val y.unop)).f n (moduleAction A M f m hn) =
      moduleAction A (homRightModule A D N T) f ((curryRight (a.val x.unop)).f r m) hn := by
  subst n
  change (curryRight (a.val y.unop)).f (r + p) (moduleAction A M f m rfl) =
    (((homRightModule A D N T).map x y).f p f).v r (r + p) rfl
      ((curryRight (a.val x.unop)).f r m)
  rw [homRightModule_action]
  apply Cochain.ext
  intro s l hl
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro t
  rw [Cochain.units_smul_v, Cochain.comp_v _ _ _ s (p + s) l (by omega) (by omega)]
  change (curryComponent (a.val y.unop) (r + p) (moduleAction A M f m rfl)).v s l hl t =
    (p * r).negOnePow • (curryComponent (a.val x.unop) r m).v (p + s) l (by omega)
      (SerrePositivity.DifferentialGraded.leftAction A N (n := p + s) f t (by omega))
  rw [curryComponent_apply, curryComponent_apply]
  have he := balancedFamily_element A D a y.unop x.unop m f t (by omega : r + p + s = l)
  change (r * p).negOnePow • _ = _ at he
  rw [mul_comm r p] at he
  calc
    _ = (p * r).negOnePow • ((p * r).negOnePow •
        familyElement A D a.val y.unop (moduleAction A M f m rfl) t (by omega)) := by
      rw [smul_smul, Int.units_mul_self, one_smul]
      rfl
    _ = _ := congrArg (fun z => (p * r).negOnePow • z) he

/-- balanced族の対象ごとの転置は右Hom加群への全次数自然なchain map族。 -/
def curryBalancedFamily {M : RightModule A D} {N : LeftModule A D} {T : Complex A}
    (a : BalancedFamily A D M N T) : ModuleMapFamily A D M (homRightModule A D N T) :=
  ⟨fun x => curryRight (a.val x.unop),
    closedFamily_of_action A (M := M) (N := homRightModule A D N T)
      (fun x => curryRight (a.val x.unop))
      (curryBalancedFamily_action A D a)⟩

/-- 全次数自然な右Hom加群への射の族をbalanced族へ逆転置する。 -/
def uncurryModuleMapFamily {M : RightModule A D} {N : LeftModule A D} {T : Complex A}
    (b : ModuleMapFamily A D M (homRightModule A D N T)) : BalancedFamily A D M N T := by
  refine balancedFamilyMk A D (fun x => uncurryRight (b.val (op x))) ?_
  intro x y r p s n hn m f t
  have he := closedFamily_action A b.val b.property (op y) (op x) p r (r + p) rfl f m
  change (b.val (op x)).f (r + p) (moduleAction A M f m rfl) =
    (((homRightModule A D N T).map (op y) (op x)).f p f).v r (r + p) rfl
      ((b.val (op y)).f r m) at he
  rw [homRightModule_action] at he
  have hv := congrArg (fun c => c.v s n (by omega) t) he
  rw [Cochain.units_smul_v, Cochain.comp_v _ _ _ s (p + s) n (by omega) (by omega)] at hv
  change ((b.val (op x)).f (r + p) (moduleAction A M f m rfl)).v s n (by omega) t =
    (p * r).negOnePow • ((b.val (op y)).f r m).v (p + s) n (by omega)
      (SerrePositivity.DifferentialGraded.leftAction A N (n := p + s) f t (by omega)) at hv
  unfold familyElement
  rw [uncurryRight_apply, uncurryRight_apply]
  change (r * p).negOnePow • ((b.val (op x)).f (r + p)
      (moduleAction A M f m rfl)).v s n (by omega) t =
    ((b.val (op y)).f r m).v (p + s) n (by omega)
      (SerrePositivity.DifferentialGraded.leftAction A N (n := p + s) f t (by omega))
  rw [hv, mul_comm r p, smul_smul, Int.units_mul_self, one_smul]

/-- balanced族と主Hom endの閉零加群射の成分条件の同値。 -/
def balancedFamilyMapEquiv (M : RightModule A D) (N : LeftModule A D) (T : Complex A) :
    BalancedFamily A D M N T ≃ ModuleMapFamily A D M (homRightModule A D N T) where
  toFun := curryBalancedFamily A D
  invFun := uncurryModuleMapFamily A D
  left_inv a := by
    apply Subtype.ext
    funext x
    exact uncurryRight_curryRight (a.val x)
  right_inv b := by
    apply Subtype.ext
    funext x
    exact curryRight_uncurryRight (b.val x)

end SerrePositivity.DifferentialGraded.BalancedTensor
end

end HomAdjunctionFamilies

/-! ## HomAdjunction（旧 SerrePositivity/DifferentialGraded/Tensor/HomAdjunction.lean） -/

/-! # balanced tensorと右Hom加群の随伴 -/

@[expose] public section HomAdjunction
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory MonoidalCategory Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 主Hom endの閉零加群射を用いるtensor–Hom同値。 -/
def tensorHomEquiv (M : ModuleCategory A D) (N : LeftModule A D) (T : Complex A) :
    (obj A D (ForgetEnrichment.to (Complex A) M) N ⟶ T) ≃
      (M ⟶ ForgetEnrichment.of (Complex A) (homRightModule A D N T)) :=
  (homEquiv A D (ForgetEnrichment.to (Complex A) M) N T).trans
    ((balancedFamilyMapEquiv A D (ForgetEnrichment.to (Complex A) M) N T).trans
      (moduleMapFamilyEquiv A D M
        (ForgetEnrichment.of (Complex A) (homRightModule A D N T))).symm)

@[simp]
lemma tensorHomEquiv_eval (M : ModuleCategory A D) (N : LeftModule A D) (T : Complex A)
    (f : obj A D (ForgetEnrichment.to (Complex A) M) N ⟶ T) (x : D) :
    (moduleEvaluation A D x).map (tensorHomEquiv A D M N T f) =
      curryRight (ι A D (ForgetEnrichment.to (Complex A) M) N x ≫ f) :=
  moduleMorphismMk_eval A D _ _ x

@[reassoc (attr := simp)]
lemma ι_tensorHomEquiv_symm (M : ModuleCategory A D) (N : LeftModule A D) (T : Complex A)
    (g : M ⟶ ForgetEnrichment.of (Complex A) (homRightModule A D N T)) (x : D) :
    ι A D (ForgetEnrichment.to (Complex A) M) N x ≫ (tensorHomEquiv A D M N T).symm g =
      uncurryRight ((moduleEvaluation A D x).map g) := by
  exact ι_desc A D _ _ _ x

lemma tensorHomEquiv_naturality_target (M : ModuleCategory A D) (N : LeftModule A D)
    {T T' : Complex A} (f : obj A D (ForgetEnrichment.to (Complex A) M) N ⟶ T)
    (g : T ⟶ T') :
    tensorHomEquiv A D M N T' (f ≫ g) =
      tensorHomEquiv A D M N T f ≫ homRightModuleMap A D N g := by
  apply moduleMorphism_ext
  intro x
  rw [CategoryTheory.Functor.map_comp, tensorHomEquiv_eval, tensorHomEquiv_eval,
    homRightModuleMap_eval]
  rw [← Category.assoc, curryRight_naturality_target]

lemma tensorHomEquiv_naturality_source {M M' : ModuleCategory A D} (N : LeftModule A D)
    (h : M ⟶ M') (f : obj A D (ForgetEnrichment.to (Complex A) M') N ⟶ T) :
    tensorHomEquiv A D M N T
      (map A D h (𝟙 (ForgetEnrichment.of (Complex A) N)) ≫ f) =
      h ≫ tensorHomEquiv A D M' N T f := by
  apply moduleMorphism_ext
  intro x
  rw [CategoryTheory.Functor.map_comp, tensorHomEquiv_eval, tensorHomEquiv_eval]
  have hi := ι_map A D (N := ForgetEnrichment.of (Complex A) N)
    (N' := ForgetEnrichment.of (Complex A) N) h (𝟙 (ForgetEnrichment.of (Complex A) N)) x
  simp only [CategoryTheory.Functor.map_id] at hi
  change ι A D (ForgetEnrichment.to (Complex A) M) N x ≫
      map A D h (𝟙 (ForgetEnrichment.of (Complex A) N)) =
    ((moduleEvaluation A D x).map h ⊗ₘ 𝟙 (N.obj x)) ≫
      ι A D (ForgetEnrichment.to (Complex A) M') N x at hi
  rw [← Category.assoc, hi, Category.assoc]
  exact curryRight_naturality_source _ _

/-- 固定左加群とのbalanced tensorを閉零右加群圏上の通常関手にする。 -/
def rightTensorFunctor (N : LeftModule A D) : ModuleCategory A D ⥤ Complex A where
  obj M := obj A D (ForgetEnrichment.to (Complex A) M) N
  map h := map A D h (𝟙 (ForgetEnrichment.of (Complex A) N))
  map_id M := map_id A D M (ForgetEnrichment.of (Complex A) N)
  map_comp f g := by
    simpa only [Category.id_comp] using
      map_comp A D f g (𝟙 (ForgetEnrichment.of (Complex A) N))
        (𝟙 (ForgetEnrichment.of (Complex A) N))

/-- balanced tensorは右Hom加群関手の左随伴。 -/
def tensorHomAdjunction (N : LeftModule A D) :
    rightTensorFunctor A D N ⊣ homRightFunctor A D N :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun M T => tensorHomEquiv A D M N T
      homEquiv_naturality_left_symm := by
        intro M M' T f g
        change M' ⟶ ForgetEnrichment.of (Complex A) (homRightModule A D N T) at g
        change (tensorHomEquiv A D M N T).symm (f ≫ g) =
          map A D f (𝟙 (ForgetEnrichment.of (Complex A) N)) ≫
            (tensorHomEquiv A D M' N T).symm g
        apply (tensorHomEquiv A D M N T).injective
        rw [Equiv.apply_symm_apply, tensorHomEquiv_naturality_source, Equiv.apply_symm_apply]
      homEquiv_naturality_right := fun f g => tensorHomEquiv_naturality_target A D _ N f g }

lemma tensorHomAdjunction_homEquiv (N : LeftModule A D) (M : ModuleCategory A D)
    (T : Complex A) :
    (tensorHomAdjunction A D N).homEquiv M T = tensorHomEquiv A D M N T := by
  exact congrFun (congrFun (Adjunction.mkOfHomEquiv_homEquiv _) M) T

end SerrePositivity.DifferentialGraded.BalancedTensor
end

end HomAdjunction

/-! ## HomAdjunctionLaws（旧 SerrePositivity/DifferentialGraded/Tensor/HomAdjunctionLaws.lean） -/

/-! # tensor–Hom随伴の単位・余単位・三角恒等式と余極限保存 -/

@[expose] public section HomAdjunctionLaws
universe u v w t

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory MonoidalCategory Opposite Limits CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma tensorHomAdjunction_unit (N : LeftModule A D) (M : ModuleCategory A D) :
    (tensorHomAdjunction A D N).unit.app M =
      tensorHomEquiv A D M N (obj A D (ForgetEnrichment.to (Complex A) M) N) (𝟙 _) := by
  have h := ((tensorHomAdjunction A D N).homEquiv_id M).symm
  rw [tensorHomAdjunction_homEquiv] at h
  exact h

@[simp]
lemma tensorHomAdjunction_unit_eval (N : LeftModule A D) (M : ModuleCategory A D) (x : D) :
    (moduleEvaluation A D x).map ((tensorHomAdjunction A D N).unit.app M) =
      curryRight (ι A D (ForgetEnrichment.to (Complex A) M) N x) := by
  rw [tensorHomAdjunction_unit]
  have h := tensorHomEquiv_eval A D M N
    (obj A D (ForgetEnrichment.to (Complex A) M) N) (𝟙 _) x
  rw [Category.comp_id] at h
  exact h

lemma tensorHomAdjunction_counit (N : LeftModule A D) (T : Complex A) :
    (tensorHomAdjunction A D N).counit.app T =
      (tensorHomEquiv A D (ForgetEnrichment.of (Complex A) (homRightModule A D N T)) N T).symm
        (𝟙 _) := by
  have h := ((tensorHomAdjunction A D N).homEquiv_symm_id T).symm
  rw [tensorHomAdjunction_homEquiv] at h
  exact h

@[reassoc (attr := simp)]
lemma ι_tensorHomAdjunction_counit (N : LeftModule A D) (T : Complex A) (x : D) :
    ι A D (homRightModule A D N T) N x ≫ (tensorHomAdjunction A D N).counit.app T =
      uncurryRight (𝟙 (homComplex A (N.obj x) T)) := by
  rw [tensorHomAdjunction_counit]
  have h := ι_tensorHomEquiv_symm A D
    (ForgetEnrichment.of (Complex A) (homRightModule A D N T)) N T (𝟙 _) x
  rw [CategoryTheory.Functor.map_id] at h
  exact h

lemma tensorHomAdjunction_counit_element (N : LeftModule A D) (T : Complex A) (x : D)
    {r s n : ℤ} (g : Homogeneous (N.obj x) T r) (v : (N.obj x).X s) (hn : r + s = n) :
    ((tensorHomAdjunction A D N).counit.app T).f n
      (element A D (homRightModule A D N T) N x g v hn) = g.v s n (by omega) v := by
  have h := element_postcompose A D (homRightModule A D N T) N x
    ((tensorHomAdjunction A D N).counit.app T) (uncurryRight (𝟙 (homComplex A (N.obj x) T)))
    (ι_tensorHomAdjunction_counit A D N T x) g v hn
  exact h.trans (uncurryRight_apply (𝟙 (homComplex A (N.obj x) T)) r s n hn g v)

lemma tensorHomAdjunction_left_triangle (N : LeftModule A D) (M : ModuleCategory A D) :
    (rightTensorFunctor A D N).map ((tensorHomAdjunction A D N).unit.app M) ≫
      (tensorHomAdjunction A D N).counit.app ((rightTensorFunctor A D N).obj M) = 𝟙 _ :=
  (tensorHomAdjunction A D N).left_triangle_components M

lemma tensorHomAdjunction_right_triangle (N : LeftModule A D) (T : Complex A) :
    (tensorHomAdjunction A D N).unit.app ((homRightFunctor A D N).obj T) ≫
      (homRightFunctor A D N).map ((tensorHomAdjunction A D N).counit.app T) = 𝟙 _ :=
  (tensorHomAdjunction A D N).right_triangle_components T

/-- 固定左加群とのbalanced tensorは、存在する任意サイズの余極限を保存する。 -/
instance rightTensorFunctor_preservesColimits (N : LeftModule A D) :
    PreservesColimitsOfSize.{w, t} (rightTensorFunctor A D N) :=
  (tensorHomAdjunction A D N).leftAdjoint_preservesColimits

end SerrePositivity.DifferentialGraded.BalancedTensor
end

end HomAdjunctionLaws

/-! ## KFlat（旧 SerrePositivity/DifferentialGraded/Tensor/KFlat.lean） -/

/-! # A上のK-flat性とdg圏上の相対K-flat性

非有界acyclic複体を試験対象とする。相対条件はHom複体のA-flat性を仮定しない。
-/

@[expose] public section KFlat
universe u v

noncomputable section
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits MonoidalCategory HomologicalComplex
variable (A : Type u) [CommRing A]

/-- 任意の非有界acyclic A複体とのtensorがacyclicになる条件。 -/
def complexKFlat (K : Complex A) : Prop :=
  ∀ L : Complex A, L.Acyclic → (K ⊗ L).Acyclic

/-- A上のK-flat性は複体同型で不変。 -/
lemma complexKFlat_of_iso {K K' : Complex A} (e : K ≅ K')
    (h : complexKFlat A K') : complexKFlat A K := by
  intro L hL n
  exact (exactAt_iff_of_quasiIsoAt ((tensorRight L).mapIso e).hom n).2 (h L hL n)

/-- 複体のretractはacyclic性を保つ。 -/
lemma complex_acyclic_of_retract {K L : Complex A} (e : Retract K L) (h : L.Acyclic) :
    K.Acyclic := by
  intro n
  apply (exactAt_iff_isZero_homology K n).2
  let r := e.map (homologyFunctor (ModuleCat A) (ComplexShape.up ℤ) n)
  have hz : IsZero ((homologyFunctor (ModuleCat A) (ComplexShape.up ℤ) n).obj L) :=
    (h n).isZero_homology
  apply (Limits.IsZero.iff_id_eq_zero _).2
  calc
    𝟙 _ = r.i ≫ r.r := r.retract.symm
    _ = 0 := by rw [hz.eq_of_tgt r.i 0, zero_comp]

/-- A上のK-flat複体はretractで閉じる。 -/
lemma complexKFlat_of_retract {K K' : Complex A} (e : Retract K K')
    (h : complexKFlat A K') : complexKFlat A K := by
  intro L hL
  exact complex_acyclic_of_retract A (e.map (tensorRight L)) (h L hL)

variable (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 左dg加群のすべての評価複体がacyclicになる条件。 -/
def leftModuleAcyclic (N : LeftModule A D) : Prop :=
  ∀ x : D, (N.obj x).Acyclic

/-- 任意のobjectwise acyclic左加群をbalanced tensorで消す相対K-flat性。 -/
def moduleRelativeKFlat (M : RightModule A D) : Prop :=
  ∀ N : LeftModule A D, leftModuleAcyclic A D N → (BalancedTensor.obj A D M N).Acyclic

/-- dg圏のHomにflat性を置かず、Yoneda評価からrepresentableの相対K-flat性を得る。 -/
lemma representable_relativeKFlat (x : D) :
    moduleRelativeKFlat A D (representable A x) := by
  intro N hN n
  exact (exactAt_iff_of_quasiIsoAt (BalancedTensor.yonedaIso A D x N).hom n).2 (hN x n)

/-- 相対K-flat性は全dg自然な右加群同型で不変。 -/
lemma moduleRelativeKFlat_of_iso {M M' : RightModule A D}
    (e : ForgetEnrichment.of (Complex A) M ≅ ForgetEnrichment.of (Complex A) M')
    (h : moduleRelativeKFlat A D M') : moduleRelativeKFlat A D M := by
  intro N hN n
  exact (exactAt_iff_of_quasiIsoAt
    ((BalancedTensor.rightTensorFunctor A D N).mapIso e).hom n).2 (h N hN n)

/-- 相対K-flat右加群は全dg自然なretractで閉じる。 -/
lemma moduleRelativeKFlat_of_retract {M M' : RightModule A D}
    (e : Retract (ForgetEnrichment.of (Complex A) M) (ForgetEnrichment.of (Complex A) M'))
    (h : moduleRelativeKFlat A D M') : moduleRelativeKFlat A D M := by
  intro N hN
  exact complex_acyclic_of_retract A
    (e.map (BalancedTensor.rightTensorFunctor A D N)) (h N hN)

end SerrePositivity.DifferentialGraded
end

end KFlat

/-! ## KFlatComplex（旧 SerrePositivity/DifferentialGraded/Tensor/KFlatComplex.lean） -/

/-! # A上のK-flat複体の単位・shift・cone・tensor閉性 -/

@[expose] public section KFlatComplex
universe u

noncomputable section
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits MonoidalCategory HomologicalComplex CochainComplex
open scoped ZeroObject
variable (A : Type u) [CommRing A]

lemma complexKFlat_unit : complexKFlat A (𝟙_ (Complex A)) := by
  intro L hL
  exact cochainAcyclic_of_iso hL (λ_ L).symm

lemma complexKFlat_shift {K : Complex A} (h : complexKFlat A K) (s : ℤ) :
    complexKFlat A (K⟦s⟧) := by
  intro L hL
  exact cochainAcyclic_of_iso (cochainAcyclic_shift (h L hL) s)
    (cochainTensorShiftLeft K L s).symm

lemma complexKFlat_cone {K K' : Complex A} (f : K ⟶ K')
    (hK : complexKFlat A K) (hK' : complexKFlat A K') :
    complexKFlat A (mappingCone f) := by
  intro L hL
  exact cochainAcyclic_of_iso
    (cochainAcyclic_mappingCone (cochainTensorMap f (𝟙 L)) (hK L hL) (hK' L hL))
    (cochainTensorConeLeft f L).symm

lemma complexKFlat_tensor {K K' : Complex A} (hK : complexKFlat A K)
    (hK' : complexKFlat A K') : complexKFlat A (K ⊗ K') := by
  intro L hL
  exact cochainAcyclic_of_iso (hK (K' ⊗ L) (hK' L hL)) (α_ K K' L).symm

/-- 両側に有界なflat複体とのtensorは、相手が非有界でもacyclic性を保つ。 -/
lemma complexKFlat_of_flat_bounds (K : Complex A) (a b : ℤ)
    (ha : ∀ i, i < a → IsZero (K.X i)) (hb : ∀ i, b < i → IsZero (K.X i))
    (hflat : ∀ i, Module.Flat A (K.X i)) : complexKFlat A K := by
  intro L hL
  exact cochainTensor_acyclic_of_flat_bounds K L a b ha hb hflat hL

/-- K-flatな右因子とのtensorは任意の準同型を保つ。 -/
lemma complexKFlat_quasiIso_left {K : Complex A} (hK : complexKFlat A K)
    {L L' : Complex A} (f : L ⟶ L') [QuasiIso f] :
    QuasiIso (cochainTensorMap f (𝟙 K)) := by
  have hc := (cochain_quasiIso_iff_cone_acyclic f).1 inferInstance
  have ht := cochainAcyclic_of_iso (hK (mappingCone f) hc)
    (cochainTensorSymmetry K (mappingCone f))
  exact (cochain_quasiIso_iff_cone_acyclic _).2
    (cochainAcyclic_of_iso ht (cochainTensorConeLeft f K))

/-- K-flatな左因子とのtensorは任意の準同型を保つ。 -/
lemma complexKFlat_quasiIso_right {K : Complex A} (hK : complexKFlat A K)
    {L L' : Complex A} (f : L ⟶ L') [QuasiIso f] :
    QuasiIso (cochainTensorMap (𝟙 K) f) := by
  have := complexKFlat_quasiIso_left A hK f
  have : QuasiIso (cochainTensorMap (𝟙 K) f ≫ (cochainTensorSymmetry K L').hom) := by
    rw [cochainTensorSymmetry_naturality]
    infer_instance
  exact quasiIso_of_comp_right _ (cochainTensorSymmetry K L').hom

/-- 非有界acyclicの消滅条件と、任意の準同型の保存は同値。 -/
lemma complexKFlat_iff_preserves_quasiIso (K : Complex A) :
    complexKFlat A K ↔ ∀ {L L' : Complex A} (f : L ⟶ L'),
      QuasiIso f → QuasiIso (cochainTensorMap (𝟙 K) f) := by
  constructor
  · intro h L L' f hf
    have := hf
    exact complexKFlat_quasiIso_right A h f
  · intro h L hL
    have h₀ : (0 : Complex A).Acyclic := acyclic_of_isZero _ (isZero_zero _)
    have hf : QuasiIso (0 : L ⟶ (0 : Complex A)) := ⟨fun n =>
      (quasiIsoAt_iff_exactAt' _ n (h₀ n)).2 (hL n)⟩
    have := h (0 : L ⟶ (0 : Complex A)) hf
    have hz : (K ⊗ (0 : Complex A)).Acyclic :=
      acyclic_of_isZero _ ((tensorLeft K).map_isZero (isZero_zero _))
    intro n
    exact (exactAt_iff_of_quasiIsoAt (cochainTensorMap (𝟙 K) (0 : L ⟶ (0 : Complex A))) n).2
      (hz n)

end SerrePositivity.DifferentialGraded
end

end KFlatComplex

/-! ## KFlatColimits（旧 SerrePositivity/DifferentialGraded/Tensor/KFlatColimits.lean） -/

/-! # 相対K-flat加群のexactな余極限 -/

@[expose] public section KFlatColimits
universe u v w w'

noncomputable section
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits MonoidalCategory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

omit [DGCategory A D] [Small.{u} D] in
/-- A上のK-flat複体はModuleCatのexactな余極限で閉じる。 -/
lemma complexKFlat_colimit {J : Type w} [Category.{w'} J] [Small.{u} J]
    [HasExactColimitsOfShape J (ModuleCat.{u} A)] (F : J ⥤ Complex A)
    (h : ∀ j, complexKFlat A (F.obj j)) : complexKFlat A (colimit F) := by
  intro L hL
  have hc := complex_colimit_acyclic A (F ⋙ tensorRight L) (fun j => h j L hL)
  intro n
  exact (hc n).of_iso (preservesColimitIso (tensorRight L) F).symm

/-- ModuleCatのexactな余極限の形に沿う相対K-flat加群の余極限は相対K-flat。 -/
lemma moduleRelativeKFlat_colimit {J : Type w} [Category.{w'} J] [Small.{u} J]
    [HasExactColimitsOfShape J (ModuleCat.{u} A)]
    (F : J ⥤ ModuleCategory A D)
    (h : ∀ j, moduleRelativeKFlat A D (ForgetEnrichment.to (Complex A) (F.obj j))) :
    moduleRelativeKFlat A D (ForgetEnrichment.to (Complex A) (colimit F)) := by
  intro N hN
  have hc := complex_colimit_acyclic A (F ⋙ BalancedTensor.rightTensorFunctor A D N)
    (fun j => h j N hN)
  intro n
  exact (hc n).of_iso (preservesColimitIso (BalancedTensor.rightTensorFunctor A D N) F).symm

/-- u-smallな族の余積は相対K-flat性を保つ。 -/
lemma moduleRelativeKFlat_coproduct {I : Type u} (M : I → RightModule A D)
    (h : ∀ i, moduleRelativeKFlat A D (M i)) :
    moduleRelativeKFlat A D
      (ForgetEnrichment.to (Complex A) (∐ fun i => ForgetEnrichment.of (Complex A) (M i))) :=
  moduleRelativeKFlat_colimit A D (Discrete.functor fun i => ForgetEnrichment.of (Complex A) (M i))
    (fun i => h i.as)

/-- 非有界加群の逐次余極限は相対K-flat性を保つ。 -/
lemma moduleRelativeKFlat_sequentialColimit (F : ℕ ⥤ ModuleCategory A D)
    (h : ∀ j, moduleRelativeKFlat A D (ForgetEnrichment.to (Complex A) (F.obj j))) :
    moduleRelativeKFlat A D (ForgetEnrichment.to (Complex A) (colimit F)) := by
  have : AB5OfSize.{0, 0} (ModuleCat.{u} A) := AB5OfSize_of_univLE (ModuleCat.{u} A)
  exact moduleRelativeKFlat_colimit A D F h

end SerrePositivity.DifferentialGraded
end

end KFlatColimits

/-! ## Enriched（旧 SerrePositivity/DifferentialGraded/Tensor/Enriched.lean） -/

/-! # balanced tensorの各変数に関するdg関手 -/

@[expose] public section Enriched
universe u v

noncomputable section
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 左加群を固定したbalanced tensorのdg関手。 -/
def rightTensorDG (N : LeftModule A D) : DGFunctor A (RightModule A D) (Complex A) :=
  DGFunctor.ofHomMaps A (fun M => obj A D M N) (fun M M' => rightHomMap A D M M' N)
    (fun M => rightHomMap_unit A D M N)
    (fun _ _ _ _ _ _ hk τ σ => rightHomMap_forward A D N τ σ hk)

/-- 右加群を固定したbalanced tensorのdg関手。 -/
def leftTensorDG (M : RightModule A D) : DGFunctor A (LeftModule A D) (Complex A) :=
  DGFunctor.ofHomMaps A (fun N => obj A D M N) (fun N N' => leftHomMap A D M N N')
    (fun N => leftHomMap_unit A D M N)
    (fun _ _ _ _ _ _ hk τ σ => leftHomMap_forward A D M τ σ hk)

end SerrePositivity.DifferentialGraded.BalancedTensor
end

end Enriched

/-! ## EnrichedHomAdjunction（旧 SerrePositivity/DifferentialGraded/Tensor/EnrichedHomAdjunction.lean） -/

/-! # パラメータ複体を持つtensor–Hom同値 -/

@[expose] public section EnrichedHomAdjunction
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory MonoidalCategory Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

/-- パラメータ付きbalanced族と右Hom加群への豊穣自然変換の同値。 -/
def paramTransEquiv (K : Complex A) (M : RightModule A D) (N : LeftModule A D)
    (T : Complex A) :
    ParamFamily A D M N K T ≃ ModuleParamTrans A D K M (homRightModule A D N T) :=
  (paramTensorFamilyEquiv A D K M N T).trans
    ((balancedFamilyMapEquiv A D (tensorModule K M) N T).trans
      (tensorFamilyEquiv A K M (homRightModule A D N T)))

lemma paramTransEquiv_app (K : Complex A) (M : RightModule A D) (N : LeftModule A D)
    (T : Complex A) (a : ParamFamily A D M N K T) (x : D) :
    (paramTransEquiv A D K M N T a).app (op x) =
      curryRight (curryRight ((α_ K (M.obj (op x)) (N.obj x)).hom ≫ a.val x)) := rfl

variable [Small.{u} D]

/-- 任意Kからの射についての主Hom複体のtensor–Hom同値。 -/
def enrichedTensorHomEquiv (K : Complex A) (M : RightModule A D) (N : LeftModule A D)
    (T : Complex A) :
    (K ⟶ homComplex A (obj A D M N) T) ≃ (K ⟶ moduleHom A D M (homRightModule A D N T)) :=
  (tensorRightHomEquiv (obj A D M N) K T).symm.trans
    ((paramHomEquiv A D M N K T).trans
      ((paramTransEquiv A D K M N T).trans
        (moduleHomEquiv A D K M (homRightModule A D N T)).symm))

@[reassoc]
lemma enrichedTensorHomEquiv_π (K : Complex A) (M : RightModule A D) (N : LeftModule A D)
    (T : Complex A) (f : K ⟶ homComplex A (obj A D M N) T) (x : D) :
    enrichedTensorHomEquiv A D K M N T f ≫ moduleHomπ A D M (homRightModule A D N T) x =
      curryRight (curryRight ((α_ K (M.obj (op x)) (N.obj x)).hom ≫
        ((K ◁ ι A D M N x) ≫ uncurryRight f))) :=
  moduleHomEquiv_symm_π A D K M (homRightModule A D N T)
    (paramTransEquiv A D K M N T (paramRestrict A D M N (uncurryRight f))) x

lemma enrichedTensorHomEquiv_naturality_param {K L : Complex A} (M : RightModule A D)
    (N : LeftModule A D) (T : Complex A) (g : L ⟶ K)
    (f : K ⟶ homComplex A (obj A D M N) T) :
    enrichedTensorHomEquiv A D L M N T (g ≫ f) =
      g ≫ enrichedTensorHomEquiv A D K M N T f := by
  apply moduleHom_ext
  intro x
  rw [Category.assoc, enrichedTensorHomEquiv_π, enrichedTensorHomEquiv_π,
    curryRight_twice_precompose, uncurryRight_precompose]
  congr 2
  rw [associator_naturality_left_assoc, whisker_exchange_assoc]

/-- balanced tensorのHomと右Hom加群の主Hom endとの実際のchain iso。 -/
def enrichedTensorHomIso (M : RightModule A D) (N : LeftModule A D) (T : Complex A) :
    homComplex A (obj A D M N) T ≅ moduleHom A D M (homRightModule A D N T) where
  hom := enrichedTensorHomEquiv A D _ M N T (𝟙 _)
  inv := (enrichedTensorHomEquiv A D _ M N T).symm (𝟙 _)
  hom_inv_id := by
    apply (enrichedTensorHomEquiv A D _ M N T).injective
    rw [enrichedTensorHomEquiv_naturality_param, Equiv.apply_symm_apply, Category.comp_id]
  inv_hom_id := by
    have h := enrichedTensorHomEquiv_naturality_param A D M N T
      ((enrichedTensorHomEquiv A D _ M N T).symm (𝟙 _)) (𝟙 _)
    rw [Category.comp_id, Equiv.apply_symm_apply] at h
    exact h.symm

lemma enrichedTensorHomEquiv_eq_comp (K : Complex A) (M : RightModule A D)
    (N : LeftModule A D) (T : Complex A) (f : K ⟶ homComplex A (obj A D M N) T) :
    enrichedTensorHomEquiv A D K M N T f = f ≫ (enrichedTensorHomIso A D M N T).hom := by
  have h := enrichedTensorHomEquiv_naturality_param A D M N T f (𝟙 _)
  rw [Category.comp_id] at h
  exact h

end SerrePositivity.DifferentialGraded.BalancedTensor
end

end EnrichedHomAdjunction

/-! ## EnrichedHomPoints（旧 SerrePositivity/DifferentialGraded/Tensor/EnrichedHomPoints.lean） -/

/-! # 豊穣tensor–Hom同型と閉零tensor–Hom随伴の一致 -/

@[expose] public section EnrichedHomPoints
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory MonoidalCategory Opposite
variable (A : Type u) [CommRing A]

lemma curryRight_twice_unit {P Q S T : Complex A} (i : P ⊗ Q ⟶ S) (f : S ⟶ T) :
    curryRight (curryRight ((α_ (𝟙_ (Complex A)) P Q).hom ≫
      (((𝟙_ (Complex A)) ◁ i) ≫ uncurryRight (closedMap A f)))) =
      closedMap A (curryRight (i ≫ f)) := by
  rw [uncurryRight_closedMap]
  rw [leftUnitor_naturality_assoc, leftUnitor_tensor_hom]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  change curryRight (curryRight (((λ_ P).hom ⊗ₘ 𝟙 Q) ≫ (i ≫ f))) = _
  rw [curryRight_naturality_source, ← uncurryRight_closedMap, curryRight_uncurryRight]

variable (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 単位複体からの閉零射で豊穣同型を評価すると、先行する通常随伴の転置と一致する。 -/
lemma enrichedTensorHomEquiv_closedMap (M : ModuleCategory A D) (N : LeftModule A D)
    (T : Complex A) (f : obj A D (ForgetEnrichment.to (Complex A) M) N ⟶ T) :
    enrichedTensorHomEquiv A D (𝟙_ (Complex A)) (ForgetEnrichment.to (Complex A) M) N T
      (closedMap A f) =
    ForgetEnrichment.homTo (Complex A) (C := RightModule A D)
      (X := ForgetEnrichment.to (Complex A) M) (Y := homRightModule A D N T)
      (tensorHomEquiv A D M N T f) := by
  apply moduleHom_ext
  intro x
  rw [enrichedTensorHomEquiv_π]
  have h := moduleEvaluation_closedMap A D x (tensorHomEquiv A D M N T f)
  rw [tensorHomEquiv_eval] at h
  exact (curryRight_twice_unit A _ f).trans h

end SerrePositivity.DifferentialGraded.BalancedTensor
end

end EnrichedHomPoints

/-! ## EnrichedHomElements（旧 SerrePositivity/DifferentialGraded/Tensor/EnrichedHomElements.lean） -/

/-! # 豊穣tensor–Hom同型の斉次要素での評価 -/

@[expose] public section EnrichedHomElements
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma enrichedTensorHomIso_hom_element (M : RightModule A D) (N : LeftModule A D)
    (T : Complex A) (x : D) {k r l s n : ℤ} (hl : r + k = l) (hn : s + l = n)
    (f : Homogeneous (obj A D M N) T k) (m : (M.obj (op x)).X r) (v : (N.obj x).X s) :
    (((moduleHomπ A D M (homRightModule A D N T) x).f k
      ((enrichedTensorHomIso A D M N T).hom.f k f)).v r l hl m).v s n hn v =
    f.v (r + s) n (by omega) (element A D M N x m v rfl) := by
  have hp := enrichedTensorHomEquiv_π A D (homComplex A (obj A D M N) T) M N T (𝟙 _) x
  have he := congrArg (fun h => ((h.f k f).v r l hl m).v s n hn v) hp
  change (((moduleHomπ A D M (homRightModule A D N T) x).f k
      ((enrichedTensorHomIso A D M N T).hom.f k f)).v r l hl m).v s n hn v = _ at he
  exact he.trans (curryRight_associator_apply (ι A D M N x) (𝟙 _) hl hn f m v)

end SerrePositivity.DifferentialGraded.BalancedTensor
end

end EnrichedHomElements

/-! ## EnrichedHomLeft（旧 SerrePositivity/DifferentialGraded/Tensor/EnrichedHomLeft.lean） -/

/-! # 豊穣tensor–Hom同型の左加群Hom変数の自然性 -/

@[expose] public section EnrichedHomLeft
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 左加群Nの全Homについて、豊穣転置は右Hom加群の反変作用と整合する。 -/
lemma enrichedTensorHomIso_left_naturality (M : RightModule A D) (N N' : LeftModule A D)
    (T : Complex A) :
    (leftHomMap A D M N N' ≫ (homContravariantDG A T).map
      (op (obj A D M N')) (op (obj A D M N))) ≫
      homPostcompose (homComplex A (obj A D M N') T) (enrichedTensorHomIso A D M N T).hom =
    (homRightContraHomMap A D N N' T ≫ modulePostcompositionMap A D M
      (homRightModule A D N' T) (homRightModule A D N T)) ≫
      homPrecompose (enrichedTensorHomIso A D M N' T).hom
        (moduleHom A D M (homRightModule A D N T)) := by
  apply HomologicalComplex.hom_ext
  intro p
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro σ
  change (homPostcompose _ (enrichedTensorHomIso A D M N T).hom).f p
      (((homContravariantDG A T).map (op (obj A D M N')) (op (obj A D M N))).f p
        ((leftHomMap A D M N N').f p σ)) =
    (homPrecompose (enrichedTensorHomIso A D M N' T).hom _).f p
      ((modulePostcompositionMap A D M (homRightModule A D N' T)
        (homRightModule A D N T)).f p ((homRightContraHomMap A D N N' T).f p σ))
  rw [homPostcompose_apply, homPrecompose_apply]
  apply Cochain.ext
  intro q n hn
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  change Homogeneous (obj A D M N') T q at f
  rw [Cochain.comp_zero_cochain_v, Cochain.zero_cochain_comp_v,
    Cochain.ofHom_v, Cochain.ofHom_v]
  change (enrichedTensorHomIso A D M N T).hom.f n
      ((((homContravariantDG A T).map (op (obj A D M N')) (op (obj A D M N))).f p
        ((leftHomMap A D M N N').f p σ)).v q n hn f) =
    (((modulePostcompositionMap A D M (homRightModule A D N' T)
      (homRightModule A D N T)).f p ((homRightContraHomMap A D N N' T).f p σ)).v q n hn)
      ((enrichedTensorHomIso A D M N' T).hom.f q f)
  rw [homContravariantDG_map_element, modulePostcompositionMap_apply]
  simp only [Units.smul_def, map_zsmul]
  change (p * q).negOnePow • (enrichedTensorHomIso A D M N T).hom.f n
      (((leftHomMap A D M N N').f p σ).comp f (by omega)) =
    compose A (D := RightModule A D) ((homRightContraHomMap A D N N' T).f p σ)
      ((enrichedTensorHomIso A D M N' T).hom.f q f) hn
  apply moduleHomElement_ext A D
  intro x
  simp only [Units.smul_def, map_zsmul]
  rw [moduleHomCompose_π]
  change (p * q).negOnePow •
      (moduleHomπ A D M (homRightModule A D N T) x).f n
        ((enrichedTensorHomIso A D M N T).hom.f n
          (((leftHomMap A D M N N').f p σ).comp f (by omega))) =
    ((moduleHomπ A D M (homRightModule A D N' T) x).f q
      ((enrichedTensorHomIso A D M N' T).hom.f q f)).comp
      ((moduleHomπ A D (homRightModule A D N' T) (homRightModule A D N T) x).f p
        ((homRightContraHomMap A D N N' T).f p σ)) hn
  apply Cochain.ext
  intro r l hl
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  rw [Cochain.units_smul_v, Cochain.comp_v _ _ hn r (r + q) l rfl (by omega)]
  change (p * q).negOnePow •
      (((moduleHomπ A D M (homRightModule A D N T) x).f n
        ((enrichedTensorHomIso A D M N T).hom.f n
          (((leftHomMap A D M N N').f p σ).comp f (by omega)))).v r l hl m) =
    (((moduleHomπ A D (homRightModule A D N' T) (homRightModule A D N T) x).f p
      ((homRightContraHomMap A D N N' T).f p σ)).v (r + q) l (by omega))
      (((moduleHomπ A D M (homRightModule A D N' T) x).f q
        ((enrichedTensorHomIso A D M N' T).hom.f q f)).v r (r + q) rfl m)
  apply Cochain.ext
  intro s a ha
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro v
  change (N.obj x).X s at v
  rw [Cochain.units_smul_v, homRightContraHomMap_element, Cochain.units_smul_v]
  change (p * q).negOnePow •
      ((((moduleHomπ A D M (homRightModule A D N T) x).f n
        ((enrichedTensorHomIso A D M N T).hom.f n
          (((leftHomMap A D M N N').f p σ).comp f (by omega)))).v r l hl m).v s a ha v) =
    (p * (r + q)).negOnePow •
      ((((leftModuleHomπ A D N N' x).f p σ).comp
        (((moduleHomπ A D M (homRightModule A D N' T) x).f q
          ((enrichedTensorHomIso A D M N' T).hom.f q f)).v r (r + q) rfl m)
        (by omega)).v s a ha v)
  rw [enrichedTensorHomIso_hom_element]
  rw [Cochain.comp_v _ f (by omega : p + q = n) (r + s) (r + (p + s)) a
    (by omega) (by omega), Cochain.comp_v _ _ (by omega : p + (r + q) = l) s (p + s) a
      (by omega) (by omega)]
  simp only [ModuleCat.comp_apply]
  rw [leftHomMap_element_of_sum A D M (l := p + s) σ x m v rfl rfl (by omega)]
  have he := enrichedTensorHomIso_hom_element A D M N' T x (k := q) (r := r)
    (l := r + q) (s := p + s) (n := a) rfl (by omega) f m
    (((leftModuleHomπ A D N N' x).f p σ).v s (p + s) (by omega) v)
  refine Eq.trans ?_ (congrArg (fun z => (p * (r + q)).negOnePow • z) he).symm
  simp only [Units.smul_def, map_zsmul]
  change (p * q).negOnePow • ((p * r).negOnePow •
      f.v (r + (p + s)) a (by omega)
        (element A D M N' x m (((leftModuleHomπ A D N N' x).f p σ).v s (p + s) (by omega) v)
          rfl)) =
    (p * (r + q)).negOnePow • f.v (r + (p + s)) a (by omega)
      (element A D M N' x m (((leftModuleHomπ A D N N' x).f p σ).v s (p + s) (by omega) v) rfl)
  rw [smul_smul, ← Int.negOnePow_add]
  have hs : p * q + p * r = p * (r + q) := by ring
  rw [hs]

end SerrePositivity.DifferentialGraded.BalancedTensor
end

end EnrichedHomLeft

/-! ## EnrichedHomTarget（旧 SerrePositivity/DifferentialGraded/Tensor/EnrichedHomTarget.lean） -/

/-! # 豊穣tensor–Hom同型の終域Hom変数の自然性 -/

@[expose] public section EnrichedHomTarget
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 終域Tの全Hom作用について、豊穣転置は後合成を保つ。 -/
lemma enrichedTensorHomIso_target_naturality (M : RightModule A D) (N : LeftModule A D)
    (T T' : Complex A) :
    (homCovariantDG A (obj A D M N)).map T T' ≫
      homPostcompose (homComplex A (obj A D M N) T) (enrichedTensorHomIso A D M N T').hom =
    (homRightHomMap A D N T T' ≫ modulePostcompositionMap A D M
      (homRightModule A D N T) (homRightModule A D N T')) ≫
      homPrecompose (enrichedTensorHomIso A D M N T).hom
        (moduleHom A D M (homRightModule A D N T')) := by
  apply HomologicalComplex.hom_ext
  intro p
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro t
  change (homPostcompose _ (enrichedTensorHomIso A D M N T').hom).f p
      (((homCovariantDG A (obj A D M N)).map T T').f p t) =
    (homPrecompose (enrichedTensorHomIso A D M N T).hom _).f p
      ((modulePostcompositionMap A D M (homRightModule A D N T)
        (homRightModule A D N T')).f p ((homRightHomMap A D N T T').f p t))
  rw [homPostcompose_apply, homPrecompose_apply]
  apply Cochain.ext
  intro q n hn
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  rw [Cochain.comp_zero_cochain_v, Cochain.zero_cochain_comp_v,
    Cochain.ofHom_v, Cochain.ofHom_v]
  change (enrichedTensorHomIso A D M N T').hom.f n
      ((((homCovariantDG A (obj A D M N)).map T T').f p t).v q n hn f) =
    (((modulePostcompositionMap A D M (homRightModule A D N T)
      (homRightModule A D N T')).f p ((homRightHomMap A D N T T').f p t)).v q n hn)
        ((enrichedTensorHomIso A D M N T).hom.f q f)
  rw [homCovariantDG_map_element, modulePostcompositionMap_apply]
  apply moduleHomElement_ext A D
  intro x
  rw [moduleHomCompose_π]
  apply Cochain.ext
  intro r l hl
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  rw [Cochain.comp_v _ _ hn r (r + q) l rfl (by omega)]
  simp only [ModuleCat.comp_apply]
  apply Cochain.ext
  intro s a ha
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro v
  rw [enrichedTensorHomIso_hom_element, homRightHomMap_element]
  rw [Cochain.comp_v f t hn (r + s) (r + s + q) a rfl (by omega)]
  rw [Cochain.comp_v _ t (by omega) s (r + s + q) a (by omega) (by omega)]
  simp only [ModuleCat.comp_apply]
  rw [enrichedTensorHomIso_hom_element]
  rfl

end SerrePositivity.DifferentialGraded.BalancedTensor
end

end EnrichedHomTarget

/-! ## EnrichedHomSource（旧 SerrePositivity/DifferentialGraded/Tensor/EnrichedHomSource.lean） -/

/-! # 豊穣tensor–Hom同型の右加群Hom変数の反変自然性 -/

@[expose] public section EnrichedHomSource
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 右加群Mの全Homについて、豊穣転置は符号付き前合成を保つ。 -/
lemma enrichedTensorHomIso_source_naturality (M M' : RightModule A D) (N : LeftModule A D)
    (T : Complex A) :
    (rightHomMap A D M M' N ≫ (homContravariantDG A T).map
      (op (obj A D M' N)) (op (obj A D M N))) ≫
      homPostcompose (homComplex A (obj A D M' N) T) (enrichedTensorHomIso A D M N T).hom =
    modulePrecompositionMap A D M M' (homRightModule A D N T) ≫
      homPrecompose (enrichedTensorHomIso A D M' N T).hom
        (moduleHom A D M (homRightModule A D N T)) := by
  apply HomologicalComplex.hom_ext
  intro p
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro σ
  change (homPostcompose _ (enrichedTensorHomIso A D M N T).hom).f p
      (((homContravariantDG A T).map (op (obj A D M' N)) (op (obj A D M N))).f p
        ((rightHomMap A D M M' N).f p σ)) =
    (homPrecompose (enrichedTensorHomIso A D M' N T).hom _).f p
      ((modulePrecompositionMap A D M M' (homRightModule A D N T)).f p σ)
  rw [homPostcompose_apply, homPrecompose_apply]
  apply Cochain.ext
  intro q n hn
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  rw [Cochain.comp_zero_cochain_v, Cochain.zero_cochain_comp_v,
    Cochain.ofHom_v, Cochain.ofHom_v]
  change (enrichedTensorHomIso A D M N T).hom.f n
      ((((homContravariantDG A T).map (op (obj A D M' N)) (op (obj A D M N))).f p
        ((rightHomMap A D M M' N).f p σ)).v q n hn f) =
    ((modulePrecompositionMap A D M M' (homRightModule A D N T)).f p σ).v q n hn
      ((enrichedTensorHomIso A D M' N T).hom.f q f)
  rw [homContravariantDG_map_element, modulePrecompositionMap_apply]
  simp only [Units.smul_def, map_zsmul]
  change (p * q).negOnePow • (enrichedTensorHomIso A D M N T).hom.f n
      (((rightHomMap A D M M' N).f p σ).comp f (by omega)) =
    forward A (D := RightModule A D) σ ((enrichedTensorHomIso A D M' N T).hom.f q f)
      (by omega)
  apply moduleHomElement_ext A D
  intro x
  simp only [Units.smul_def, map_zsmul]
  rw [moduleHomForward_π]
  change (p * q).negOnePow •
      (moduleHomπ A D M (homRightModule A D N T) x).f n
        ((enrichedTensorHomIso A D M N T).hom.f n
          (((rightHomMap A D M M' N).f p σ).comp f (by omega))) =
    (p * q).negOnePow • (((moduleHomπ A D M M' x).f p σ).comp
      ((moduleHomπ A D M' (homRightModule A D N T) x).f q
        ((enrichedTensorHomIso A D M' N T).hom.f q f)) (by omega))
  congr 1
  apply Cochain.ext
  intro r l hl
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  rw [Cochain.comp_v _ _ (by omega : p + q = n) r (r + p) l rfl (by omega)]
  simp only [ModuleCat.comp_apply]
  apply Cochain.ext
  intro s a ha
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro v
  rw [enrichedTensorHomIso_hom_element, enrichedTensorHomIso_hom_element]
  rw [Cochain.comp_v _ f (by omega : p + q = n) (r + s) (r + p + s) a (by omega) (by omega)]
  simp only [ModuleCat.comp_apply]
  rw [rightHomMap_element_of_sum A D N (l := r + p) σ x m v rfl (by omega) (by omega)]

end SerrePositivity.DifferentialGraded.BalancedTensor
end

end EnrichedHomSource

/-! ## Interchange（旧 SerrePositivity/DifferentialGraded/Tensor/Interchange.lean） -/

/-! # balanced tensorの左右作用の全次数交換則 -/

@[expose] public section Interchange
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 左右のHom作用を交換する際の符号は二つのHom次数の積。 -/
lemma homMaps_interchange {M M' : RightModule A D} {N N' : LeftModule A D} {p q k : ℤ}
    (τ : (moduleHom A D M M').X p) (σ : (leftModuleHom A D N N').X q) (hk : p + q = k) :
    (((rightHomMap A D M M' N).f p τ).comp ((leftHomMap A D M' N N').f q σ) hk) =
    (p * q).negOnePow • (((leftHomMap A D M N N').f q σ).comp
      ((rightHomMap A D M M' N').f p τ) (by omega)) := by
  apply cochain_element_ext A D M N
  intro x r s a n ha hn m v
  rw [Cochain.comp_v _ _ hk a (p + r + s) n (by omega) (by omega),
    Cochain.units_smul_v,
    Cochain.comp_v _ _ (by omega) a (r + (q + s)) n (by omega) (by omega)]
  change (((leftHomMap A D M' N N').f q σ).v (p + r + s) n (by omega)
      ((((rightHomMap A D M M' N).f p τ).v a (p + r + s) (by omega))
        (element A D M N x m v ha))) =
    (p * q).negOnePow • (((rightHomMap A D M M' N').f p τ).v (r + (q + s)) n
      (by omega) ((((leftHomMap A D M N N').f q σ).v a (r + (q + s)) (by omega))
        (element A D M N x m v ha)))
  rw [rightHomMap_element_of_sum A D N τ x m v ha rfl (by omega),
    leftHomMap_element_of_sum A D M' σ x _ v rfl rfl (by omega),
    leftHomMap_element_of_sum A D M σ x m v ha rfl (by omega)]
  simp only [Units.smul_def, map_zsmul]
  change (q * (p + r)).negOnePow •
      element A D M' N' x
        (((moduleHomπ A D M M' x).f p τ).v r (p + r) (by omega) m)
        (((leftModuleHomπ A D N N' x).f q σ).v s (q + s) (by omega) v) (by omega) =
    (p * q).negOnePow • ((q * r).negOnePow •
      (((rightHomMap A D M M' N').f p τ).v (r + (q + s)) n (by omega)
        (element A D M N' x m
          (((leftModuleHomπ A D N N' x).f q σ).v s (q + s) (by omega) v) rfl)))
  rw [rightHomMap_element_of_sum A D N' τ x m _ rfl rfl (by omega)]
  simp only [smul_smul, ← Int.negOnePow_add]
  congr 1
  congr 1
  ring

end SerrePositivity.DifferentialGraded.BalancedTensor
end

end Interchange

/-! ## LeftColimits（旧 SerrePositivity/DifferentialGraded/Tensor/LeftColimits.lean） -/

/-! # balanced tensorの左加群変数における余極限保存 -/

@[expose] public section LeftColimits
universe u v w t

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory MonoidalCategory Opposite Limits
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 固定右加群とのbalanced tensorを閉零左加群圏上の関手にする。 -/
def leftTensorFunctor (M : RightModule A D) : LeftModuleCategory A D ⥤ Complex A where
  obj N := obj A D M (ForgetEnrichment.to (Complex A) N)
  map g := map A D (𝟙 (ForgetEnrichment.of (Complex A) M)) g
  map_id N := map_id A D (ForgetEnrichment.of (Complex A) M) N
  map_comp f g := by
    simpa only [Category.id_comp] using
      map_comp A D (𝟙 (ForgetEnrichment.of (Complex A) M))
        (𝟙 (ForgetEnrichment.of (Complex A) M)) f g

/-- 左加群変数のtensorは、oppositeでの右加群変数のtensorと自然同型。 -/
def leftTensorSwapIso (M : RightModule A D) :
    leftTensorFunctor A D M ≅
      leftModuleToRightOpposite A D ⋙ rightTensorFunctor A Dᵒᵖ M.toFunctor :=
  NatIso.ofComponents (fun N => swapIso A D M (ForgetEnrichment.to (Complex A) N))
    (fun g => swapHom_naturality_left A D M g)

/-- 存在する任意サイズの余極限を左加群変数でも保存する。 -/
instance leftTensorFunctor_preservesColimits (M : RightModule A D) :
    PreservesColimitsOfSize.{w, t} (leftTensorFunctor A D M) :=
  preservesColimits_of_natIso (leftTensorSwapIso A D M).symm

end SerrePositivity.DifferentialGraded.BalancedTensor
end

end LeftColimits

/-! ## BoundedAbove（旧 SerrePositivity/DifferentialGraded/Tensor/BoundedAbove.lean） -/

/-! # 上に有界なflat複体の非有界相手に対するK-flat性 -/

@[expose] public section BoundedAbove
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits HomologicalComplex
variable (A : Type u) [CommRing A]

/-- 上に有界な次数ごとflat複体は、任意の非有界acyclic複体とのtensorで消える。 -/
lemma complexKFlat_of_flat_boundedAbove (K : Complex A) (b : ℤ)
    (hb : ∀ i, b < i → IsZero (K.X i)) (hflat : ∀ i, Module.Flat A (K.X i)) :
    complexKFlat A K := by
  have hstage (n : ℕ) : complexKFlat A ((lowerTruncationSequence A K).obj n) := by
    change complexKFlat A (StupidTruncation.above K (-(n : ℤ)))
    apply complexKFlat_of_flat_bounds A _ (-(n : ℤ)) b
    · intro i hi
      exact StupidTruncation.above_isZero_X K _ i hi
    · intro i hi
      by_cases hni : -(n : ℤ) ≤ i
      · exact (StupidTruncation.aboveXIso K _ i hni).isZero_iff.mpr (hb i hi)
      · exact StupidTruncation.above_isZero_X K _ i (by omega)
    · intro i
      by_cases hni : -(n : ℤ) ≤ i
      · have := hflat i
        exact Module.Flat.of_linearEquiv
          (StupidTruncation.aboveXIso K _ i hni).toLinearEquiv
      · have := ModuleCat.subsingleton_of_isZero
          (StupidTruncation.above_isZero_X K (-(n : ℤ)) i (by omega))
        infer_instance
  have : AB5OfSize.{0, 0} (ModuleCat.{u} A) := AB5OfSize_of_univLE (ModuleCat.{u} A)
  exact complexKFlat_of_iso A (lowerTruncationColimitIso A K).symm
    (complexKFlat_colimit A (lowerTruncationSequence A K) hstage)

/-- 上に有界flatな左因子は、相手の有界性なしに任意の準同型を保存する。 -/
lemma complexTensor_quasiIso_right_of_flat_boundedAbove (K : Complex A) (b : ℤ)
    (hb : ∀ i, b < i → IsZero (K.X i)) (hflat : ∀ i, Module.Flat A (K.X i))
    {L L' : Complex A} (f : L ⟶ L') [QuasiIso f] :
    QuasiIso (cochainTensorMap (𝟙 K) f) :=
  complexKFlat_quasiIso_right A (complexKFlat_of_flat_boundedAbove A K b hb hflat) f

/-- 上に有界flatな右因子でも、相手の有界性なしに任意の準同型を保存する。 -/
lemma complexTensor_quasiIso_left_of_flat_boundedAbove (K : Complex A) (b : ℤ)
    (hb : ∀ i, b < i → IsZero (K.X i)) (hflat : ∀ i, Module.Flat A (K.X i))
    {L L' : Complex A} (f : L ⟶ L') [QuasiIso f] :
    QuasiIso (cochainTensorMap f (𝟙 K)) :=
  complexKFlat_quasiIso_left A (complexKFlat_of_flat_boundedAbove A K b hb hflat) f

end SerrePositivity.DifferentialGraded
end

end BoundedAbove

/-! ## YonedaEnriched（旧 SerrePositivity/DifferentialGraded/Tensor/YonedaEnriched.lean） -/

/-! # balanced tensorのYoneda評価の主Homに関する自然性 -/

@[expose] public section YonedaEnriched
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 右representableのYoneda評価は主Hom複体全体に関して自然。 -/
lemma yonedaEvaluation_enriched_naturality (z : D) (N N' : LeftModule A D) :
    leftHomMap A D (representable A z) N N' ≫
      homPostcompose (obj A D (representable A z) N) (yonedaEvaluation A D z N') =
    leftModuleHomπ A D N N' z ≫
      homPrecompose (yonedaEvaluation A D z N) (N'.obj z) := by
  apply HomologicalComplex.hom_ext
  intro q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro τ
  change (homPostcompose _ (yonedaEvaluation A D z N')).f q
      ((leftHomMap A D (representable A z) N N').f q τ) =
    (homPrecompose (yonedaEvaluation A D z N) _).f q ((leftModuleHomπ A D N N' z).f q τ)
  rw [homPostcompose_apply, homPrecompose_apply]
  apply cochain_element_ext A D (representable A z) N
  intro x p r a n ha hn f m
  rw [Cochain.comp_zero_cochain_v, Cochain.zero_cochain_comp_v, Cochain.ofHom_v,
    Cochain.ofHom_v]
  change (yonedaEvaluation A D z N').f n
      (((leftHomMap A D (representable A z) N N').f q τ).v a n hn
        (element A D (representable A z) N x f m ha)) =
    ((leftModuleHomπ A D N N' z).f q τ).v a n hn
      ((yonedaEvaluation A D z N).f a (element A D (representable A z) N x f m ha))
  rw [leftHomMap_element_of_sum A D (representable A z) τ x f m ha rfl hn]
  simp only [Units.smul_def, map_zsmul]
  exact (yonedaEvaluation_homElement A D τ z x f m ha (by omega) hn).symm

/-- 左representableのYoneda評価も主Hom複体全体に関して自然。 -/
lemma leftYonedaEvaluation_enriched_naturality (z : D) (M M' : RightModule A D) :
    rightHomMap A D M M' (leftRepresentable A z) ≫
      homPostcompose (obj A D M (leftRepresentable A z)) (leftYonedaEvaluation A D z M') =
    moduleHomπ A D M M' z ≫
      homPrecompose (leftYonedaEvaluation A D z M) (M'.obj (op z)) := by
  apply HomologicalComplex.hom_ext
  intro q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro τ
  change (homPostcompose _ (leftYonedaEvaluation A D z M')).f q
      ((rightHomMap A D M M' (leftRepresentable A z)).f q τ) =
    (homPrecompose (leftYonedaEvaluation A D z M) _).f q ((moduleHomπ A D M M' z).f q τ)
  rw [homPostcompose_apply, homPrecompose_apply]
  apply cochain_element_ext A D M (leftRepresentable A z)
  intro x r p a n ha hn m f
  rw [Cochain.comp_zero_cochain_v, Cochain.zero_cochain_comp_v, Cochain.ofHom_v,
    Cochain.ofHom_v]
  change (leftYonedaEvaluation A D z M').f n
      (((rightHomMap A D M M' (leftRepresentable A z)).f q τ).v a n hn
        (element A D M (leftRepresentable A z) x m f ha)) =
    ((moduleHomπ A D M M' z).f q τ).v a n hn
      ((leftYonedaEvaluation A D z M).f a (element A D M (leftRepresentable A z) x m f ha))
  rw [rightHomMap_element_of_sum A D (leftRepresentable A z) τ x m f ha rfl hn]
  exact (leftYonedaEvaluation_homElement A D τ z x m f ha (by omega) hn).symm

end SerrePositivity.DifferentialGraded.BalancedTensor
end

end YonedaEnriched

/-! ## YonedaRepresentative（旧 SerrePositivity/DifferentialGraded/Tensor/YonedaRepresentative.lean） -/

/-! # 代表対象を動かすYoneda tensor評価の全Hom自然性 -/

@[expose] public section YonedaRepresentative
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma yonedaEvaluation_representative_naturality (N : LeftModule A D) (z z' : D) :
    yonedaHom A D z z' ≫ rightHomMap A D (representable A z) (representable A z') N ≫
      homPostcompose (obj A D (representable A z) N) (yonedaEvaluation A D z' N) =
    N.map z z' ≫ homPrecompose (yonedaEvaluation A D z N) (N.obj z') := by
  apply HomologicalComplex.hom_ext
  intro k
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  change (homPostcompose _ (yonedaEvaluation A D z' N)).f k
      ((rightHomMap A D (representable A z) (representable A z') N).f k
        ((yonedaHom A D z z').f k f)) =
    (homPrecompose (yonedaEvaluation A D z N) _).f k ((N.map z z').f k f)
  rw [homPostcompose_apply, homPrecompose_apply]
  apply cochain_element_ext A D (representable A z) N
  intro x r s a n ha hn h m
  rw [Cochain.comp_zero_cochain_v, Cochain.zero_cochain_comp_v, Cochain.ofHom_v,
    Cochain.ofHom_v]
  change (yonedaEvaluation A D z' N).f n
      (((rightHomMap A D (representable A z) (representable A z') N).f k
        ((yonedaHom A D z z').f k f)).v a n hn
          (element A D (representable A z) N x h m ha)) =
    ((N.map z z').f k f).v a n hn
      ((yonedaEvaluation A D z N).f a (element A D (representable A z) N x h m ha))
  rw [rightHomMap_element_of_sum A D N _ x h m ha rfl hn, yonedaHom_element,
    yonedaEvaluation_element, yonedaEvaluation_element]
  have hs : SerrePositivity.DifferentialGraded.leftAction A N (n := n)
      ((k * r).negOnePow • forward A h f (show r + k = k + r by omega)) m (by omega) =
    (k * r).negOnePow • SerrePositivity.DifferentialGraded.leftAction A N (n := n)
      (forward A h f (show r + k = k + r by omega)) m (by omega) := by
    simp only [SerrePositivity.DifferentialGraded.leftAction, Units.smul_def, map_zsmul]
    rfl
  rw [hs, SerrePositivity.DifferentialGraded.leftAction_forward A N h f m
    (show r + k = k + r by omega) (show s + r = a by omega) (by omega)]
  rw [mul_comm r k, smul_smul, Int.units_mul_self, one_smul]
  rfl

lemma leftYonedaEvaluation_representative_naturality (M : RightModule A D) (z z' : D) :
    leftYonedaHom A D z z' ≫ leftHomMap A D M (leftRepresentable A z) (leftRepresentable A z') ≫
      homPostcompose (obj A D M (leftRepresentable A z)) (leftYonedaEvaluation A D z' M) =
    M.map (op z) (op z') ≫
      homPrecompose (leftYonedaEvaluation A D z M) (M.obj (op z')) := by
  apply HomologicalComplex.hom_ext
  intro p
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  change (homPostcompose _ (leftYonedaEvaluation A D z' M)).f p
      ((leftHomMap A D M (leftRepresentable A z) (leftRepresentable A z')).f p
        ((leftYonedaHom A D z z').f p f)) =
    (homPrecompose (leftYonedaEvaluation A D z M) _).f p ((M.map (op z) (op z')).f p f)
  rw [homPostcompose_apply, homPrecompose_apply]
  apply cochain_element_ext A D M (leftRepresentable A z)
  intro x r s a n ha hn m h
  rw [Cochain.comp_zero_cochain_v, Cochain.zero_cochain_comp_v, Cochain.ofHom_v,
    Cochain.ofHom_v]
  change (leftYonedaEvaluation A D z' M).f n
      (((leftHomMap A D M (leftRepresentable A z) (leftRepresentable A z')).f p
        ((leftYonedaHom A D z z').f p f)).v a n hn
          (element A D M (leftRepresentable A z) x m h ha)) =
    ((M.map (op z) (op z')).f p f).v a n hn
      ((leftYonedaEvaluation A D z M).f a (element A D M (leftRepresentable A z) x m h ha))
  rw [leftHomMap_element_of_sum A D M _ x m h ha rfl hn, leftYonedaHom_element]
  simp only [Units.smul_def, map_zsmul]
  rw [leftYonedaEvaluation_element, leftYonedaEvaluation_element]
  simp only [Units.smul_def, map_zsmul]
  change (p * r).negOnePow • ((r * (p + s)).negOnePow •
      moduleAction A M (x := op x) (y := op z')
        (forward A (D := D) (x := z') (y := z) (z := x) f h (by omega)) m (by omega)) =
    (r * s).negOnePow • moduleAction A M f (moduleAction A M h m ha) hn
  have hc := moduleAction_representable A x M (op z) (op z') p s r (p + s) n a
    (by omega) ha (by omega) f h m
  change moduleAction A M (x := op x) (y := op z')
    (forward A (D := D) (x := z') (y := z) (z := x) f h (by omega)) m (by omega) = _ at hc
  rw [hc]
  simp only [smul_smul, ← Int.negOnePow_add]
  have hs : p * r + r * (p + s) = r * s + 2 * (p * r) := by ring
  rw [hs, Int.negOnePow_add, Int.negOnePow_two_mul, mul_one]

end SerrePositivity.DifferentialGraded.BalancedTensor
end

end YonedaRepresentative

/-! ## FreeEvaluation（旧 SerrePositivity/DifferentialGraded/Tensor/FreeEvaluation.lean） -/

/-! # 自由dg加群とのbalanced tensorの評価

free/evaluationとtensor/Homの随伴を合成し、同じ右随伴を持つ左随伴の一意性を使う。
-/

@[expose] public section FreeEvaluation
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory Limits MonoidalCategory Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 右Hom加群をxで評価すると既存のHom複体関手になる。 -/
def homRightEvaluationIso (N : LeftModule A D) (x : D) :
    homRightFunctor A D N ⋙ moduleEvaluation A D x ≅ homFunctor (N.obj x) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro T T' g
    change (moduleEvaluation A D x).map (homRightModuleMap A D N g) ≫ 𝟙 _ =
      𝟙 _ ≫ homPostcompose (N.obj x) g
    simpa only [Category.comp_id, Category.id_comp] using homRightModuleMap_eval A D N g x)

/-- 自由加群とのbalanced tensorと評価後のtensorの自然同型。 -/
def freeTensorFunctorIso (N : LeftModule A D) (x : D) :
    freeAt x ⋙ rightTensorFunctor A D N ≅ tensorRight (N.obj x) :=
  Adjunction.leftAdjointUniq
    (((freeEvaluationAdjunction A D x).comp (tensorHomAdjunction A D N)).ofNatIsoRight
      (homRightEvaluationIso A D N x))
    (tensorRightHomAdjunction (N.obj x))

/-- 自由dg加群のbalanced tensorは任意の生成複体で評価できる。 -/
def freeTensorIso (N : LeftModule A D) (x : D) (K : Complex A) :
    obj A D (ForgetEnrichment.to (Complex A) ((freeAt x).obj K)) N ≅ K ⊗ N.obj x :=
  (freeTensorFunctorIso A D N x).app K

/-- 自由加群の生成複体を変える射についての自然性。 -/
lemma freeTensorIso_naturality (N : LeftModule A D) (x : D) {K K' : Complex A} (f : K ⟶ K') :
    (rightTensorFunctor A D N).map ((freeAt x).map f) ≫ (freeTensorIso A D N x K').hom =
      (freeTensorIso A D N x K).hom ≫ (f ▷ N.obj x) :=
  (freeTensorFunctorIso A D N x).hom.naturality f

end BalancedTensor

open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- A上K-flatな生成複体からの自由加群は相対K-flat。Hom_Dのflat性は不要。 -/
lemma freeAt_relativeKFlat (x : D) (K : Complex A) (hK : complexKFlat A K) :
    moduleRelativeKFlat A D (ForgetEnrichment.to (Complex A) ((freeAt x).obj K)) := by
  intro N hN n
  exact (hK (N.obj x) (hN x) n).of_iso (BalancedTensor.freeTensorIso A D N x K).symm

end SerrePositivity.DifferentialGraded
end

end FreeEvaluation

/-! ## SphereFreeKFlat（旧 SerrePositivity/DifferentialGraded/Tensor/SphereFreeKFlat.lean） -/

/-! # 自由sphereとsphere-free段階の相対K-flat性 -/

@[expose] public section SphereFreeKFlat
universe u v

noncomputable section
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits MonoidalCategory
variable (A : Type u) [CommRing A]

/-- 任意整数次数のsphereはA上K-flat。 -/
lemma complexSphere_kFlat (n : ℤ) : complexKFlat A (complexSphere A n) := by
  have h : complexKFlat A ((complexSphere A 0)⟦-n⟧) :=
    complexKFlat_shift A (complexKFlat_unit A) (-n)
  have e : (complexSphere A 0)⟦-n⟧ ≅ complexSphere A n := by
    simpa using complexSphereShiftIso A 0 (-n)
  exact complexKFlat_of_iso A e.symm h

variable (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 任意次数の自由sphereはHom_DのA-flat性を仮定せず相対K-flat。 -/
lemma freeSphere_relativeKFlat (x : D) (n : ℤ) :
    moduleRelativeKFlat A D (ForgetEnrichment.to (Complex A) (freeSphere A D x n)) :=
  freeAt_relativeKFlat A D x (complexSphere A n) (complexSphere_kFlat A n)

/-- 実際のsphere-free表示を持つ段階は相対K-flat。添字はambient宇宙から縮小する。 -/
lemma sphereFreePresentation_relativeKFlat {M : ModuleCategory A D}
    (S : ModuleSphereFreePresentation A D M) :
    moduleRelativeKFlat A D (ForgetEnrichment.to (Complex A) M) := by
  have := S.smallIndex
  have : HasExactColimitsOfShape (Discrete S.Index) (ModuleCat.{u} A) :=
    HasExactColimitsOfShape.of_domain_equivalence (ModuleCat.{u} A)
      (Discrete.equivalence (equivShrink.{u} S.Index).symm)
  apply moduleRelativeKFlat_of_iso A D S.iso
  exact moduleRelativeKFlat_colimit A D
    (Discrete.functor fun i => freeSphere A D (S.object i) (S.degree i))
    (fun i => freeSphere_relativeKFlat A D (S.object i.as) (S.degree i.as))

end SerrePositivity.DifferentialGraded
end

end SphereFreeKFlat

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "4.4.2.14" (partial := special) "仮定：dg 圏上の片側 dg 加群と通常圏の余極限（Lean は外側の代数を単位にした、複体値の釣合テンソルの場合に限る）。結論：左・右を固定した釣合テンソルがそれぞれ通常の余極限を保つ（この場合の各変数の保存に一致）。operadic 輸送と任意の両側加群は含まれない。"] _root_.SerrePositivity.DifferentialGraded.BalancedTensor.leftTensorFunctor_preservesColimits
attribute [cite HA "4.4.2.14" (partial := special) "仮定：dg 圏上の片側 dg 加群と通常圏の余極限（Lean は外側の代数を単位にした、複体値の釣合テンソルの場合に限る）。結論：左・右を固定した釣合テンソルがそれぞれ通常の余極限を保つ（この場合の各変数の保存に一致）。operadic 輸送と任意の両側加群は含まれない。"] _root_.SerrePositivity.DifferentialGraded.BalancedTensor.rightTensorFunctor_preservesColimits
attribute [cite HA "4.4.2.15" (partial := special) "仮定：dg 圏上の左右の dg 加群（Lean は外側が単位で、通常の余極限を取る場合に限る）。結論：複体値の釣合テンソルが各変数で通常の余極限を保つ（この場合に一致）。一般のモノイダル ∞ 圏の両側加群での保存は含まれない。"] _root_.SerrePositivity.DifferentialGraded.BalancedTensor.leftTensorFunctor_preservesColimits
attribute [cite HA "4.4.2.15" (partial := special) "仮定：dg 圏上の左右の dg 加群（Lean は外側が単位で、通常の余極限を取る場合に限る）。結論：複体値の釣合テンソルが各変数で通常の余極限を保つ（この場合に一致）。一般のモノイダル ∞ 圏の両側加群での保存は含まれない。"] _root_.SerrePositivity.DifferentialGraded.BalancedTensor.rightTensorFunctor_preservesColimits
attribute [cite HA "4.4.2.16" (partial := special) "仮定：dg 圏上の左右の dg 加群（Lean は作用圏を同じ dg 模型に取り、外側の代数を単位にした場合に限る）。結論：釣合テンソルが左右それぞれに関して通常の余極限を保つ（複体値の場合に一致）。異なる作用圏での ∞ 圏の余極限は含まれない。"] _root_.SerrePositivity.DifferentialGraded.BalancedTensor.leftTensorFunctor_preservesColimits
attribute [cite HA "4.4.2.16" (partial := special) "仮定：dg 圏上の左右の dg 加群（Lean は作用圏を同じ dg 模型に取り、外側の代数を単位にした場合に限る）。結論：釣合テンソルが左右それぞれに関して通常の余極限を保つ（複体値の場合に一致）。異なる作用圏での ∞ 圏の余極限は含まれない。"] _root_.SerrePositivity.DifferentialGraded.BalancedTensor.rightTensorFunctor_preservesColimits
