module

public import SerrePositivity.DifferentialGraded.Complexes.HomComplex
public import SerrePositivity.HomologicalAlgebra.CochainTensor.Basic
public import Mathlib.Algebra.Homology.Double
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import SerrePositivity.HomologicalAlgebra.CochainTensor.Symmetric
public import SerrePositivity.HomologicalAlgebra.CochainTensor.Shuffle
public import SerrePositivity.HomologicalAlgebra.Complex.ConeLES
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.Algebra.Homology.BifunctorHomotopy

/-!
# Complexes.Perturbation

## 概要
16 本の同主題の構成と比較をまとめる。

## 方針
依存順に連結し、宣言と証明を保存する。

## 規約
元ごとの section で variable と option を保持する。private 名の変更は private_renames で明示する。

## 使われ方
DG の土台とその下流から import する。
-/

/-! ## UnitTensor（旧 SerrePositivity/DifferentialGraded/Complexes/UnitTensor.lean） -/

/-! # 単位からの射の tensor と次数零評価 -/

@[expose] public section UnitTensor
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits MonoidalCategory HomologicalComplex
variable {A : Type u} [CommRing A]

/-- 単位からの射 f,g の tensor を、単位の対角と合成して 1 で評価する。
閉次数零射の合成と元の合成を比較する入口。 -/
lemma unit_tensor_apply {P Q : Complex A} (f : 𝟙_ (Complex A) ⟶ P)
    (g : 𝟙_ (Complex A) ⟶ Q) :
    (((λ_ (𝟙_ (Complex A))).inv ≫ (f ⊗ₘ g)).f 0) (1 : A) =
      ιTensorObj P Q 0 0 0 rfl ((cycleFromUnit P f).val ⊗ₜ[A] (cycleFromUnit Q g).val) := by
  change ((leftUnitor' (𝟙_ (Complex A))).inv 0 ≫ (f ⊗ₘ g).f 0) (1 : A) = _
  rw [leftUnitor'_inv, Category.assoc, Category.assoc, ι_tensorHom]
  rfl

/-- 任意の chain map は単位からの射の評価と可換。 -/
lemma cycleFromUnit_postcomp {P Q : Complex A} (f : 𝟙_ (Complex A) ⟶ P) (g : P ⟶ Q) :
    (cycleFromUnit Q (f ≫ g)).val = g.f 0 (cycleFromUnit P f).val := rfl
end SerrePositivity.DifferentialGraded
end

end UnitTensor

/-! ## UnitBoundary（旧 SerrePositivity/DifferentialGraded/Complexes/UnitBoundary.lean） -/

/-! # 単位からのホモトピーと元の Hom 複体の境界 -/

@[expose] public section UnitBoundary
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A]

/-- −1 の元 h を単位複体から K への −1 コチェインにする。 -/
def unitMinusOne (K : Complex A) (h : K.X (-1)) : Cochain (𝟙_ (Complex A)) K (-1) :=
  Cochain.mk (fun p q hpq =>
    if hp : p = 0 then
      eqToHom (by subst p; rfl) ≫
        ModuleCat.ofHom
          { toFun a := a • h
            map_add' a b := add_smul a b h
            map_smul' a b := mul_smul a b h } ≫
        eqToHom (congrArg K.X (show (-1 : ℤ) = q by omega))
    else 0)

/-- −1 コチェインを単位の 1 で評価すると境界の次数零元になる。 -/
lemma unit_homotopy_boundary (K : Complex A) (f g : 𝟙_ (Complex A) ⟶ K) :
    Nonempty (Homotopy f g) ↔
      ∃ h : K.X (-1), (K.d (-1) 0) h =
        (cycleFromUnit K f).val - (cycleFromUnit K g).val := by
  constructor
  · rintro ⟨h⟩
    refine ⟨h.hom 0 (-1) ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv 1), ?_⟩
    have hc := h.comm 0
    rw [dNext_eq h.hom (show (ComplexShape.up ℤ).Rel 0 1 by simp),
      prevD_eq h.hom (show (ComplexShape.up ℤ).Rel (-1) 0 by simp)] at hc
    change f.f 0 =
      ((single (ModuleCat A) (.up ℤ) 0).obj (𝟙_ (ModuleCat A))).d 0 1 ≫ h.hom 1 0 +
        h.hom 0 (-1) ≫ K.d (-1) 0 + g.f 0 at hc
    rw [single_obj_d, zero_comp, zero_add] at hc
    have hv := congr($(hc).hom ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv 1))
    change f.f 0 ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv 1) =
      K.d (-1) 0 (h.hom 0 (-1) ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv 1)) +
        g.f 0 ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv 1) at hv
    change K.d (-1) 0 (h.hom 0 (-1) _) = f.f 0 _ - g.f 0 _
    rw [hv]
    abel
  · rintro ⟨h, dh⟩
    apply (unit_homotopy_iff K f g).2
    refine ⟨unitMinusOne K h, ?_⟩
    apply Cochain.ext₀
    intro p
    by_cases hp : p = 0
    · subst p
      rw [Cochain.add_v, Cochain.ofHom_v,
        δ_v (-1) 0 (by omega) (unitMinusOne K h) 0 0 (by omega) (-1) 1 rfl rfl]
      change f.f 0 = (unitMinusOne K h).v 0 (-1) rfl ≫ K.d (-1) 0 +
        (0 : ℤ).negOnePow •
          (((single (ModuleCat A) (.up ℤ) 0).obj (𝟙_ (ModuleCat A))).d 0 1 ≫
            (unitMinusOne K h).v 1 0 (by omega)) + g.f 0
      rw [single_obj_d, zero_comp, smul_zero, add_zero]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro a
      change f.f 0 a = (K.d (-1) 0) ((show A from a) • h) + g.f 0 a
      rw [map_smul]
      have hd : (K.d (-1) 0) h = f.f 0 (1 : A) - g.f 0 (1 : A) := dh
      rw [hd, smul_sub, ← map_smul, ← map_smul]
      change f.f 0 a = f.f 0 ((show A from a) • (1 : A)) -
        g.f 0 ((show A from a) • (1 : A)) + g.f 0 a
      simp
    · apply (isZero_single_obj_X (.up ℤ) 0 (𝟙_ (ModuleCat A)) p hp).eq_of_src
end SerrePositivity.DifferentialGraded
end

end UnitBoundary

/-! ## Cells（旧 SerrePositivity/DifferentialGraded/Complexes/Cells.lean） -/

/-! # コチェインの sphere/disk と生成元の指定

sphere n は次数nのA、disk n は次数n→n+1の恒等微分。
セルの境界包含は sphere (n+1)→disk n。この規約をホモロジー次数と混同しない。
-/

@[expose] public section Cells
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits MonoidalCategory HomologicalComplex
variable (A : Type u) [CommRing A]

/-- Aからの線形射は1の像で指定できる。 -/
def moduleElementMap (V : ModuleCat.{u} A) (z : V) : (𝟙_ (ModuleCat A)) ⟶ V :=
  ModuleCat.ofHom
    { toFun := fun a => a • z
      map_add' a b := add_smul a b z
      map_smul' a b := mul_smul a b z }

def moduleElementEquiv (V : ModuleCat.{u} A) : ((𝟙_ (ModuleCat A)) ⟶ V) ≃ V where
  toFun f := f (1 : A)
  invFun := moduleElementMap A V
  left_inv f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    change a • f (1 : A) = f a
    rw [← map_smul]
    congr 1
    simp
  right_inv z := by change (1 : A) • z = z; exact one_smul A z

/-- 一つの次数nに集中したA複体。 -/
abbrev complexSphere (n : ℤ) : Complex A :=
  (single (ModuleCat A) (.up ℤ) n).obj (𝟙_ (ModuleCat A))

/-- 次数n→n+1の恒等微分からなるdisk。 -/
abbrev complexDisk (n : ℤ) : Complex A :=
  double (𝟙 (𝟙_ (ModuleCat A))) (show (ComplexShape.up ℤ).Rel n (n + 1) by simp)

/-- 次数nのcycleを要素として扱う。 -/
abbrev complexCycles (K : Complex A) (n : ℤ) := LinearMap.ker (K.d n (n + 1)).hom

abbrev complexDiskX₀ (n : ℤ) : (complexDisk A n).X n ≅ (𝟙_ (ModuleCat A)) :=
  doubleXIso₀ _ _

abbrev complexDiskX₁ (n : ℤ) : (complexDisk A n).X (n + 1) ≅ (𝟙_ (ModuleCat A)) :=
  doubleXIso₁ _ _ (by omega)

/-- diskからのchain mapは次数nの任意の生成元の像で指定できる。 -/
def complexDiskHomEquiv (K : Complex A) (n : ℤ) : (complexDisk A n ⟶ K) ≃ K.X n :=
  (evalCompCoyonedaCorepresentableByDoubleId
    (show (ComplexShape.up ℤ).Rel n (n + 1) by simp) (by omega) (𝟙_ (ModuleCat A))).homEquiv.trans
      (moduleElementEquiv A (K.X n))

/-- sphereからの射の生成元の像はcycle。 -/
def complexSphereCycle {K : Complex A} (n : ℤ) (f : complexSphere A n ⟶ K) :
    complexCycles A K n where
  val := ((singleObjXSelf (.up ℤ) n (𝟙_ (ModuleCat A))).inv ≫ f.f n) (1 : A)
  property := by
    have hc := f.comm n (n + 1)
    change f.f n ≫ K.d n (n + 1) =
      ((single (ModuleCat A) (.up ℤ) n).obj (𝟙_ (ModuleCat A))).d n (n + 1) ≫ f.f (n + 1) at hc
    rw [single_obj_d, zero_comp] at hc
    have h := congrArg (fun φ =>
      ((singleObjXSelf (.up ℤ) n (𝟙_ (ModuleCat A))).inv ≫ φ) (1 : A)) hc
    change K.d n (n + 1)
      (((singleObjXSelf (.up ℤ) n (𝟙_ (ModuleCat A))).inv ≫ f.f n) (1 : A)) = 0 at h
    exact h

/-- cycleを指定したsphereからの射。 -/
def complexSphereMap {K : Complex A} (n : ℤ) (z : complexCycles A K n) : complexSphere A n ⟶ K :=
  mkHomFromSingle (moduleElementMap A (K.X n) z.val) (by
    intro k hk
    obtain rfl : k = n + 1 := hk.symm
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    change K.d n (n + 1) (a • z.val) = 0
    rw [map_smul, z.property, smul_zero])

/-- sphereからのchain mapは次数nのcycleの像で指定できる。 -/
def complexSphereHomEquiv (K : Complex A) (n : ℤ) :
    (complexSphere A n ⟶ K) ≃ complexCycles A K n where
  toFun := complexSphereCycle A n
  invFun := complexSphereMap A n
  left_inv f := by
    apply from_single_hom_ext
    apply (cancel_epi (singleObjXSelf (.up ℤ) n (𝟙_ (ModuleCat A))).inv).1
    rw [complexSphereMap, mkHomFromSingle_f, Iso.inv_hom_id_assoc]
    exact (moduleElementEquiv A (K.X n)).left_inv
      ((singleObjXSelf (.up ℤ) n (𝟙_ (ModuleCat A))).inv ≫ f.f n)
  right_inv z := by
    apply Subtype.ext
    change ((singleObjXSelf (.up ℤ) n (𝟙_ (ModuleCat A))).inv ≫
      (complexSphereMap A n z).f n) (1 : A) = z.val
    rw [complexSphereMap, mkHomFromSingle_f, Iso.inv_hom_id_assoc]
    exact one_smul A z.val

/-- cochain diskの境界は上の次数n+1のsphere。 -/
def complexSphereToDisk (n : ℤ) : complexSphere A (n + 1) ⟶ complexDisk A n :=
  mkHomFromSingle (complexDiskX₁ A n).inv (by
    intro k _
    rw [double_d_eq_zero₀ _ _ (n + 1) k (by omega), comp_zero])

lemma complexDiskHomEquiv_apply {K : Complex A} (n : ℤ) (f : complexDisk A n ⟶ K) :
    complexDiskHomEquiv A K n f = ((complexDiskX₀ A n).inv ≫ f.f n) (1 : A) := rfl

lemma complexDiskHomEquiv_naturality {K L : Complex A} (n : ℤ)
    (f : complexDisk A n ⟶ K) (g : K ⟶ L) :
    complexDiskHomEquiv A L n (f ≫ g) = g.f n (complexDiskHomEquiv A K n f) := by
  rw [complexDiskHomEquiv_apply, HomologicalComplex.comp_f, complexDiskHomEquiv_apply]
  rfl

/-- diskの上の生成元の像は、下の生成元の像の微分。 -/
lemma complexDisk_upper_apply {K : Complex A} (n : ℤ) (f : complexDisk A n ⟶ K) :
    ((complexDiskX₁ A n).inv ≫ f.f (n + 1)) (1 : A) =
      K.d n (n + 1) (complexDiskHomEquiv A K n f) := by
  have hc := f.comm n (n + 1)
  change f.f n ≫ K.d n (n + 1) =
    (double _ (show (ComplexShape.up ℤ).Rel n (n + 1) by simp)).d n (n + 1) ≫ f.f (n + 1) at hc
  rw [double_d _ _ (by omega)] at hc
  have hh := congrArg (fun φ => (complexDiskX₀ A n).inv ≫ φ) hc
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Category.id_comp] at hh
  have hv := congrArg (fun φ => φ (1 : A)) hh
  change K.d n (n + 1) (((complexDiskX₀ A n).inv ≫ f.f n) (1 : A)) =
    ((complexDiskX₁ A n).inv ≫ f.f (n + 1)) (1 : A) at hv
  exact hv.symm

/-- セル境界包含による前合成は生成元の微分を取る操作。 -/
lemma complexSphereToDisk_comp {K : Complex A} (n : ℤ) (f : complexDisk A n ⟶ K) :
    (complexSphereHomEquiv A K (n + 1) (complexSphereToDisk A n ≫ f)).val =
      K.d n (n + 1) (complexDiskHomEquiv A K n f) := by
  change (((singleObjXSelf (.up ℤ) (n + 1) (𝟙_ (ModuleCat A))).inv) ≫
    (complexSphereToDisk A n ≫ f).f (n + 1)) (1 : A) = _
  rw [HomologicalComplex.comp_f, complexSphereToDisk, mkHomFromSingle_f,
    Category.assoc, Iso.inv_hom_id_assoc]
  exact complexDisk_upper_apply A n f

end SerrePositivity.DifferentialGraded
end

end Cells

/-! ## SphereHom（旧 SerrePositivity/DifferentialGraded/Complexes/SphereHom.lean） -/

/-! # sphereからの全次数Homとacyclic性

singleからのcochainは唯一の生成元の像で決まり、Hom微分は値域の微分になる。
-/

@[expose] public section SphereHom
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A]

def complexSphereHomElementEquiv (K : Complex A) (n p : ℤ) :
    (homComplex A (complexSphere A n) K).X p ≃ K.X (n + p) :=
  (Cochain.fromSingleEquiv (X := 𝟙_ (ModuleCat A)) (K := K) (rfl : n + p = n + p)).toEquiv.trans
    (moduleElementEquiv A (K.X (n + p)))

def complexSphereHomElementLinearEquiv (K : Complex A) (n p : ℤ) :
    (homComplex A (complexSphere A n) K).X p ≃ₗ[A] K.X (n + p) where
  toEquiv := complexSphereHomElementEquiv A K n p
  map_add' z t := by
    change (Cochain.fromSingleEquiv (X := 𝟙_ (ModuleCat A)) (K := K)
      (rfl : n + p = n + p) (z + t)) (1 : A) = _
    rw [map_add]
    rfl
  map_smul' r z := by
    change (Cochain.fromSingleEquiv (X := 𝟙_ (ModuleCat A)) (K := K)
      (rfl : n + p = n + p) (r • z)) (1 : A) = _
    rw [Cochain.fromSingleEquiv_smul]
    rfl

lemma complexSphereHomElementEquiv_zero (K : Complex A) (n p : ℤ) :
    complexSphereHomElementEquiv A K n p 0 = 0 := by
  change (Cochain.fromSingleEquiv (X := 𝟙_ (ModuleCat A)) (K := K) (rfl : n + p = n + p) 0)
    (1 : A) = 0
  rw [map_zero]
  rfl

lemma complexSphereHomElementEquiv_d (K : Complex A) (n p q : ℤ)
    (z : (homComplex A (complexSphere A n) K).X p) :
    complexSphereHomElementEquiv A K n q ((homComplex A (complexSphere A n) K).d p q z) =
      K.d (n + p) (n + q) (complexSphereHomElementEquiv A K n p z) := by
  obtain ⟨f, rfl⟩ := Cochain.fromSingleMk_surjective z (n + p) rfl
  change (Cochain.fromSingleEquiv (X := 𝟙_ (ModuleCat A)) (K := K) (rfl : n + q = n + q)
    (δ p q (Cochain.fromSingleMk f rfl))) (1 : A) =
      K.d (n + p) (n + q)
        ((Cochain.fromSingleEquiv (X := 𝟙_ (ModuleCat A)) (K := K) rfl
          (Cochain.fromSingleMk f (rfl : n + p = n + p))) (1 : A))
  rw [Cochain.δ_fromSingleMk f (rfl : n + p = n + p) q (n + q) rfl,
    Cochain.fromSingleEquiv_fromSingleMk,
    Cochain.fromSingleEquiv_fromSingleMk]
  rfl

/-- 全整数次数でsphereからのHomはacyclic複体をacyclicに送る。 -/
lemma complexSphereHom_acyclic (K : Complex A) (n : ℤ) (hK : K.Acyclic) :
    (homComplex A (complexSphere A n) K).Acyclic := by
  intro p
  apply (HomologicalComplex.exactAt_iff' (K := homComplex A (complexSphere A n) K)
    (i := p - 1) (j := p) (k := p + 1) (by simp) (by simp)).2
  rw [ShortComplex.moduleCat_exact_iff]
  change ∀ z : (homComplex A (complexSphere A n) K).X p,
    (homComplex A (complexSphere A n) K).d p (p + 1) z = 0 →
      ∃ t : (homComplex A (complexSphere A n) K).X (p - 1),
        (homComplex A (complexSphere A n) K).d (p - 1) p t = z
  intro z hz
  have hc := congrArg (complexSphereHomElementEquiv A K n (p + 1)) hz
  rw [complexSphereHomElementEquiv_d, complexSphereHomElementEquiv_zero] at hc
  have he := (HomologicalComplex.exactAt_iff' (K := K)
    (i := n + (p - 1)) (j := n + p) (k := n + (p + 1))
      (by simp; omega) (by simp; omega)).1 (hK (n + p))
  rw [ShortComplex.moduleCat_exact_iff] at he
  change ∀ y : K.X (n + p), K.d (n + p) (n + (p + 1)) y = 0 →
    ∃ t : K.X (n + (p - 1)), K.d (n + (p - 1)) (n + p) t = y at he
  obtain ⟨t, ht⟩ := he (complexSphereHomElementEquiv A K n p z) hc
  refine ⟨(complexSphereHomElementEquiv A K n (p - 1)).symm t, ?_⟩
  apply (complexSphereHomElementEquiv A K n p).injective
  rw [complexSphereHomElementEquiv_d, Equiv.apply_symm_apply]
  exact ht

end SerrePositivity.DifferentialGraded
end

end SphereHom

/-! ## Composition（旧 SerrePositivity/DifferentialGraded/Complexes/Composition.lean） -/

/-! # 通常順の dg 合成と豊穣順の符号比較 -/

@[expose] public section Composition
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A]

/-- 双次数の射が tensor 微分と両立すれば、非有界全 tensor から chain map を作る。
直和の普遍性を用いるので有限支持・有界性を仮定しない。 -/
def tensorLift {P Q T : Complex A}
    (b : ∀ (i j n : ℤ), i + j = n → (P.X i ⊗ Q.X j ⟶ T.X n))
    (db : ∀ (i j : ℤ),
      b i j (i + j) rfl ≫ T.d (i + j) (i + j + 1) =
        (P.d i (i + 1) ▷ Q.X j) ≫ b (i + 1) j (i + j + 1) (by omega) +
        i.negOnePow • ((P.X i ◁ Q.d j (j + 1)) ≫
          b i (j + 1) (i + j + 1) (by omega))) : P ⊗ Q ⟶ T where
  f n := mapBifunctorDesc (fun i j h => b i j n h)
  comm' n m h := by
    obtain rfl : m = n + 1 := h.symm
    apply mapBifunctor.hom_ext
    intro i j hij
    subst n
    rw [ι_mapBifunctorDesc_assoc]
    change b i j (i + j) rfl ≫ T.d (i + j) (i + j + 1) =
      (ιTensorObj P Q i j (i + j) rfl ≫ (P ⊗ Q).d (i + j) (i + j + 1)) ≫
        mapBifunctorDesc (fun i j h => b i j (_ + 1) h)
    have hd := SerrePositivity.cochainTensorι_d P Q i j
    change ιTensorObj P Q i j (i + j) rfl ≫ (P ⊗ Q).d (i + j) (i + j + 1) = _ at hd
    rw [hd, Preadditive.add_comp,
      Linear.units_smul_comp, Category.assoc, Category.assoc,
      ι_mapBifunctorDesc, ι_mapBifunctorDesc]
    exact db i j

/-- tensorLift の斉次成分。 -/
@[reassoc (attr := simp)]
lemma ι_tensorLift {P Q T : Complex A}
    (b : ∀ (i j n : ℤ), i + j = n → (P.X i ⊗ Q.X j ⟶ T.X n)) (db)
    (i j n : ℤ) (h : i + j = n) :
    ιTensorObj P Q i j n h ≫ (tensorLift b db).f n = b i j n h :=
  by
    dsimp only [tensorLift]
    exact ι_mapBifunctorDesc _ i j h

/-- g⊗f を f.comp g へ送る A 線形射。通常の dg 合成の順序。 -/
def compositionComponent (X Y Z : Complex A) (q p n : ℤ) (h : q + p = n) :
    (homComplex A Y Z).X q ⊗ (homComplex A X Y).X p ⟶ (homComplex A X Z).X n :=
  ModuleCat.ofHom (TensorProduct.lift
    { toFun g :=
        { toFun f := f.comp g (by omega)
          map_add' f f' := Cochain.add_comp f f' g _
          map_smul' a f := Cochain.smul_comp a f g _ }
      map_add' g g' := by apply LinearMap.ext; intro f; exact Cochain.comp_add f g g' (by omega)
      map_smul' a g := by apply LinearMap.ext; intro f; exact Cochain.comp_smul f a g (by omega) })

/-- 純粋 tensor における通常順合成。 -/
@[simp]
lemma compositionComponent_apply (X Y Z : Complex A) (q p n : ℤ) (h : q + p = n)
    (g : Homogeneous Y Z q) (f : Homogeneous X Y p) :
    compositionComponent X Y Z q p n h (g ⊗ₜ[A] f) = f.comp g (by omega) := rfl

/-- 通常順合成の chain map。Leibniz の符号が tensor の第一因子 q と一致する。 -/
def composition (X Y Z : Complex A) :
    homComplex A Y Z ⊗ homComplex A X Y ⟶ homComplex A X Z :=
  tensorLift (compositionComponent X Y Z) (by
    intro q p
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    apply LinearMap.ext
    intro g
    apply LinearMap.ext
    intro f
    change δ (q + p) (q + p + 1) (f.comp g (by omega)) =
      f.comp (δ q (q + 1) g) (by omega) +
      q.negOnePow • (δ p (p + 1) f).comp g (by omega)
    exact differential_comp f g (by omega))

/-- 豊穣順 f⊗g の合成は signed braiding の後に通常順合成する。 -/
def enrichedComposition (X Y Z : Complex A) :
    homComplex A X Y ⊗ homComplex A Y Z ⟶ homComplex A X Z :=
  (SerrePositivity.cochainTensorSymmetry _ _).hom ≫ composition X Y Z

/-- 豊穣順と通常順の Koszul 比較。交換同型の既存成分公式を用いる。 -/
lemma enrichedComposition_component (X Y Z : Complex A) (p q n : ℤ) (h : p + q = n) :
    ιTensorObj (homComplex A X Y) (homComplex A Y Z) p q n h ≫
      (enrichedComposition X Y Z).f n =
    (p * q).negOnePow • ((β_ ((homComplex A X Y).X p) ((homComplex A Y Z).X q)).hom ≫
      compositionComponent X Y Z q p n (by omega)) := by
  dsimp only [enrichedComposition, HomologicalComplex.comp_f]
  rw [← Category.assoc, SerrePositivity.ιTensorObj_cochainTensorSymmetry,
    Linear.units_smul_comp, Category.assoc]
  dsimp only [composition]
  rw [ι_tensorLift]

/-- 閉次数零では豊穣順の合成に符号は付かない。 -/
lemma enrichedComposition_zero (X Y Z : Complex A) :
    ιTensorObj (homComplex A X Y) (homComplex A Y Z) 0 0 0 rfl ≫
      (enrichedComposition X Y Z).f 0 =
    (β_ ((homComplex A X Y).X 0) ((homComplex A Y Z).X 0)).hom ≫
      compositionComponent X Y Z 0 0 0 rfl := by
  simpa using enrichedComposition_component X Y Z 0 0 0 rfl
end SerrePositivity.DifferentialGraded
end

end Composition

/-! ## CompositionLaws（旧 SerrePositivity/DifferentialGraded/Complexes/CompositionLaws.lean） -/

/-! # dg 合成の単位と結合 -/

@[expose] public section CompositionLaws
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A]

/-- 恒等 chain map に対応する閉次数零単位。 -/
def identity (X : Complex A) : 𝟙_ (Complex A) ⟶ homComplex A X X :=
  unitFromCycle _ ⟨Cochain.ofHom (𝟙 X), δ_ofHom _⟩

/-- 豊穣合成を純粋斉次 tensor で評価する。 -/
lemma enrichedComposition_apply (X Y Z : Complex A) (p q n : ℤ) (h : p + q = n)
    (f : Homogeneous X Y p) (g : Homogeneous Y Z q) :
    (enrichedComposition X Y Z).f n
      (ιTensorObj (homComplex A X Y) (homComplex A Y Z) p q n h (f ⊗ₜ[A] g)) =
      (p * q).negOnePow • f.comp g h := by
  have hc := enrichedComposition_component X Y Z p q n h
  have he := congr($(hc).hom (f ⊗ₜ[A] g))
  change (enrichedComposition X Y Z).f n
    (ιTensorObj (homComplex A X Y) (homComplex A Y Z) p q n h (f ⊗ₜ[A] g)) =
      (p * q).negOnePow • compositionComponent X Y Z q p n (by omega) (g ⊗ₜ[A] f) at he
  exact he

/-- 二重 tensor の射の等式を三重斉次 tensor へ帰着する。 -/
lemma triple_ext {P Q T S : Complex A} {f g : (P ⊗ Q) ⊗ T ⟶ S}
    (h : ∀ (i j k n : ℤ) (hn : i + j + k = n),
      (ιTensorObj P Q i j (i + j) rfl ▷ T.X k) ≫
        ιTensorObj (P ⊗ Q) T (i + j) k n hn ≫ f.f n =
      (ιTensorObj P Q i j (i + j) rfl ▷ T.X k) ≫
        ιTensorObj (P ⊗ Q) T (i + j) k n hn ≫ g.f n) : f = g := by
  apply HomologicalComplex.Hom.ext
  funext n
  exact SerrePositivity.cochainTensorTriple_hom_ext P Q T n
    (fun i j k hn => h i j k n hn)

/-- associator の三重斉次成分公式。 -/
@[reassoc]
lemma ι_associator (P Q T : Complex A) (i j k n : ℤ) (hn : i + j + k = n) :
    (ιTensorObj P Q i j (i + j) rfl ▷ T.X k) ≫
      ιTensorObj (P ⊗ Q) T (i + j) k n hn ≫ (α_ P Q T).hom.f n =
    (α_ (P.X i) (Q.X j) (T.X k)).hom ≫
      (P.X i ◁ ιTensorObj Q T j k (j + k) rfl) ≫
        ιTensorObj P (Q ⊗ T) i (j + k) n (by omega) :=
  SerrePositivity.ιTensorObj_cochainTensorAssociator_hom P Q T i j k n hn

/-- 豊穣順の合成の結合則。符号の等式は p q+p r+q r の二つの展開。 -/
lemma enrichedComposition_assoc (W X Y Z : Complex A) :
    enrichedComposition W X Y ▷ homComplex A Y Z ≫ enrichedComposition W Y Z =
    (α_ _ _ _).hom ≫ homComplex A W X ◁ enrichedComposition X Y Z ≫
      enrichedComposition W X Z := by
  apply triple_ext
  intro p q r n hn
  simp only [HomologicalComplex.comp_f]
  rw [ι_whiskerRight_assoc, ι_associator_assoc, ι_whiskerLeft_assoc]
  apply ModuleCat.hom_ext
  apply TensorProduct.ext_threefold
  intro f g h
  change (enrichedComposition W Y Z).f n
    (ιTensorObj (homComplex A W Y) (homComplex A Y Z) (p + q) r n hn
      ((enrichedComposition W X Y).f (p + q)
        (ιTensorObj (homComplex A W X) (homComplex A X Y) p q (p + q) rfl
          (f ⊗ₜ[A] g)) ⊗ₜ[A] h)) =
    (enrichedComposition W X Z).f n
      (ιTensorObj (homComplex A W X) (homComplex A X Z) p (q + r) n (by omega)
        (f ⊗ₜ[A] (enrichedComposition X Y Z).f (q + r)
          (ιTensorObj (homComplex A X Y) (homComplex A Y Z) q r (q + r) rfl
            (g ⊗ₜ[A] h))))
  rw [enrichedComposition_apply, enrichedComposition_apply]
  rw [enrichedComposition_apply, enrichedComposition_apply]
  simp only [Cochain.units_smul_comp, Cochain.comp_units_smul, smul_smul,
    ← Int.negOnePow_add]
  rw [Cochain.comp_assoc _ _ _ rfl rfl hn]
  congr 1
  congr 1
  ring
/-- 豊穣順の閉単位の左単位則。 -/
lemma identity_comp (X Y : Complex A) :
    (λ_ (homComplex A X Y)).inv ≫ identity X ▷ _ ≫ enrichedComposition X X Y = 𝟙 _ := by
  apply HomologicalComplex.Hom.ext
  funext n
  change (leftUnitor' (homComplex A X Y)).inv n ≫
    (identity X ▷ homComplex A X Y).f n ≫ (enrichedComposition X X Y).f n = 𝟙 _
  rw [leftUnitor'_inv, Category.assoc, Category.assoc, ι_whiskerRight_assoc]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  change (enrichedComposition X X Y).f n
    (ιTensorObj (homComplex A X X) (homComplex A X Y) 0 n n (zero_add n)
      ((identity X).f 0 ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv 1) ⊗ₜ[A] f)) = f
  rw [enrichedComposition_apply]
  change (0 * n).negOnePow •
    (cycleFromUnit _ (identity X)).val.comp f (zero_add n) = f
  rw [identity, cycleFromUnit_unitFromCycle]
  simp

/-- 豊穣順の閉単位の右単位則。 -/
lemma comp_identity (X Y : Complex A) :
    (ρ_ (homComplex A X Y)).inv ≫ _ ◁ identity Y ≫ enrichedComposition X Y Y = 𝟙 _ := by
  apply HomologicalComplex.Hom.ext
  funext n
  change (rightUnitor' (homComplex A X Y)).inv n ≫
    (homComplex A X Y ◁ identity Y).f n ≫ (enrichedComposition X Y Y).f n = 𝟙 _
  rw [rightUnitor'_inv, Category.assoc, Category.assoc, ι_whiskerLeft_assoc]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  change (enrichedComposition X Y Y).f n
    (ιTensorObj (homComplex A X Y) (homComplex A Y Y) n 0 n (add_zero n)
      (f ⊗ₜ[A] (identity Y).f 0 ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv 1))) = f
  rw [enrichedComposition_apply]
  change (n * 0).negOnePow •
    f.comp (cycleFromUnit _ (identity Y)).val (add_zero n) = f
  rw [identity, cycleFromUnit_unitFromCycle]
  simp

/-- tensor の chain map から双次数成分を取り出すと tensorLift の微分条件を満たす。 -/
lemma tensorComponent_d {P Q T : Complex A} (c : P ⊗ Q ⟶ T) (i j : ℤ) :
    (ιTensorObj P Q i j (i + j) rfl ≫ c.f (i + j)) ≫ T.d (i + j) (i + j + 1) =
      (P.d i (i + 1) ▷ Q.X j) ≫
        (ιTensorObj P Q (i + 1) j (i + j + 1) (by omega) ≫ c.f (i + j + 1)) +
      i.negOnePow • ((P.X i ◁ Q.d j (j + 1)) ≫
        (ιTensorObj P Q i (j + 1) (i + j + 1) (by omega) ≫ c.f (i + j + 1))) := by
  have hd := SerrePositivity.cochainTensorι_d P Q i j
  change ιTensorObj P Q i j (i + j) rfl ≫ (P ⊗ Q).d (i + j) (i + j + 1) = _ at hd
  rw [Category.assoc, c.comm, ← Category.assoc, hd,
    Preadditive.add_comp, Linear.units_smul_comp, Category.assoc, Category.assoc]

/-- 成分 accessor と tensorLift constructor の chain map の往復。 -/
lemma tensorLift_recover {P Q T : Complex A} (c : P ⊗ Q ⟶ T) :
    tensorLift (fun i j n h => ιTensorObj P Q i j n h ≫ c.f n) (tensorComponent_d c) = c := by
  apply tensorHom_ext
  intro i j n h
  rw [ι_tensorLift]
end SerrePositivity.DifferentialGraded
end

end CompositionLaws

/-! ## AcyclicCone（旧 SerrePositivity/DifferentialGraded/Complexes/AcyclicCone.lean） -/

/-! # 既存の複体 cone による quasiIso の判定 -/

@[expose] public section AcyclicCone
universe u

noncomputable section
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex CochainComplex
variable (A : Type u) [CommRing A]

/-- 非有界複体の射は、その標準 mapping cone が acyclic であるとき準同型。 -/
lemma complex_quasiIso_iff_acyclic_cone {P Q : Complex A} (f : P ⟶ Q) :
    QuasiIso f ↔ (mappingCone f).Acyclic :=
  SerrePositivity.cochain_quasiIso_iff_cone_acyclic f

end SerrePositivity.DifferentialGraded
end

end AcyclicCone

/-! ## Perturbation（旧 SerrePositivity/DifferentialGraded/Complexes/Perturbation.lean） -/

/-! # 閉じた二乗零cochainによる非有界複体の微分の変更

次数+1のcochain θについてδθ=0とθ²=0を個別の証明として受け取り、d+θを微分とする。
dg商への適用ではθ²=0を別途証明する必要がある。
-/

@[expose] public section Perturbation
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits Preadditive HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A] (K : Complex A) (θ : Cochain K K 1)

/-- 閉じた次数+1の自己cochainは元の微分と反交換する。 -/
lemma closed_one_anticommute (hθ : δ 1 2 θ = 0) (i : ℤ) :
    θ.v i (i + 1) rfl ≫ K.d (i + 1) (i + 1 + 1) +
      K.d i (i + 1) ≫ θ.v (i + 1) (i + 1 + 1) rfl = 0 := by
  have h := congrArg (fun f : Cochain K K 2 => f.v i (i + 1 + 1) (by omega)) hθ
  rw [δ_v 1 2 (by omega) θ i (i + 1 + 1) (by omega) (i + 1) (i + 1)
    (by omega) rfl, show (2 : ℤ).negOnePow = 1 by decide, one_smul, Cochain.zero_v] at h
  exact h

/-- cochainの二乗零から隣接する成分の合成零を得る。 -/
lemma square_zero_one_components
    (hθθ : θ.comp θ (show (1 : ℤ) + 1 = 2 by omega) = 0) (i : ℤ) :
    θ.v i (i + 1) rfl ≫ θ.v (i + 1) (i + 1 + 1) rfl = 0 := by
  have h := congrArg (fun f : Cochain K K 2 => f.v i (i + 1 + 1) (by omega)) hθθ
  rw [Cochain.comp_v θ θ _ i (i + 1) (i + 1 + 1) rfl rfl, Cochain.zero_v] at h
  exact h

/-- 元の微分と閉じた二乗零作用素の和も二乗零。 -/
lemma perturbedDifferential_squared (hθ : δ 1 2 θ = 0)
    (hθθ : θ.comp θ (show (1 : ℤ) + 1 = 2 by omega) = 0) (i : ℤ) :
    (K.d i (i + 1) + θ.v i (i + 1) rfl) ≫
      (K.d (i + 1) (i + 1 + 1) + θ.v (i + 1) (i + 1 + 1) rfl) = 0 := by
  rw [add_comp, comp_add, comp_add, K.d_comp_d, zero_add,
    square_zero_one_components K θ hθθ, add_zero]
  exact (add_comm _ _).trans (closed_one_anticommute K θ hθ i)

/-- 各次数の加群を保ち、微分をd+θへ変更した非有界複体。 -/
def perturbComplex (hθ : δ 1 2 θ = 0)
    (hθθ : θ.comp θ (show (1 : ℤ) + 1 = 2 by omega) = 0) : Complex A :=
  CochainComplex.of K.X (fun i => K.d i (i + 1) + θ.v i (i + 1) rfl)
    (perturbedDifferential_squared K θ hθ hθθ)

@[simp] lemma perturbComplex_X (hθ : δ 1 2 θ = 0)
    (hθθ : θ.comp θ (show (1 : ℤ) + 1 = 2 by omega) = 0) (i : ℤ) :
    (perturbComplex K θ hθ hθθ).X i = K.X i := rfl

@[simp] lemma perturbComplex_d (hθ : δ 1 2 θ = 0)
    (hθθ : θ.comp θ (show (1 : ℤ) + 1 = 2 by omega) = 0) (i : ℤ) :
    (perturbComplex K θ hθ hθθ).d i (i + 1) =
      K.d i (i + 1) + θ.v i (i + 1) rfl := by
  exact CochainComplex.of_d K.X (fun j => K.d j (j + 1) + θ.v j (j + 1) rfl) i

end SerrePositivity.DifferentialGraded
end

end Perturbation

/-! ## PerturbationMap（旧 SerrePositivity/DifferentialGraded/Complexes/PerturbationMap.lean） -/

/-! # 始域の微分変更と次数0 cochainからのchain map -/

@[expose] public section PerturbationMap
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Preadditive HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A]

/-- δf=θfを満たすcochainは、始域の微分をd+θへ変えるとchain mapとなる。 -/
def perturbSourceMap (K L : Complex A) (θ : Cochain K K 1) (hθ : δ 1 2 θ = 0)
    (hθθ : θ.comp θ (show (1 : ℤ) + 1 = 2 by omega) = 0)
    (f : Cochain K L 0) (hf : δ 0 1 f = θ.comp f (add_zero 1)) :
    perturbComplex K θ hθ hθθ ⟶ L :=
  CochainComplex.ofHom (fun i => f.v i i (add_zero i)) (fun i => by
    have h := congrArg (fun z : Cochain K L 1 => z.v i (i + 1) rfl) hf
    rw [δ_zero_cochain_v, Cochain.comp_zero_cochain_v] at h
    rw [perturbComplex_d, add_comp]
    simpa only [add_comm] using (sub_eq_iff_eq_add).1 h)

lemma perturbSourceMap_f (K L : Complex A) (θ : Cochain K K 1) (hθ : δ 1 2 θ = 0)
    (hθθ : θ.comp θ (show (1 : ℤ) + 1 = 2 by omega) = 0)
    (f : Cochain K L 0) (hf : δ 0 1 f = θ.comp f (add_zero 1)) (i : ℤ) :
    (perturbSourceMap K L θ hθ hθθ f hf).f i = f.v i i (add_zero i) := rfl

end SerrePositivity.DifferentialGraded
end

end PerturbationMap

/-! ## PerturbationRestriction（旧 SerrePositivity/DifferentialGraded/Complexes/PerturbationRestriction.lean） -/

/-! # 分裂包含に沿う追加微分の制限とchain map

## 概要
分裂包含に沿う追加微分の制限とchain map。

## 方針
既存の全dg自然なHom・作用・chain mapと局所化の計算を再利用する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。dg加群の導来作用・準同値比較の基盤。任意可換環上のMorita・K理論のモデル比較に再利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section PerturbationRestriction
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Preadditive HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A] {L K : Complex A}

lemma cochain_postcomp_injective_of_retraction (i : L ⟶ K) (r : K ⟶ L) (hir : i ≫ r = 𝟙 L)
    (T : Complex A) (p : ℤ) :
    Function.Injective (fun f : Cochain T L p => f.comp (Cochain.ofHom i) (add_zero p)) := by
  intro f g h
  have hh := congrArg (fun z : Cochain T K p => z.comp (Cochain.ofHom r) (add_zero p)) h
  simpa only [Cochain.comp_assoc_of_third_is_zero_cochain, ← Cochain.ofHom_comp,
    hir, Cochain.comp_id] using hh

/-- 包含と追加微分の可換式から、制限した作用素の閉性を得る。 -/
lemma perturbation_closed_of_inclusion (i : L ⟶ K) (r : K ⟶ L) (hir : i ≫ r = 𝟙 L)
    (ψ : Cochain L L 1) (θ : Cochain K K 1) (hθ : δ 1 2 θ = 0)
    (hi : (Cochain.ofHom i).comp θ (zero_add 1) = ψ.comp (Cochain.ofHom i) (add_zero 1)) :
    δ 1 2 ψ = 0 := by
  apply cochain_postcomp_injective_of_retraction i r hir L 2
  dsimp only
  rw [Cochain.zero_comp, ← δ_comp_ofHom, ← hi, δ_ofHom_comp, hθ, Cochain.comp_zero]

/-- 同じ可換式から、制限した作用素の二乗零を得る。 -/
lemma perturbation_square_zero_of_inclusion (i : L ⟶ K) (r : K ⟶ L) (hir : i ≫ r = 𝟙 L)
    (ψ : Cochain L L 1) (θ : Cochain K K 1)
    (hθθ : θ.comp θ (show (1 : ℤ) + 1 = 2 by omega) = 0)
    (hi : (Cochain.ofHom i).comp θ (zero_add 1) = ψ.comp (Cochain.ofHom i) (add_zero 1)) :
    ψ.comp ψ (show (1 : ℤ) + 1 = 2 by omega) = 0 := by
  apply cochain_postcomp_injective_of_retraction i r hir L 2
  dsimp only
  rw [Cochain.zero_comp, Cochain.comp_assoc_of_third_is_zero_cochain, ← hi,
    ← Cochain.comp_assoc_of_second_is_zero_cochain, ← hi,
    Cochain.comp_assoc_of_first_is_zero_cochain, hθθ, Cochain.comp_zero]

/-- 両側の微分変更と可換する元のchain map。 -/
def perturbMap (i : L ⟶ K) (ψ : Cochain L L 1) (θ : Cochain K K 1)
    (hψ : δ 1 2 ψ = 0) (hθ : δ 1 2 θ = 0)
    (hψψ : ψ.comp ψ (show (1 : ℤ) + 1 = 2 by omega) = 0)
    (hθθ : θ.comp θ (show (1 : ℤ) + 1 = 2 by omega) = 0)
    (hi : (Cochain.ofHom i).comp θ (zero_add 1) = ψ.comp (Cochain.ofHom i) (add_zero 1)) :
    perturbComplex L ψ hψ hψψ ⟶ perturbComplex K θ hθ hθθ :=
  CochainComplex.ofHom (fun n => i.f n) (fun n => by
    rw [perturbComplex_d, perturbComplex_d, comp_add, add_comp, i.comm]
    congr 1
    have h := congrArg (fun f : Cochain L K 1 => f.v n (n + 1) rfl) hi
    simpa only [Cochain.zero_cochain_comp_v, Cochain.comp_zero_cochain_v, Cochain.ofHom_v] using h)

lemma perturbMap_f (i : L ⟶ K) (ψ : Cochain L L 1) (θ : Cochain K K 1)
    (hψ : δ 1 2 ψ = 0) (hθ : δ 1 2 θ = 0)
    (hψψ : ψ.comp ψ (show (1 : ℤ) + 1 = 2 by omega) = 0)
    (hθθ : θ.comp θ (show (1 : ℤ) + 1 = 2 by omega) = 0)
    (hi : (Cochain.ofHom i).comp θ (zero_add 1) = ψ.comp (Cochain.ofHom i) (add_zero 1)) (n : ℤ) :
    (perturbMap i ψ θ hψ hθ hψψ hθθ hi).f n = i.f n := rfl

end SerrePositivity.DifferentialGraded
end

end PerturbationRestriction

/-! ## MapEvaluation（旧 SerrePositivity/DifferentialGraded/Complexes/MapEvaluation.lean） -/

/-! # 複体の射の可換式の斉次元での評価 -/

@[expose] public section MapEvaluation
universe u

namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex
variable {A : Type u} [CommRing A]

lemma chain_comp_apply {X Y Z : Complex A} (f : X ⟶ Y) (g : Y ⟶ Z)
    (n : ℤ) (x : X.X n) : (f ≫ g).f n x = g.f n (f.f n x) := rfl

/-- 合成の等式を、各複体の内部構成を展開せずに斉次元へ適用する。 -/
lemma chain_comp_apply_of_eq {X Y Z : Complex A} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z)
    (w : f ≫ g = h) (n : ℤ) (x : X.X n) : g.f n (f.f n x) = h.f n x :=
  ConcreteCategory.congr_hom (HomologicalComplex.congr_hom w n) x

/-- 各次数の元での等式から複体の射の等式を得る。 -/
lemma chain_ext_apply {X Y : Complex A} (f g : X ⟶ Y)
    (h : ∀ (n : ℤ) (x : X.X n), f.f n x = g.f n x) : f = g := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  exact h n

end SerrePositivity.DifferentialGraded

end MapEvaluation

/-! ## MapComponentFunctions（旧 SerrePositivity/DifferentialGraded/Complexes/MapComponentFunctions.lean） -/

/-! # 指定された成分関数で複体の射を再表示する -/

@[expose] public section MapComponentFunctions
universe u

noncomputable section
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex
variable {A : Type u} [CommRing A] {X Y : Complex A}

/-- 成分関数とその既存chain mapへの一致から、成分を明示したchain mapを構成する。 -/
def chainMapOfComponentFunctions (f : X ⟶ Y) (F : ∀ n, X.X n → Y.X n)
    (h : ∀ n x, F n x = f.f n x) : X ⟶ Y where
  f n := ModuleCat.ofHom {
    toFun := F n
    map_add' := fun x y => by rw [h, h, h]; exact map_add (f.f n).hom x y
    map_smul' := fun a x => by rw [h, h]; exact map_smul (f.f n).hom a x }
  comm' i j hij := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change Y.d i j (F i x) = F j (X.d i j x)
    rw [h, h]
    exact ConcreteCategory.congr_hom (f.comm i j) x

@[simp]
lemma chainMapOfComponentFunctions_apply (f : X ⟶ Y) (F : ∀ n, X.X n → Y.X n)
    (h : ∀ n x, F n x = f.f n x) (n : ℤ) (x : X.X n) :
    (chainMapOfComponentFunctions f F h).f n x = F n x := rfl

lemma chainMapOfComponentFunctions_eq (f : X ⟶ Y) (F : ∀ n, X.X n → Y.X n)
    (h : ∀ n x, F n x = f.f n x) : chainMapOfComponentFunctions f F h = f := by
  apply chain_ext_apply
  exact h

end SerrePositivity.DifferentialGraded
end

end MapComponentFunctions

/-! ## ExactColimits（旧 SerrePositivity/DifferentialGraded/Complexes/ExactColimits.lean） -/

/-! # 非有界複体のexactな余極限とacyclic性 -/

@[expose] public section ExactColimits
universe u w w'

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits HomologicalComplex
variable (A : Type u) [CommRing A] {J : Type w} [Category.{w'} J] [Small.{u} J]

/-- 非有界複体の図式を複体の各次数にある図式へ転置する。 -/
def complexDiagramTranspose (F : J ⥤ Complex A) : CochainComplex (J ⥤ ModuleCat.{u} A) ℤ where
  X i := F ⋙ eval (ModuleCat.{u} A) (.up ℤ) i
  d i j := { app := fun x => (F.obj x).d i j
             naturality := fun _ _ f => (F.map f).comm i j }
  shape i j h := by
    apply NatTrans.ext
    funext x
    exact (F.obj x).shape i j h
  d_comp_d' i j k _ _ := by
    apply NatTrans.ext
    funext x
    exact (F.obj x).d_comp_d i j k

omit [Small.{u} J] in
/-- 対象ごとのacyclic性は転置した関手複体のacyclic性を与える。 -/
lemma complexDiagramTranspose_acyclic (F : J ⥤ Complex A) (h : ∀ j, (F.obj j).Acyclic) :
    (complexDiagramTranspose A F).Acyclic := by
  intro n
  apply (exactAt_iff_isZero_homology _ n).2
  apply (Functor.isZero_iff _).2
  intro j
  exact IsZero.of_iso ((h j n).isZero_homology)
    (((complexDiagramTranspose A F).sc n).mapHomologyIso
      ((evaluation J (ModuleCat.{u} A)).obj j)).symm

variable [HasColimitsOfShape J (ModuleCat.{u} A)] [HasExactColimitsOfShape J (ModuleCat.{u} A)]

/-- 対象ごとacyclicな非有界複体のexactな余極限はacyclic。 -/
lemma complex_colimit_acyclic (F : J ⥤ Complex A) (h : ∀ j, (F.obj j).Acyclic) :
    (colimit F).Acyclic := by
  let K := complexDiagramTranspose A F
  let L := ((colim : (J ⥤ ModuleCat.{u} A) ⥤ ModuleCat.{u} A).mapHomologicalComplex (.up ℤ)).obj K
  have hK := complexDiagramTranspose_acyclic A F h
  have hL : L.Acyclic := by
    intro n
    apply (exactAt_iff_isZero_homology _ n).2
    exact IsZero.of_iso
      ((colim : (J ⥤ ModuleCat.{u} A) ⥤ ModuleCat.{u} A).map_isZero ((hK n).isZero_homology))
      ((K.sc n).mapHomologyIso (colim : (J ⥤ ModuleCat.{u} A) ⥤ ModuleCat.{u} A))
  let e : L ≅ colimit F :=
    IsColimit.coconePointUniqueUpToIso (isColimitCoconeOfHasColimitEval F) (colimit.isColimit F)
  intro n
  exact (hL n).of_iso e

end SerrePositivity.DifferentialGraded
end

end ExactColimits

/-! ## DiskGenerator（旧 SerrePositivity/DifferentialGraded/Complexes/DiskGenerator.lean） -/

/-! # diskからの射の逆構成と下の生成元の像 -/

@[expose] public section DiskGenerator
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A]

lemma complexDiskHomEquiv_symm_generator (K : Complex A) (q : ℤ) (z : K.X q) :
    ((complexDiskHomEquiv A K q).symm z).f q ((complexDiskX₀ A q).inv (1 : A)) = z := by
  have h := (complexDiskHomEquiv A K q).apply_symm_apply z
  rw [complexDiskHomEquiv_apply] at h
  exact h

end SerrePositivity.DifferentialGraded
end

end DiskGenerator

/-! ## DiskFiltration（旧 SerrePositivity/DifferentialGraded/Complexes/DiskFiltration.lean） -/

/-! # diskの二段sphere filtration

上の次数n+1のsphereを部分複体とし、商は次数nのsphere。
次数付きsection/retractionにはchain map条件を課さない。
-/

@[expose] public section DiskFiltration
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A]

def complexDiskToSphere (n : ℤ) : complexDisk A n ⟶ complexSphere A n :=
  mkHomToSingle (complexDiskX₀ A n).hom (by
    intro i _
    rw [double_d_eq_zero₁ _ _ i n (by omega), zero_comp])

lemma complexDiskToSphere_f (n : ℤ) :
    (complexDiskToSphere A n).f n =
      (complexDiskX₀ A n).hom ≫ (singleObjXSelf (.up ℤ) n (𝟙_ (ModuleCat A))).inv :=
  mkHomToSingle_f _ _

lemma complexDiskToSphere_f_eq_zero (n k : ℤ) (hk : k ≠ n) :
    (complexDiskToSphere A n).f k = 0 :=
  (isZero_single_obj_X (.up ℤ) n (𝟙_ (ModuleCat A)) k hk).eq_of_tgt _ _

lemma complexSphereToDisk_f (n : ℤ) :
    (complexSphereToDisk A n).f (n + 1) =
      (singleObjXSelf (.up ℤ) (n + 1) (𝟙_ (ModuleCat A))).hom ≫ (complexDiskX₁ A n).inv :=
  mkHomFromSingle_f _ _

lemma complexSphereToDisk_f_eq_zero (n k : ℤ) (hk : k ≠ n + 1) :
    (complexSphereToDisk A n).f k = 0 :=
  (isZero_single_obj_X (.up ℤ) (n + 1) (𝟙_ (ModuleCat A)) k hk).eq_of_src _ _

lemma complexSphereToDiskToSphere (n : ℤ) :
    complexSphereToDisk A n ≫ complexDiskToSphere A n = 0 := by
  apply from_single_hom_ext
  simp only [HomologicalComplex.comp_f, HomologicalComplex.zero_f,
    complexDiskToSphere_f_eq_zero A n (n + 1) (by omega), comp_zero]

def complexDiskGradedRetraction (n : ℤ) :
    Homogeneous (complexDisk A n) (complexSphere A (n + 1)) 0 :=
  Cochain.single ((complexDiskX₁ A n).hom ≫
    (singleObjXSelf (.up ℤ) (n + 1) (𝟙_ (ModuleCat A))).inv) 0

def complexDiskGradedSection (n : ℤ) :
    Homogeneous (complexSphere A n) (complexDisk A n) 0 :=
  Cochain.single ((singleObjXSelf (.up ℤ) n (𝟙_ (ModuleCat A))).hom ≫
    (complexDiskX₀ A n).inv) 0

lemma complexDiskGraded_inclusion_retraction (n k : ℤ) :
    (complexSphereToDisk A n).f k ≫ (complexDiskGradedRetraction A n).v k k (add_zero k) = 𝟙 _ := by
  by_cases hk : k = n + 1
  · subst k
    simp only [complexSphereToDisk_f, complexDiskGradedRetraction, Cochain.single_v,
      Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id]
  · exact (isZero_single_obj_X (.up ℤ) (n + 1) (𝟙_ (ModuleCat A)) k hk).eq_of_src _ _

lemma complexDiskGraded_section_projection (n k : ℤ) :
    (complexDiskGradedSection A n).v k k (add_zero k) ≫ (complexDiskToSphere A n).f k = 𝟙 _ := by
  by_cases hk : k = n
  · subst k
    simp only [complexDiskToSphere_f, complexDiskGradedSection, Cochain.single_v,
      Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id]
  · exact (isZero_single_obj_X (.up ℤ) n (𝟙_ (ModuleCat A)) k hk).eq_of_src _ _

lemma complexDiskGraded_section_retraction (n k : ℤ) :
    (complexDiskGradedSection A n).v k k (add_zero k) ≫
      (complexDiskGradedRetraction A n).v k k (add_zero k) = 0 := by
  by_cases hk : k = n
  · subst k
    rw [complexDiskGradedRetraction, Cochain.single_v_eq_zero _ 0 n n (add_zero n) (by omega),
      comp_zero]
  · rw [complexDiskGradedSection, Cochain.single_v_eq_zero _ 0 k k (add_zero k) hk, zero_comp]

lemma complexDiskGraded_decomposition (n k : ℤ) :
    (complexDiskGradedRetraction A n).v k k (add_zero k) ≫ (complexSphereToDisk A n).f k +
      (complexDiskToSphere A n).f k ≫ (complexDiskGradedSection A n).v k k (add_zero k) = 𝟙 _ := by
  by_cases h₀ : k = n
  · subst k
    rw [complexDiskGradedRetraction, Cochain.single_v_eq_zero _ 0 n n (add_zero n) (by omega)]
    simp only [zero_comp, zero_add, complexDiskToSphere_f, complexDiskGradedSection,
      Cochain.single_v, Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id]
  · by_cases h₁ : k = n + 1
    · subst k
      rw [complexDiskToSphere_f_eq_zero A n (n + 1) (by omega)]
      simp only [zero_comp, add_zero, complexDiskGradedRetraction, Cochain.single_v,
        complexSphereToDisk_f, Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id]
    · exact (isZero_double_X _ _ k h₀ h₁).eq_of_src _ _

def complexDiskSphereShortComplex (n : ℤ) : ShortComplex (Complex A) :=
  ShortComplex.mk (complexSphereToDisk A n) (complexDiskToSphere A n)
    (complexSphereToDiskToSphere A n)

/-- 各次数でのMathlib標準の分裂データ。 -/
def complexDiskSphereSplitting (n k : ℤ) :
    ((complexDiskSphereShortComplex A n).map
      (HomologicalComplex.eval (ModuleCat A) (.up ℤ) k)).Splitting where
  r := (complexDiskGradedRetraction A n).v k k (add_zero k)
  s := (complexDiskGradedSection A n).v k k (add_zero k)
  f_r := complexDiskGraded_inclusion_retraction A n k
  s_g := complexDiskGraded_section_projection A n k
  id := complexDiskGraded_decomposition A n k

lemma complexDiskSphereShortExact (n k : ℤ) :
    ((complexDiskSphereShortComplex A n).map
      (HomologicalComplex.eval (ModuleCat A) (.up ℤ) k)).ShortExact :=
  (complexDiskSphereSplitting A n k).shortExact

lemma complexDiskGraded_inclusion_retraction_cochain (n : ℤ) :
    (Cochain.ofHom (complexSphereToDisk A n)).comp (complexDiskGradedRetraction A n)
      (zero_add 0) = Cochain.ofHom (𝟙 _) := by
  apply Cochain.ext₀
  intro k
  rw [Cochain.comp_zero_cochain_v, Cochain.ofHom_v, Cochain.ofHom_v, HomologicalComplex.id_f]
  exact complexDiskGraded_inclusion_retraction A n k

lemma complexDiskGraded_section_projection_cochain (n : ℤ) :
    (complexDiskGradedSection A n).comp (Cochain.ofHom (complexDiskToSphere A n))
      (zero_add 0) = Cochain.ofHom (𝟙 _) := by
  apply Cochain.ext₀
  intro k
  rw [Cochain.comp_zero_cochain_v, Cochain.ofHom_v, Cochain.ofHom_v, HomologicalComplex.id_f]
  exact complexDiskGraded_section_projection A n k

lemma complexDiskGraded_section_retraction_cochain (n : ℤ) :
    (complexDiskGradedSection A n).comp (complexDiskGradedRetraction A n) (zero_add 0) = 0 := by
  apply Cochain.ext₀
  intro k
  rw [Cochain.comp_zero_cochain_v, Cochain.zero_v]
  exact complexDiskGraded_section_retraction A n k

lemma complexDiskGraded_decomposition_cochain (n : ℤ) :
    (complexDiskGradedRetraction A n).comp (Cochain.ofHom (complexSphereToDisk A n)) (zero_add 0) +
      (Cochain.ofHom (complexDiskToSphere A n)).comp (complexDiskGradedSection A n) (zero_add 0) =
        Cochain.ofHom (𝟙 _) := by
  apply Cochain.ext₀
  intro k
  rw [Cochain.add_v, Cochain.comp_zero_cochain_v, Cochain.comp_zero_cochain_v,
    Cochain.ofHom_v, Cochain.ofHom_v, Cochain.ofHom_v, HomologicalComplex.id_f]
  exact complexDiskGraded_decomposition A n k

end SerrePositivity.DifferentialGraded
end

end DiskFiltration

/-! ## DiskContractible（旧 SerrePositivity/DifferentialGraded/Complexes/DiskContractible.lean） -/

/-! # コチェインdiskの次数−1の収縮 -/

@[expose] public section DiskContractible
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A]

/-- 上の次数n+1から下の次数nへ戻す収縮cochain。 -/
def complexDiskContractingCochain (n : ℤ) :
    Homogeneous (complexDisk A n) (complexDisk A n) (-1) :=
  Cochain.single ((complexDiskX₁ A n).hom ≫ (complexDiskX₀ A n).inv) (-1)

lemma complexDiskContracting_d (n : ℤ) :
    δ (-1) 0 (complexDiskContractingCochain A n) = Cochain.ofHom (𝟙 (complexDisk A n)) := by
  rw [complexDiskContractingCochain, Cochain.δ_single _ (-1) 0 (by omega) n (n + 1) rfl rfl]
  have hd : (complexDisk A n).d n (n + 1) = (complexDiskX₀ A n).hom ≫ (complexDiskX₁ A n).inv := by
    rw [double_d _ _ (by omega)]
    simp only [Category.id_comp]
  rw [hd]
  simp only [Int.negOnePow_zero, one_smul, Category.assoc, Iso.inv_hom_id_assoc,
    Iso.hom_inv_id]
  apply Cochain.ext₀
  intro k
  by_cases h₀ : k = n
  · subst k
    rw [Cochain.add_v, Cochain.single_v_eq_zero _ _ _ _ _ (by omega), Cochain.single_v,
      Cochain.ofHom_v]
    simp
  · by_cases h₁ : k = n + 1
    · subst k
      rw [Cochain.add_v, Cochain.single_v, Cochain.single_v_eq_zero _ _ _ _ _ (by omega),
        Cochain.ofHom_v]
      simp
    · exact (isZero_double_X _ _ k h₀ h₁).eq_of_src _ _

/-- diskの恒等射から零射への次数−1のホモトピー。 -/
def complexDiskContractingHomotopy (n : ℤ) : Homotopy (𝟙 (complexDisk A n)) 0 :=
  contractingHomotopy _ (complexDiskContractingCochain A n) (complexDiskContracting_d A n)

lemma complexDisk_acyclic (n : ℤ) : (complexDisk A n).Acyclic := by
  intro i
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  apply (IsZero.iff_id_eq_zero _).2
  have h := (complexDiskContractingHomotopy A n).homologyMap_eq i
  simpa only [homologyMap_id, homologyMap_zero] using h

/-- 具体的収縮は任意非有界複体とのtensorで保存される。 -/
def complexDiskTensorContractingHomotopy (n : ℤ) (P : Complex A) :
    Homotopy (𝟙 (complexDisk A n ⊗ P)) 0 := by
  have h := mapBifunctorMapHomotopy₁ (complexDiskContractingHomotopy A n)
    (𝟙 P) (curriedTensor (ModuleCat A)) (.up ℤ)
  change Homotopy (𝟙 (complexDisk A n) ⊗ₘ 𝟙 P) (0 ⊗ₘ 𝟙 P) at h
  simpa only [tensorHom_id, id_whiskerRight, MonoidalPreadditive.zero_whiskerRight] using h

lemma complexDiskTensor_acyclic (n : ℤ) (P : Complex A) : (complexDisk A n ⊗ P).Acyclic := by
  intro i
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  apply (IsZero.iff_id_eq_zero _).2
  have h := (complexDiskTensorContractingHomotopy A n P).homologyMap_eq i
  simpa only [homologyMap_id, homologyMap_zero] using h

end SerrePositivity.DifferentialGraded
end

end DiskContractible
