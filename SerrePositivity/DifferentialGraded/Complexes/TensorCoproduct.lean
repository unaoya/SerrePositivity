module

public import SerrePositivity.DifferentialGraded.Complexes.Perturbation
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import SerrePositivity.DifferentialGraded.Complexes.MaurerCartanCurrying
public import Mathlib.Algebra.Homology.Precylinder
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.BifunctorHomotopy
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import SerrePositivity.HomologicalAlgebra.CochainTensor.Shuffle
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Tactic.CategoryTheory.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.Functor.OfSequence
public import SerrePositivity.DifferentialGraded.Complexes.HomComplex
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.Logic.Small.Basic

/-!
# Complexes.TensorCoproduct

## 概要
16 本の同主題の構成と比較をまとめる。

## 方針
依存順に連結し、宣言と証明を保存する。

## 規約
元ごとの section で variable と option を保持する。private 名の変更は private_renames で明示する。

## 使われ方
DG の土台とその下流から import する。
-/

/-! ## CellCriterion（旧 SerrePositivity/DifferentialGraded/Complexes/CellCriterion.lean） -/

/-! # sphere→disk の生成元方程式はconeのacyclic性を検出する -/

@[expose] public section CellCriterion
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits HomologicalComplex CochainComplex
variable (A : Type u) [CommRing A]

/-- 複体射の境界を指定しながら生成元をliftする条件。 -/
def complexBoundaryLiftAt {K L : Complex A} (f : K ⟶ L) (n : ℤ) : Prop :=
  ∀ z : complexCycles A K (n + 1), ∀ y : L.X n,
    f.f (n + 1) z.val = L.d n (n + 1) y →
      ∃ t : K.X n, K.d n (n + 1) t = z.val ∧ f.f n t = y

/-- coneの要素は二つの標準射影で判定できる。 -/
lemma complexCone_element_ext {K L : Complex A} (f : K ⟶ L) (i : ℤ)
    {z w : (mappingCone f).X i}
    (h₁ : homotopyCofiber.fstX f i (i + 1) rfl z = homotopyCofiber.fstX f i (i + 1) rfl w)
    (h₂ : homotopyCofiber.sndX f i z = homotopyCofiber.sndX f i w) : z = w := by
  have hm : moduleElementMap A _ z = moduleElementMap A _ w := by
    apply homotopyCofiber.ext_to_X f i (i + 1) rfl
    · apply (moduleElementEquiv A (K.X (i + 1))).injective
      change homotopyCofiber.fstX f i (i + 1) rfl ((1 : A) • z) =
        homotopyCofiber.fstX f i (i + 1) rfl ((1 : A) • w)
      simpa only [one_smul] using h₁
    · apply (moduleElementEquiv A (L.X i)).injective
      change homotopyCofiber.sndX f i ((1 : A) • z) = homotopyCofiber.sndX f i ((1 : A) • w)
      simpa only [one_smul] using h₂
  have he := congrArg (fun k => k (1 : A)) hm
  change (1 : A) • z = (1 : A) • w at he
  simpa only [one_smul] using he

/-- 全整数次数で境界cellをliftできる複体射は準同型。 -/
lemma complex_quasiIso_of_boundary_lifting {K L : Complex A} (f : K ⟶ L)
    (h : ∀ n : ℤ, complexBoundaryLiftAt A f n) : QuasiIso f := by
  apply (complex_quasiIso_iff_acyclic_cone A f).2
  intro i
  apply (HomologicalComplex.exactAt_iff' (K := mappingCone f) (i := i - 1) (j := i)
    (k := i + 1) (by simp) (by simp)).2
  rw [ShortComplex.moduleCat_exact_iff]
  change ∀ z : (mappingCone f).X i, (mappingCone f).d i (i + 1) z = 0 →
    ∃ t : (mappingCone f).X (i - 1), (mappingCone f).d (i - 1) i t = z
  intro z hz
  let a := homotopyCofiber.fstX f i (i + 1) rfl z
  let b := homotopyCofiber.sndX f i z
  have ha : K.d (i + 1) (i + 1 + 1) a = 0 := by
    have hc := congrArg (fun k => k z) (homotopyCofiber.d_fstX f i (i + 1) (i + 1 + 1) rfl rfl)
    change homotopyCofiber.fstX f (i + 1) (i + 1 + 1) rfl
      ((mappingCone f).d i (i + 1) z) = -K.d (i + 1) (i + 1 + 1) a at hc
    rw [hz, map_zero] at hc
    exact neg_eq_zero.mp hc.symm
  have hab : f.f (i + 1) a + L.d i (i + 1) b = 0 := by
    have hc := congrArg (fun k => k z) (homotopyCofiber.d_sndX f i (i + 1) rfl)
    change homotopyCofiber.sndX f (i + 1) ((mappingCone f).d i (i + 1) z) =
      f.f (i + 1) a + L.d i (i + 1) b at hc
    rw [hz, map_zero] at hc
    exact hc.symm
  have hc : f.f (i + 1) a = L.d i (i + 1) (-b) := by
    rw [map_neg]
    exact eq_neg_of_add_eq_zero_left hab
  obtain ⟨t, ht, hf⟩ := h i ⟨a, ha⟩ (-b) hc
  let e := -homotopyCofiber.inlX f i (i - 1) (show (ComplexShape.up ℤ).Rel (i - 1) i by simp) t
  refine ⟨e, ?_⟩
  apply complexCone_element_ext A f i
  · have hd := congrArg (fun k => k e)
      (homotopyCofiber.d_fstX f (i - 1) i (i + 1) (by simp) rfl)
    change homotopyCofiber.fstX f i (i + 1) rfl ((mappingCone f).d (i - 1) i e) =
      -K.d i (i + 1) (homotopyCofiber.fstX f (i - 1) i (by simp) e) at hd
    rw [hd]
    have he : homotopyCofiber.fstX f (i - 1) i (by simp) e = -t := by
      dsimp [e]
      rw [map_neg, ← ModuleCat.comp_apply, homotopyCofiber.inlX_fstX, ModuleCat.id_apply]
    rw [he, map_neg, neg_neg]
    exact ht
  · have hd := congrArg (fun k => k e)
      (homotopyCofiber.d_sndX f (i - 1) i (by simp))
    change homotopyCofiber.sndX f i ((mappingCone f).d (i - 1) i e) =
      f.f i (homotopyCofiber.fstX f (i - 1) i (by simp) e) +
        L.d (i - 1) i (homotopyCofiber.sndX f (i - 1) e) at hd
    rw [hd]
    have he₁ : homotopyCofiber.fstX f (i - 1) i (by simp) e = -t := by
      dsimp [e]
      rw [map_neg, ← ModuleCat.comp_apply, homotopyCofiber.inlX_fstX, ModuleCat.id_apply]
    have he₂ : homotopyCofiber.sndX f (i - 1) e = 0 := by
      dsimp [e]
      rw [map_neg, ← ModuleCat.comp_apply, homotopyCofiber.inlX_sndX]
      exact neg_zero
    rw [he₁, he₂, map_zero, add_zero, map_neg, hf, neg_neg]

/-- 次数ごと全射な準同型なら、境界を保つ生成元の同時liftが存在する。 -/
lemma complex_boundary_lifting_of_surjective_quasiIso {K L : Complex A} (f : K ⟶ L)
    (hs : ∀ i : ℤ, Function.Surjective (f.f i)) (hq : QuasiIso f) (n : ℤ) :
    complexBoundaryLiftAt A f n := by
  intro z y hy
  let c := homotopyCofiber.inlX f (n + 1) n rfl z.val - homotopyCofiber.inrX f n y
  have hc₁ : homotopyCofiber.fstX f n (n + 1) rfl c = z.val := by
    dsimp [c]
    rw [map_sub, ← ModuleCat.comp_apply, ← ModuleCat.comp_apply,
      homotopyCofiber.inlX_fstX, homotopyCofiber.inrX_fstX, ModuleCat.id_apply]
    exact sub_zero z.val
  have hc₂ : homotopyCofiber.sndX f n c = -y := by
    dsimp [c]
    rw [map_sub, ← ModuleCat.comp_apply, ← ModuleCat.comp_apply,
      homotopyCofiber.inlX_sndX, homotopyCofiber.inrX_sndX, ModuleCat.id_apply]
    exact zero_sub y
  have hc : (mappingCone f).d n (n + 1) c = 0 := by
    apply complexCone_element_ext A f (n + 1)
    · rw [map_zero]
      have hd := congrArg (fun k => k c)
        (homotopyCofiber.d_fstX f n (n + 1) (n + 1 + 1) rfl rfl)
      change homotopyCofiber.fstX f (n + 1) (n + 1 + 1) rfl
        ((mappingCone f).d n (n + 1) c) =
          -K.d (n + 1) (n + 1 + 1) (homotopyCofiber.fstX f n (n + 1) rfl c) at hd
      rw [hd, hc₁, z.property, neg_zero]
    · rw [map_zero]
      have hd := congrArg (fun k => k c) (homotopyCofiber.d_sndX f n (n + 1) rfl)
      change homotopyCofiber.sndX f (n + 1) ((mappingCone f).d n (n + 1) c) =
        f.f (n + 1) (homotopyCofiber.fstX f n (n + 1) rfl c) +
          L.d n (n + 1) (homotopyCofiber.sndX f n c) at hd
      rw [hd, hc₁, hc₂, map_neg, hy, add_neg_cancel]
  have he := (complex_quasiIso_iff_acyclic_cone A f).1 hq n
  rw [HomologicalComplex.exactAt_iff' (K := mappingCone f) (i := n - 1) (j := n)
    (k := n + 1) (by simp) (by simp), ShortComplex.moduleCat_exact_iff] at he
  change ∀ v : (mappingCone f).X n, (mappingCone f).d n (n + 1) v = 0 →
    ∃ e : (mappingCone f).X (n - 1), (mappingCone f).d (n - 1) n e = v at he
  obtain ⟨e, he⟩ := he c hc
  let u := homotopyCofiber.fstX f (n - 1) n (by simp) e
  let v := homotopyCofiber.sndX f (n - 1) e
  have hu : -K.d n (n + 1) u = z.val := by
    have hd := congrArg (fun k => k e)
      (homotopyCofiber.d_fstX f (n - 1) n (n + 1) (by simp) rfl)
    change homotopyCofiber.fstX f n (n + 1) rfl ((mappingCone f).d (n - 1) n e) =
      -K.d n (n + 1) u at hd
    rw [he, hc₁] at hd
    exact hd.symm
  have huv : f.f n u + L.d (n - 1) n v = -y := by
    have hd := congrArg (fun k => k e) (homotopyCofiber.d_sndX f (n - 1) n (by simp))
    change homotopyCofiber.sndX f n ((mappingCone f).d (n - 1) n e) =
      f.f n u + L.d (n - 1) n v at hd
    rw [he, hc₂] at hd
    exact hd.symm
  obtain ⟨q, hq⟩ := hs (n - 1) v
  refine ⟨-u - K.d (n - 1) n q, ?_, ?_⟩
  · have hd := congrArg (fun k => k q) (K.d_comp_d (n - 1) n (n + 1))
    change K.d n (n + 1) (K.d (n - 1) n q) = 0 at hd
    rw [map_sub, map_neg, hd, sub_zero]
    exact hu
  · have hd := congrArg (fun k => k q) (f.comm (n - 1) n)
    change L.d (n - 1) n (f.f (n - 1) q) = f.f n (K.d (n - 1) n q) at hd
    rw [hq] at hd
    rw [map_sub, map_neg, ← hd]
    have hv := congrArg Neg.neg huv
    simpa only [neg_add, neg_neg, sub_eq_add_neg] using hv

end SerrePositivity.DifferentialGraded
end

end CellCriterion

/-! ## TensorCylinder（旧 SerrePositivity/DifferentialGraded/Complexes/TensorCylinder.lean） -/

/-! # 単位複体の cylinder の tensor は任意非有界複体でホモトピー同値 -/

@[expose] public section TensorCylinder
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory HomologicalComplex
variable (A : Type u) [CommRing A]

/-- 単位複体の標準cylinder。 -/
abbrev dgInterval : Complex A := (𝟙_ (Complex A)).cylinder

/-- 標準cylinderの収縮を任意複体へtensorする。flatnessを要求しない。 -/
def tensorIntervalHomotopyEquiv (P : Complex A) :
    HomotopyEquiv (dgInterval A ⊗ P) ((𝟙_ (Complex A)) ⊗ P) where
  hom := cylinder.π (𝟙_ (Complex A)) ⊗ₘ 𝟙 P
  inv := cylinder.ι₀ (𝟙_ (Complex A)) ⊗ₘ 𝟙 P
  homotopyHomInvId := by
    have h := mapBifunctorMapHomotopy₁
      (cylinder.πCompι₀Homotopy (𝟙_ (Complex A)) (fun n => ⟨n - 1, by simp⟩))
      (𝟙 P) (curriedTensor (ModuleCat A)) (.up ℤ)
    change Homotopy ((cylinder.π _ ≫ cylinder.ι₀ _) ⊗ₘ 𝟙 P)
      (𝟙 (dgInterval A) ⊗ₘ 𝟙 P) at h
    rw [tensorHom_comp_tensorHom, Category.id_comp]
    simpa only [tensorHom_id, id_whiskerRight] using h
  homotopyInvHomId := Homotopy.ofEq (by
    rw [tensorHom_comp_tensorHom, cylinder.ι₀_π, Category.id_comp, tensorHom_id,
      id_whiskerRight])

lemma tensorIntervalProjection_quasiIso (P : Complex A) :
    QuasiIso ((cylinder.π (𝟙_ (Complex A)) ⊗ₘ 𝟙 P) ≫ (λ_ P).hom) := by
  have : QuasiIso (cylinder.π (𝟙_ (Complex A)) ⊗ₘ 𝟙 P) :=
    (tensorIntervalHomotopyEquiv A P).quasiIso_hom
  infer_instance

end SerrePositivity.DifferentialGraded
end

end TensorCylinder

/-! ## TensorCoproduct（旧 SerrePositivity/DifferentialGraded/Complexes/TensorCoproduct.lean） -/

/-! # 二つの複体の余積からのtensor写像の普遍性

余積とtensorの交換を既存閉構造の随伴から得る。添字の宇宙をHomの宇宙へ固定せず、
指定した余積の存在を仮定する。
-/

@[expose] public section TensorCoproduct
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits MonoidalCategory
variable {A : Type u} [CommRing A] {I : Type v} {J : Type w}

/-- 左tensorは指定された複体余積のcofanを余積へ送る。 -/
def tensorLeftCoproductIsColimit (K : Complex A) (F : I → Complex A) [HasCoproduct F] :
    IsColimit (Cofan.mk (K ⊗ ∐ F) (fun i => K ◁ Sigma.ι F i)) :=
  isColimitOfHasCoproductOfPreservesColimit (tensorLeft K) F

/-- 右tensorの余積保存は既存の右tensor–Hom随伴から得る。 -/
def tensorRightCoproductIsColimit (K : Complex A) (F : I → Complex A) [HasCoproduct F] :
    IsColimit (Cofan.mk ((∐ F) ⊗ K) (fun i => Sigma.ι F i ▷ K)) := by
  letI := (tensorRightHomAdjunction K).isLeftAdjoint
  exact isColimitOfHasCoproductOfPreservesColimit (tensorRight K) F

/-- 一つの因子を固定した右余積からのtensor写像。 -/
def tensorCoproductRightDesc (K : Complex A) (G : J → Complex A) [HasCoproduct G]
    (T : Complex A) (f : ∀ j, K ⊗ G j ⟶ T) : K ⊗ ∐ G ⟶ T :=
  (tensorLeftCoproductIsColimit K G).desc (Cofan.mk T f)

lemma tensorCoproductRightDesc_ι (K : Complex A) (G : J → Complex A) [HasCoproduct G]
    (T : Complex A) (f : ∀ j, K ⊗ G j ⟶ T) (j : J) :
    (K ◁ Sigma.ι G j) ≫ tensorCoproductRightDesc K G T f = f j :=
  (tensorLeftCoproductIsColimit K G).fac (Cofan.mk T f) ⟨j⟩

/-- 各二因子上の写像を二つの余積のtensorへ延長する。 -/
def tensorCoproductDesc (F : I → Complex A) (G : J → Complex A)
    [HasCoproduct F] [HasCoproduct G] (T : Complex A) (f : ∀ i j, F i ⊗ G j ⟶ T) :
    (∐ F) ⊗ (∐ G) ⟶ T :=
  (tensorRightCoproductIsColimit (∐ G) F).desc
    (Cofan.mk T (fun i => tensorCoproductRightDesc (F i) G T (f i)))

lemma tensorCoproductDesc_left (F : I → Complex A) (G : J → Complex A)
    [HasCoproduct F] [HasCoproduct G] (T : Complex A) (f : ∀ i j, F i ⊗ G j ⟶ T) (i : I) :
    (Sigma.ι F i ▷ ∐ G) ≫ tensorCoproductDesc F G T f =
      tensorCoproductRightDesc (F i) G T (f i) :=
  (tensorRightCoproductIsColimit (∐ G) F).fac
    (Cofan.mk T (fun i => tensorCoproductRightDesc (F i) G T (f i))) ⟨i⟩

lemma tensorCoproductDesc_ι (F : I → Complex A) (G : J → Complex A)
    [HasCoproduct F] [HasCoproduct G] (T : Complex A) (f : ∀ i j, F i ⊗ G j ⟶ T)
    (i : I) (j : J) :
    (Sigma.ι F i ⊗ₘ Sigma.ι G j) ≫ tensorCoproductDesc F G T f = f i j := by
  rw [tensorHom_def', Category.assoc, tensorCoproductDesc_left, tensorCoproductRightDesc_ι]

/-- 二つの余積のtensorからのchain mapは各二因子への制限で決まる。 -/
lemma tensorCoproduct_hom_ext (F : I → Complex A) (G : J → Complex A)
    [HasCoproduct F] [HasCoproduct G] {T : Complex A} (f g : (∐ F) ⊗ (∐ G) ⟶ T)
    (h : ∀ i j, (Sigma.ι F i ⊗ₘ Sigma.ι G j) ≫ f =
      (Sigma.ι F i ⊗ₘ Sigma.ι G j) ≫ g) : f = g := by
  apply (tensorRightCoproductIsColimit (∐ G) F).hom_ext
  rintro ⟨i⟩
  apply (tensorLeftCoproductIsColimit (F i) G).hom_ext
  rintro ⟨j⟩
  change (F i ◁ Sigma.ι G j) ≫ (Sigma.ι F i ▷ ∐ G) ≫ f =
    (F i ◁ Sigma.ι G j) ≫ (Sigma.ι F i ▷ ∐ G) ≫ g
  simpa only [← Category.assoc, ← tensorHom_def'] using h i j

end SerrePositivity.DifferentialGraded
end

end TensorCoproduct

/-! ## TensorCoproductExt（旧 SerrePositivity/DifferentialGraded/Complexes/TensorCoproductExt.lean） -/

/-! # 複数のtensor因子を持つ余積からの射の判定 -/

@[expose] public section TensorCoproductExt
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits MonoidalCategory
variable {A : Type u} [CommRing A] {I : Type v}

lemma tensorLeftRightCoproduct_hom_ext (K R : Complex A) (F : I → Complex A) [HasCoproduct F]
    {T : Complex A} (f g : (K ⊗ ∐ F) ⊗ R ⟶ T)
    (h : ∀ i, ((K ◁ Sigma.ι F i) ▷ R) ≫ f = ((K ◁ Sigma.ι F i) ▷ R) ≫ g) : f = g := by
  let := (tensorRightHomAdjunction R).isLeftAdjoint
  apply (isColimitOfHasCoproductOfPreservesColimit (tensorLeft K ⋙ tensorRight R) F).hom_ext
  rintro ⟨i⟩
  exact h i

lemma tensorLeftTwoRightCoproduct_hom_ext (L K R : Complex A) (F : I → Complex A)
    [HasCoproduct F] {T : Complex A} (f g : (L ⊗ (K ⊗ ∐ F)) ⊗ R ⟶ T)
    (h : ∀ i, ((L ◁ (K ◁ Sigma.ι F i)) ▷ R) ≫ f =
      ((L ◁ (K ◁ Sigma.ι F i)) ▷ R) ≫ g) : f = g := by
  let := (tensorRightHomAdjunction R).isLeftAdjoint
  apply (isColimitOfHasCoproductOfPreservesColimit
    (tensorLeft K ⋙ tensorLeft L ⋙ tensorRight R) F).hom_ext
  rintro ⟨i⟩
  exact h i

end SerrePositivity.DifferentialGraded
end

end TensorCoproductExt

/-! ## TensorInterchange（旧 SerrePositivity/DifferentialGraded/Complexes/TensorInterchange.lean） -/

/-! # tensorモノイダル関手の交差符号と既存shuffleの比較 -/

@[expose] public section TensorInterchange
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory HomologicalComplex
variable {A : Type u} [CommRing A]

/-- Mathlibのtensorμは既存の複体shuffleと同じ射。 -/
lemma tensorμ_eq_shuffle (P Q T U : Complex A) :
    tensorμ P Q T U = (SerrePositivity.cochainTensorShuffle P Q T U).hom := by
  simp only [tensorμ, SerrePositivity.cochainTensorShuffle, Iso.trans_hom]
  rfl

/-- 中央二因子の次数積がtensorμのKoszul符号になる。 -/
lemma tensorμ_apply (P Q T U : Complex A) (i j k l n : ℤ)
    (hn : i + j + k + l = n) (x : P.X i) (y : Q.X j) (z : T.X k) (w : U.X l) :
    (tensorμ P Q T U).f n
      (SerrePositivity.cochainTensorQuadι P Q T U i j k l n hn
        ((x ⊗ₜ[A] y) ⊗ₜ[A] (z ⊗ₜ[A] w))) =
      (j * k).negOnePow •
        SerrePositivity.cochainTensorQuadι P T Q U i k j l n (by omega)
          ((x ⊗ₜ[A] z) ⊗ₜ[A] (y ⊗ₜ[A] w)) := by
  rw [tensorμ_eq_shuffle]
  exact SerrePositivity.cochainTensorShuffle_hom_apply_ι P Q T U i j k l n hn x y z w

end SerrePositivity.DifferentialGraded
end

end TensorInterchange

/-! ## TensorGeneratorMaps（旧 SerrePositivity/DifferentialGraded/Complexes/TensorGeneratorMaps.lean） -/

/-! # tensor生成元を指定したmapの合成則 -/

@[expose] public section TensorGeneratorMaps
universe u

namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory
variable {A : Type u} [CommRing A]

lemma tensorLeft_generator_map {H J K T Z U : Complex A}
    (i : J ⟶ K) (o : H ⊗ K ⟶ Z) (p : Z ⟶ U) (a : K ⟶ T)
    (j : H ⊗ T ⟶ U) (v : J ⟶ T)
    (ho : o ≫ p = (𝟙 H ⊗ₘ a) ≫ j) (ha : i ≫ a = v) :
    ((H ◁ i) ≫ o) ≫ p = (H ◁ v) ≫ j := by
  rw [Category.assoc, ho, id_tensorHom, ← whiskerLeft_comp_assoc, ha]

lemma tensorRight_generator_map {H J K L T Z U : Complex A}
    (i : H ⊗ J ⟶ K) (o : K ⊗ L ⟶ Z) (p : Z ⟶ U) (a : K ⟶ T)
    (j : T ⊗ L ⟶ U) (v : H ⊗ J ⟶ T)
    (ho : o ≫ p = (a ⊗ₘ 𝟙 L) ≫ j) (ha : i ≫ a = v) :
    ((α_ H J L).inv ≫ (i ▷ L) ≫ o) ≫ p = (α_ H J L).inv ≫ (v ▷ L) ≫ j := by
  simp only [Category.assoc]
  rw [ho, tensorHom_id, ← comp_whiskerRight_assoc, ha]

lemma tensor_associator_balance {H J L X Y T : Complex A}
    (a : H ⊗ J ⟶ X) (b : J ⊗ L ⟶ Y) (i : X ⊗ L ⟶ T) (j : H ⊗ Y ⟶ T)
    (h : (a ▷ L) ≫ i = (α_ H J L).hom ≫ (H ◁ b) ≫ j) :
    (H ◁ b) ≫ j = (α_ H J L).inv ≫ (a ▷ L) ≫ i := by
  rw [h, Iso.inv_hom_id_assoc]

end SerrePositivity.DifferentialGraded

end TensorGeneratorMaps

/-! ## TensorRightTwoCoproductExt（旧 SerrePositivity/DifferentialGraded/Complexes/TensorRightTwoCoproductExt.lean） -/

/-! # 二つの右tensor因子を持つ余積からの射の判定 -/

@[expose] public section TensorRightTwoCoproductExt
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits MonoidalCategory
variable {A : Type u} [CommRing A]

lemma tensorRightTwoCoproduct_hom_ext {J : Type v}
    (F : J → Complex A) [HasCoproduct F] (Q R T : Complex A)
    (f g : ((∐ F) ⊗ Q) ⊗ R ⟶ T)
    (h : ∀ j, ((Sigma.ι F j ▷ Q) ▷ R) ≫ f = ((Sigma.ι F j ▷ Q) ▷ R) ≫ g) : f = g := by
  let := (tensorRightHomAdjunction Q).isLeftAdjoint
  let := (tensorRightHomAdjunction R).isLeftAdjoint
  apply (isColimitOfHasCoproductOfPreservesColimit (tensorRight Q ⋙ tensorRight R) F).hom_ext
  rintro ⟨j⟩
  exact h j

end SerrePositivity.DifferentialGraded
end

end TensorRightTwoCoproductExt

/-! ## ProductAcyclic（旧 SerrePositivity/DifferentialGraded/Complexes/ProductAcyclic.lean） -/

/-! # u-smallなacyclic複体の直積

各cycleの原像を成分ごとに選び、各次数の直積普遍性で組み立てる。
-/

@[expose] public section ProductAcyclic
universe u w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits MonoidalCategory HomologicalComplex
variable (A : Type u) [CommRing A] {J : Type w} [Small.{u} J]

/-- 各次数で複体の直積射影が直積を与える。 -/
def complexProductDegreeIsLimit (F : J → Complex A) (n : ℤ) :
    IsLimit (Fan.mk ((∏ᶜ F).X n) (fun j => (Pi.π F j).f n)) :=
  isLimitOfHasProductOfPreservesLimit (HomologicalComplex.eval (ModuleCat A) (.up ℤ) n) F

lemma complexProductDegree_hom_ext (F : J → Complex A) (n : ℤ)
    {P : ModuleCat.{u} A} {f g : P ⟶ (∏ᶜ F).X n}
    (h : ∀ j, f ≫ (Pi.π F j).f n = g ≫ (Pi.π F j).f n) : f = g := by
  apply (complexProductDegreeIsLimit A F n).hom_ext
  intro j
  exact h j.as

lemma complexProduct_acyclic (F : J → Complex A) (hF : ∀ j, (F j).Acyclic) :
    (∏ᶜ F).Acyclic := by
  intro p
  apply (HomologicalComplex.exactAt_iff' (K := ∏ᶜ F)
    (i := p - 1) (j := p) (k := p + 1) (by simp) (by simp)).2
  rw [ShortComplex.moduleCat_exact_iff]
  change ∀ z : (∏ᶜ F).X p, (∏ᶜ F).d p (p + 1) z = 0 →
    ∃ t : (∏ᶜ F).X (p - 1), (∏ᶜ F).d (p - 1) p t = z
  intro z hz
  have hj : ∀ j : J, ∃ t : (F j).X (p - 1),
      (F j).d (p - 1) p t = (Pi.π F j).f p z := by
    intro j
    have he := (HomologicalComplex.exactAt_iff' (K := F j)
      (i := p - 1) (j := p) (k := p + 1) (by simp) (by simp)).1 (hF j p)
    rw [ShortComplex.moduleCat_exact_iff] at he
    apply he
    have hc := congrArg (fun a => a z) ((Pi.π F j).comm p (p + 1))
    change (F j).d p (p + 1) ((Pi.π F j).f p z) =
      (Pi.π F j).f (p + 1) ((∏ᶜ F).d p (p + 1) z) at hc
    rw [hz, map_zero] at hc
    exact hc
  let tj := fun j => Classical.choose (hj j)
  let f : (𝟙_ (ModuleCat A)) ⟶ (∏ᶜ F).X (p - 1) :=
    Fan.IsLimit.lift (complexProductDegreeIsLimit A F (p - 1))
      (fun j => moduleElementMap A _ (tj j))
  let t := f (1 : A)
  have ht : ∀ j : J, (Pi.π F j).f (p - 1) t = tj j := by
    intro j
    have h := congrArg (fun a => a (1 : A))
      (Fan.IsLimit.fac (complexProductDegreeIsLimit A F (p - 1))
        (fun j => moduleElementMap A _ (tj j)) j)
    change (Pi.π F j).f (p - 1) t = (1 : A) • tj j at h
    exact h.trans (one_smul A _)
  refine ⟨t, ?_⟩
  have hm : moduleElementMap A _ ((∏ᶜ F).d (p - 1) p t) = moduleElementMap A _ z := by
    apply complexProductDegree_hom_ext A F p
    intro j
    apply (moduleElementEquiv A _).injective
    change (Pi.π F j).f p ((1 : A) • ((∏ᶜ F).d (p - 1) p t)) =
      (Pi.π F j).f p ((1 : A) • z)
    simp only [one_smul]
    have hc := congrArg (fun a => a t) ((Pi.π F j).comm (p - 1) p)
    change (F j).d (p - 1) p ((Pi.π F j).f (p - 1) t) =
      (Pi.π F j).f p ((∏ᶜ F).d (p - 1) p t) at hc
    exact hc.symm.trans ((congrArg ((F j).d (p - 1) p) (ht j)).trans (Classical.choose_spec (hj j)))
  have he := congrArg (fun a => a (1 : A)) hm
  change (1 : A) • ((∏ᶜ F).d (p - 1) p t) = (1 : A) • z at he
  simpa only [one_smul] using he

end SerrePositivity.DifferentialGraded
end

end ProductAcyclic

/-! ## ParameterCross（旧 SerrePositivity/DifferentialGraded/Complexes/ParameterCross.lean） -/

/-! # tensorの左因子を横切るパラメータ複体 -/

@[expose] public section ParameterCross
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory HomologicalComplex
variable {A : Type u} [CommRing A]

/-- KをPの右側へ移す。符号はKとPの次数の積。 -/
def parameterCross (K P Q : Complex A) : K ⊗ (P ⊗ Q) ⟶ P ⊗ (K ⊗ Q) :=
  (α_ K P Q).inv ≫ (signedSwap K P).hom ▷ Q ≫ (α_ P K Q).hom

@[reassoc]
lemma parameterCross_naturality_left (K : Complex A) {P P' : Complex A}
    (f : P ⟶ P') (Q : Complex A) :
    (K ◁ (f ▷ Q)) ≫ parameterCross K P' Q =
      parameterCross K P Q ≫ (f ▷ (K ⊗ Q)) := by
  have h := signedSwap_naturality (𝟙 K) f
  simp only [id_tensorHom, tensorHom_id] at h
  unfold parameterCross
  rw [associator_inv_naturality_middle_assoc, ← comp_whiskerRight_assoc, h,
    comp_whiskerRight, Category.assoc, associator_naturality_left]
  simp only [Category.assoc]

@[reassoc]
lemma parameterCross_naturality_right (K P : Complex A) {Q Q' : Complex A}
    (g : Q ⟶ Q') :
    (K ◁ (P ◁ g)) ≫ parameterCross K P Q' =
      parameterCross K P Q ≫ (P ◁ (K ◁ g)) := by
  unfold parameterCross
  rw [associator_inv_naturality_right_assoc, whisker_exchange_assoc,
    associator_naturality_right]
  simp only [Category.assoc]

/-- KをP⊗Qの右へ動かすことはP、Qの順に動かすことに等しい。 -/
@[reassoc]
lemma parameterCross_tensor (K P Q T : Complex A) :
    parameterCross K (P ⊗ Q) T ≫ (α_ P Q (K ⊗ T)).hom =
    (K ◁ (α_ P Q T).hom) ≫ parameterCross K P (Q ⊗ T) ≫
      (P ◁ parameterCross K Q T) := by
  unfold parameterCross signedSwap
  simp only [← braiding_eq_existing]
  rw [BraidedCategory.braiding_tensor_right_hom]
  monoidal

/-- パラメータと第一因子の次数の積だけが交換符号に現れる。 -/
lemma parameterCross_apply (K P Q : Complex A) (k r s n : ℤ) (hn : k + (r + s) = n)
    (t : K.X k) (m : P.X r) (v : Q.X s) :
    (parameterCross K P Q).f n
      (ιTensorObj K (P ⊗ Q) k (r + s) n hn
        (t ⊗ₜ[A] ιTensorObj P Q r s (r + s) rfl (m ⊗ₜ[A] v))) =
    (k * r).negOnePow • ιTensorObj P (K ⊗ Q) r (k + s) n (by omega)
      (m ⊗ₜ[A] ιTensorObj K Q k s (k + s) rfl (t ⊗ₜ[A] v)) := by
  change (α_ P K Q).hom.f n
    (((signedSwap K P).hom ▷ Q).f n
      ((α_ K P Q).inv.f n
        (ιTensorObj K (P ⊗ Q) k (r + s) n hn
          (t ⊗ₜ[A] ιTensorObj P Q r s (r + s) rfl (m ⊗ₜ[A] v))))) = _
  rw [associator_inv_apply, whiskerRight_apply, signedSwap_apply]
  simp only [Units.smul_def, ← TensorProduct.smul_tmul', map_zsmul]
  rw [associator_apply_of_sum]

end SerrePositivity.DifferentialGraded
end

end ParameterCross

/-! ## FilteredCycles（旧 SerrePositivity/DifferentialGraded/Complexes/FilteredCycles.lean） -/

/-! # filtered余極限のcycleの有限段表示

任意可換環上の非有界複体について、cycleの微分が零となる段階まで添字を進める。
-/

@[expose] public section FilteredCycles
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits HomologicalComplex
variable (A : Type u) [CommRing A]
variable (F : ℕ ⥤ Complex A) (s : Cocone F)

/-- 可算filtered余極限のcycleは、ある有限段のcycleの像である。 -/
lemma complexSequentialColimit_cycle_rep (hs : IsColimit s) (n : ℤ) (z : complexCycles A s.pt n) :
    ∃ (k : ℕ) (t : complexCycles A (F.obj k) n), (s.ι.app k).f n t.val = z.val := by
  let : PreservesFilteredColimitsOfSize.{0, 0} (forget (ModuleCat.{u} A)) :=
    preservesSmallestFilteredColimits_of_preservesFilteredColimits _
  let ev := HomologicalComplex.eval (ModuleCat.{u} A) (ComplexShape.up ℤ)
  let Fn := F ⋙ ev n
  let sn := (ev n).mapCocone s
  have hn : IsColimit sn := isColimitOfPreserves (ev n) hs
  obtain ⟨j, t, ht⟩ := Concrete.isColimit_exists_rep Fn hn z.val
  change (s.ι.app j).f n t = z.val at ht
  let Fn' := F ⋙ ev (n + 1)
  have hn' : IsColimit ((ev (n + 1)).mapCocone s) :=
    isColimitOfPreserves (ev (n + 1)) hs
  have hz : (s.ι.app j).f (n + 1) ((F.obj j).d n (n + 1) t) = 0 := by
    have h := congrArg (fun f => f t) ((s.ι.app j).comm n (n + 1))
    change (s.pt.d n (n + 1)) ((s.ι.app j).f n t) =
      (s.ι.app j).f (n + 1) ((F.obj j).d n (n + 1) t) at h
    exact h.symm.trans (ht ▸ z.property)
  obtain ⟨k, f, g, hk⟩ := Concrete.isColimit_exists_of_rep_eq Fn' hn'
    ((F.obj j).d n (n + 1) t) (0 : (F.obj j).X (n + 1)) (by
      change (s.ι.app j).f (n + 1) ((F.obj j).d n (n + 1) t) = (s.ι.app j).f (n + 1) 0
      simpa only [map_zero] using hz)
  change (F.map f).f (n + 1) ((F.obj j).d n (n + 1) t) = (F.map g).f (n + 1) 0 at hk
  rw [map_zero] at hk
  have hc : (F.obj k).d n (n + 1) ((F.map f).f n t) = 0 := by
    have h := congrArg (fun a => a t) ((F.map f).comm n (n + 1))
    exact h.trans hk
  refine ⟨k, ⟨(F.map f).f n t, hc⟩, ?_⟩
  have h := congrArg (fun a => a.f n t) (s.ι.naturality f)
  change (s.ι.app k).f n ((F.map f).f n t) = (s.ι.app j).f n t at h
  exact h.trans ht

end SerrePositivity.DifferentialGraded
end

end FilteredCycles

/-! ## TowerPrimitives（旧 SerrePositivity/DifferentialGraded/Complexes/TowerPrimitives.lean） -/

/-! # 全射的なacyclic複体の可算塔における互換な境界の原像

任意の逆極限の完全性は使わず、原像を補正しながら逐次選ぶ。
-/

@[expose] public section TowerPrimitives
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex
variable {A : Type u} [CommRing A]

lemma complexAcyclic_boundary {K : Complex A} (hK : K.Acyclic) (q : ℤ)
    (z : K.X q) (hz : K.d q (q + 1) z = 0) :
    ∃ t : K.X (q - 1), K.d (q - 1) q t = z := by
  have h := (HomologicalComplex.exactAt_iff' (K := K)
    (i := q - 1) (j := q) (k := q + 1) (by simp) (by simp)).1 (hK q)
  rw [ShortComplex.moduleCat_exact_iff] at h
  exact h z hz

lemma complexTower_primitive_step {K L : Complex A} (r : L ⟶ K)
    (hK : K.Acyclic) (hL : L.Acyclic)
    (hr : ∀ n : ℤ, Function.Surjective (r.f n)) (q : ℤ)
    (z : L.X q) (hz : L.d q (q + 1) z = 0)
    (t : K.X (q - 1)) (ht : K.d (q - 1) q t = r.f q z) :
    ∃ s : L.X (q - 1), L.d (q - 1) q s = z ∧ r.f (q - 1) s = t := by
  obtain ⟨b, hb⟩ := complexAcyclic_boundary (K := L) hL q z hz
  have hrb := congrArg (fun a => a b) (r.comm (q - 1) q)
  change K.d (q - 1) q (r.f (q - 1) b) = r.f q (L.d (q - 1) q b) at hrb
  rw [hb] at hrb
  have hw : K.d (q - 1) q (t - r.f (q - 1) b) = 0 := by
    rw [map_sub, ht, hrb, sub_self]
  obtain ⟨a, ha⟩ := complexAcyclic_boundary (K := K) hK (q - 1) (t - r.f (q - 1) b)
    (by rw [show q - 1 + 1 = q by omega]
        exact hw)
  obtain ⟨c, hc⟩ := hr (q - 1 - 1) a
  refine ⟨b + L.d (q - 1 - 1) (q - 1) c, ?_, ?_⟩
  · have hd := congrArg (fun a => a c) (L.d_comp_d (q - 1 - 1) (q - 1) q)
    change L.d (q - 1) q (L.d (q - 1 - 1) (q - 1) c) = 0 at hd
    rw [map_add, hb, hd, add_zero]
  · have hd := congrArg (fun a => a c) (r.comm (q - 1 - 1) (q - 1))
    change K.d (q - 1 - 1) (q - 1) (r.f (q - 1 - 1) c) =
      r.f (q - 1) (L.d (q - 1 - 1) (q - 1) c) at hd
    rw [hc, ha] at hd
    rw [map_add, ← hd]
    abel

lemma complexTower_compatible_primitives (K : ℕ → Complex A)
    (r : ∀ n, K (n + 1) ⟶ K n) (hK : ∀ n, (K n).Acyclic)
    (hr : ∀ (n : ℕ) (q : ℤ), Function.Surjective ((r n).f q)) (q : ℤ)
    (z : ∀ n, (K n).X q) (hz : ∀ n, (K n).d q (q + 1) (z n) = 0)
    (hcompat : ∀ n, (r n).f q (z (n + 1)) = z n) :
    ∃ t : ∀ n, (K n).X (q - 1),
      (∀ n, (K n).d (q - 1) q (t n) = z n) ∧
      (∀ n, (r n).f (q - 1) (t (n + 1)) = t n) := by
  let P := fun n => { t : (K n).X (q - 1) // (K n).d (q - 1) q t = z n }
  have h0 := complexAcyclic_boundary (hK 0) q (z 0) (hz 0)
  have hstep (n : ℕ) (t : P n) : ∃ s : (K (n + 1)).X (q - 1),
      (K (n + 1)).d (q - 1) q s = z (n + 1) ∧ (r n).f (q - 1) s = t.val := by
    apply complexTower_primitive_step (r n) (hK n) (hK (n + 1)) (hr n) q
      (z (n + 1)) (hz (n + 1)) t.val
    exact t.property.trans (hcompat n).symm
  let t : (n : ℕ) → P n := Nat.rec
    ⟨Classical.choose h0, Classical.choose_spec h0⟩
    (fun n t => ⟨Classical.choose (hstep n t), (Classical.choose_spec (hstep n t)).1⟩)
  exact ⟨fun n => (t n).val, fun n => (t n).property,
    fun n => (Classical.choose_spec (hstep n (t n))).2⟩

end SerrePositivity.DifferentialGraded
end

end TowerPrimitives

/-! ## TowerLimitAcyclic（旧 SerrePositivity/DifferentialGraded/Complexes/TowerLimitAcyclic.lean） -/

/-! # 全射的acyclic複体の可算逆極限のacyclic性 -/

@[expose] public section TowerLimitAcyclic
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits MonoidalCategory Opposite HomologicalComplex
variable (A : Type u) [CommRing A]

lemma complexLimitDegree_element_ext {J : Type*} [Category* J]
    {F : J ⥤ Complex A} {c : Cone F} (hc : IsLimit c) (q : ℤ)
    [PreservesLimit F (HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) q)]
    {z w : c.pt.X q} (h : ∀ j, (c.π.app j).f q z = (c.π.app j).f q w) : z = w := by
  have hm : moduleElementMap A _ z = moduleElementMap A _ w := by
    apply (isLimitOfPreserves (HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) q) hc).hom_ext
    intro j
    apply (moduleElementEquiv A _).injective
    change (c.π.app j).f q ((1 : A) • z) = (c.π.app j).f q ((1 : A) • w)
    simpa only [one_smul] using h j
  have he := congrArg (fun a => a (1 : A)) hm
  change (1 : A) • z = (1 : A) • w at he
  simpa only [one_smul] using he

lemma complexTowerLimit_acyclic (F : ℕᵒᵖ ⥤ Complex A) {c : Cone F} (hc : IsLimit c)
    (hF : ∀ n, (F.obj (op n)).Acyclic)
    (hr : ∀ (n : ℕ) (q : ℤ), Function.Surjective
      ((F.map (homOfLE (n.le_add_right 1)).op).f q)) : c.pt.Acyclic := by
  intro q
  apply (HomologicalComplex.exactAt_iff' (K := c.pt)
    (i := q - 1) (j := q) (k := q + 1) (by simp) (by simp)).2
  rw [ShortComplex.moduleCat_exact_iff]
  change ∀ z : c.pt.X q, c.pt.d q (q + 1) z = 0 →
    ∃ t : c.pt.X (q - 1), c.pt.d (q - 1) q t = z
  intro z hz
  have hcycles (n : ℕ) : (F.obj (op n)).d q (q + 1) ((c.π.app (op n)).f q z) = 0 := by
    have he := congrArg (fun a => a z) ((c.π.app (op n)).comm q (q + 1))
    change (F.obj (op n)).d q (q + 1) ((c.π.app (op n)).f q z) =
      (c.π.app (op n)).f (q + 1) (c.pt.d q (q + 1) z) at he
    exact he.trans (by rw [hz, map_zero])
  have hcompat (n : ℕ) :
      (F.map (homOfLE (n.le_add_right 1)).op).f q ((c.π.app (op (n + 1))).f q z) =
        (c.π.app (op n)).f q z := by
    exact congrArg (fun a => a.f q z) (c.w (homOfLE (n.le_add_right 1)).op)
  obtain ⟨t, hdt, htcompat⟩ := complexTower_compatible_primitives
    (fun n => F.obj (op n)) (fun n => F.map (homOfLE (n.le_add_right 1)).op)
    hF hr q (fun n => (c.π.app (op n)).f q z) hcycles hcompat
  let tc : Cone (F ⋙ HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) (q - 1)) :=
    { pt := 𝟙_ (ModuleCat A)
      π := NatTrans.ofOpSequence (fun n => moduleElementMap A _ (t n)) (by
        intro n
        apply (moduleElementEquiv A _).injective
        change (1 : A) • t n =
          (F.map (homOfLE (n.le_add_right 1)).op).f (q - 1) ((1 : A) • t (n + 1))
        simpa only [one_smul] using (htcompat n).symm) }
  let hl := isLimitOfPreserves (HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) (q - 1)) hc
  let b := hl.lift tc (1 : A)
  have hb (n : ℕ) : (c.π.app (op n)).f (q - 1) b = t n := by
    have he := congrArg (fun a => a (1 : A)) (hl.fac tc (op n))
    change (c.π.app (op n)).f (q - 1) b = (1 : A) • t n at he
    exact he.trans (one_smul A _)
  refine ⟨b, ?_⟩
  apply complexLimitDegree_element_ext A hc q
  intro n
  have he := congrArg (fun a => a b) ((c.π.app n).comm (q - 1) q)
  change (F.obj n).d (q - 1) q ((c.π.app n).f (q - 1) b) =
    (c.π.app n).f q (c.pt.d (q - 1) q b) at he
  exact he.symm.trans ((congrArg ((F.obj n).d (q - 1) q) (hb n.unop)).trans (hdt n.unop))

end SerrePositivity.DifferentialGraded
end

end TowerLimitAcyclic

/-! ## HomMapEvaluation（旧 SerrePositivity/DifferentialGraded/Complexes/HomMapEvaluation.lean） -/

/-! # 主Homの自然性を斉次cochainの等式から構成する -/

@[expose] public section HomMapEvaluation
universe u

namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A]

/-- 四つの元の比較から作用と写像の可換式を得る。 -/
lemma element_square {X X' Y Y' : Type u} (a : X → Y) (b : X' → Y')
    (l : X → X') (r : Y → Y') (x : X) (x' : X') (y : Y) (y' : Y')
    (hl : l x = x') (ha : a x = y) (hb : b x' = y') (hr : r y = y') :
    b (l x) = r (a x) :=
  (congrArg b hl).trans (hb.trans (hr.symm.trans (congrArg r ha.symm)))

lemma cochain_comp_ofHom_apply {X Y Z : Complex A} {p i n : ℤ}
    (g : Cochain X Y p) (f : Y ⟶ Z) (hn : i + p = n) (x : X.X i) :
    (g.comp (Cochain.ofHom f) (add_zero p)).v i n hn x = f.f n (g.v i n hn x) := by
  rw [Cochain.comp_v _ _ _ i n n hn (add_zero n)]
  rfl

lemma cochain_ofHom_comp_apply {X Y Z : Complex A} {p i n : ℤ}
    (f : X ⟶ Y) (g : Cochain Y Z p) (hn : i + p = n) (x : X.X i) :
    ((Cochain.ofHom f).comp g (zero_add p)).v i n hn x = g.v i n hn (f.f i x) := by
  rw [Cochain.comp_v _ _ _ i i n (add_zero i) hn]
  rfl

lemma hom_naturality_of_apply {H X X' Y Y' : Complex A}
    (F : H ⟶ homComplex A X X') (G : H ⟶ homComplex A Y Y')
    (a : X ⟶ Y) (b : X' ⟶ Y')
    (h : ∀ (p : ℤ) (g : H.X p),
      (F.f p g).comp (Cochain.ofHom b) (add_zero p) =
        (Cochain.ofHom a).comp (G.f p g) (zero_add p)) :
    F ≫ homPostcompose X b = G ≫ homPrecompose a Y' := by
  apply chain_ext_apply
  intro p g
  rw [chain_comp_apply, chain_comp_apply, homPostcompose_apply, homPrecompose_apply]
  exact h p g

end SerrePositivity.DifferentialGraded

end HomMapEvaluation

/-! ## HomNaturalityEvaluation（旧 SerrePositivity/DifferentialGraded/Complexes/HomNaturalityEvaluation.lean） -/

/-! # 主Homの可換式を斉次要素へ評価する -/

@[expose] public section HomNaturalityEvaluation
universe u

namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A]

lemma hom_naturality_apply {H X X' Y Y' : Complex A}
    (F : H ⟶ homComplex A X X') (G : H ⟶ homComplex A Y Y')
    (a : X ⟶ Y) (b : X' ⟶ Y')
    (h : F ≫ homPostcompose X b = G ≫ homPrecompose a Y')
    {p i n : ℤ} (hn : i + p = n) (g : H.X p) (x : X.X i) :
    b.f n ((F.f p g).v i n hn x) = (G.f p g).v i n hn (a.f i x) := by
  have hh := congrArg (fun k : H ⟶ homComplex A X Y' => k.f p g) h
  rw [chain_comp_apply, chain_comp_apply, homPostcompose_apply, homPrecompose_apply] at hh
  have hv := congrArg (fun k : Cochain X Y' p => k.v i n hn x) hh
  rw [cochain_comp_ofHom_apply, cochain_ofHom_comp_apply] at hv
  exact hv

end SerrePositivity.DifferentialGraded

end HomNaturalityEvaluation

/-! ## CoproductSupport（旧 SerrePositivity/DifferentialGraded/Complexes/CoproductSupport.lean） -/

/-! # dg加群のcompact性に使う余積の有限support表示 -/

@[expose] public section CoproductSupport
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits HomologicalComplex
variable (A : Type u) [CommRing A] {J : Type u}

/-- 任意の加群の余積cofanの元は、有限個の包含の像の和である。 -/
lemma moduleCofan_element_rep (F : J → ModuleCat.{u} A) (s : Cofan F)
    (hs : IsColimit s) (z : s.pt) :
    ∃ (t : Finset J) (c : ∀ j, F j), ∑ j ∈ t, s.inj j (c j) = z := by
  classical
  let e := (ModuleCat.coproductCoconeIsColimit F).coconePointUniqueUpToIso hs
  let w : DirectSum J (fun j => F j) := e.inv z
  have hi (j : J) (a : F j) : e.hom (DirectSum.of (fun j => F j) j a) = s.inj j a := by
    have h := (ModuleCat.coproductCoconeIsColimit F).comp_coconePointUniqueUpToIso_hom hs ⟨j⟩
    exact congrArg (fun k => k a) h
  have hw : e.hom w = z := by
    change e.hom (e.inv z) = z
    rw [← ModuleCat.comp_apply, e.inv_hom_id, ModuleCat.id_apply]
  have h := congrArg e.hom.hom (DirectSum.sum_support_of w)
  simp only [map_sum, hi, hw] at h
  exact ⟨w.support, fun j => w j, h⟩

/-- 次数ごとの余積表示。複体は非有界でよい。 -/
lemma complexCofan_element_rep (F : J → Complex A) (s : Cofan F) (hs : IsColimit s)
    (n : ℤ) (z : s.pt.X n) :
    ∃ (t : Finset J) (c : ∀ j, (F j).X n), ∑ j ∈ t, (s.inj j).f n (c j) = z := by
  let ev := HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) n
  have hn : IsColimit (Cofan.mk (s.pt.X n) (fun j => (s.inj j).f n)) :=
    isColimitCofanMkObjOfIsColimit ev F s.inj hs
  exact moduleCofan_element_rep A (fun j => (F j).X n) _ hn z

/-- cycleも有限個の成分cycleの像の和になる。 -/
lemma complexCofan_cycle_rep (F : J → Complex A) (s : Cofan F) (hs : IsColimit s)
    (n : ℤ) (z : complexCycles A s.pt n) :
    ∃ (t : Finset J) (c : ∀ j, complexCycles A (F j) n),
      ∑ j ∈ t, (s.inj j).f n (c j).val = z.val := by
  classical
  let pr (j : J) : s.pt ⟶ F j := hs.desc (Cofan.mk (F j) (Pi.single j (𝟙 (F j))))
  have hself (j : J) : s.inj j ≫ pr j = 𝟙 (F j) := by
    have h := hs.fac (Cofan.mk (F j) (Pi.single j (𝟙 (F j)))) ⟨j⟩
    change s.inj j ≫ pr j = (Pi.single j (𝟙 (F j)) : ∀ i, F i ⟶ F j) j at h
    rw [Pi.single_eq_same] at h
    exact h
  have hne (i j : J) (hij : i ≠ j) : s.inj i ≫ pr j = 0 := by
    have h := hs.fac (Cofan.mk (F j) (Pi.single j (𝟙 (F j)))) ⟨i⟩
    change s.inj i ≫ pr j = (Pi.single j (𝟙 (F j)) : ∀ i, F i ⟶ F j) i at h
    rw [Pi.single_eq_of_ne hij] at h
    exact h
  let c (j : J) : complexCycles A (F j) n :=
    ⟨(pr j).f n z.val, by
      have h := congrArg (fun k => k z.val) ((pr j).comm n (n + 1))
      change (F j).d n (n + 1) ((pr j).f n z.val) = 0
      change (F j).d n (n + 1) ((pr j).f n z.val) =
        (pr j).f (n + 1) (s.pt.d n (n + 1) z.val) at h
      have hz : s.pt.d n (n + 1) z.val = 0 := z.property
      rw [hz, map_zero] at h
      exact h⟩
  obtain ⟨t, b, hb⟩ := complexCofan_element_rep A F s hs n z.val
  have hc (j : J) (hj : j ∈ t) : (c j).val = b j := by
    change (pr j).f n z.val = b j
    rw [← hb, map_sum]
    calc
      _ = (pr j).f n ((s.inj j).f n (b j)) := Finset.sum_eq_single j
        (fun i _ hij => by
          rw [← ModuleCat.comp_apply, ← HomologicalComplex.comp_f, hne i j hij]
          rfl)
        (fun h => (h hj).elim)
      _ = b j := by
        rw [← ModuleCat.comp_apply, ← HomologicalComplex.comp_f, hself j]
        rfl
  refine ⟨t, c, ?_⟩
  calc
    _ = ∑ j ∈ t, (s.inj j).f n (b j) := Finset.sum_congr rfl (fun j hj => by rw [hc j hj])
    _ = z.val := hb

end SerrePositivity.DifferentialGraded
end

end CoproductSupport

/-! ## CoproductSubfamily（旧 SerrePositivity/DifferentialGraded/Complexes/CoproductSubfamily.lean） -/

/-! # 非有界複体の直和の部分族と分裂写像

## 概要
非有界複体の直和の部分族と分裂写像。

## 方針
既存の全dg自然なHom・作用・chain mapと局所化の計算を再利用する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。dg加群の導来作用・準同値比較の基盤。任意可換環上のMorita・K理論のモデル比較に再利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section CoproductSubfamily
universe u v

noncomputable section
namespace SerrePositivity.DifferentialGraded.ComplexCoproduct
open CategoryTheory Limits HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A] {J : Type v} [Small.{u} J]
variable (K : J → Complex A)

lemma cochain_ext {T : Complex A} (p : ℤ) (f g : Cochain (∐ K) T p)
    (h : ∀ j, (Cochain.ofHom (Sigma.ι K j)).comp f (zero_add p) =
      (Cochain.ofHom (Sigma.ι K j)).comp g (zero_add p)) : f = g := by
  apply Cochain.ext
  intro i n hn
  apply (isColimitOfPreserves (HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) i)
    (colimit.isColimit (Discrete.functor K))).hom_ext
  intro j
  change (Sigma.ι K j.as).f i ≫ f.v i n hn = (Sigma.ι K j.as).f i ≫ g.v i n hn
  simpa only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v] using
    congrArg (fun z : Cochain (K j.as) T p => z.v i n hn) (h j.as)

def cochainDesc (T : Complex A) (p : ℤ) (f : ∀ j, Cochain (K j) T p) :
    Cochain (∐ K) T p :=
  Cochain.mk (fun i n hn =>
    (isColimitOfHasCoproductOfPreservesColimit
      (HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) i) K).desc
      (Cofan.mk (T.X n) (fun j => (f j).v i n hn)))

lemma cochainDesc_precomp (T : Complex A) (p : ℤ) (f : ∀ j, Cochain (K j) T p) (j : J) :
    (Cochain.ofHom (Sigma.ι K j)).comp (cochainDesc K T p f) (zero_add p) = f j := by
  apply Cochain.ext
  intro i n hn
  rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, cochainDesc, Cochain.mk_v]
  exact (isColimitOfHasCoproductOfPreservesColimit
    (HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) i) K).fac
    (Cofan.mk (T.X n) (fun j => (f j).v i n hn)) ⟨j⟩

abbrev subfamily (S : Set J) : Complex A := ∐ (fun j : S => K j.val)

def inclusion (S : Set J) : subfamily K S ⟶ ∐ K :=
  Sigma.desc (fun j : S => Sigma.ι K j.val)

lemma ι_inclusion (S : Set J) (j : S) :
    Sigma.ι (fun j : S => K j.val) j ≫ inclusion K S = Sigma.ι K j.val :=
  Sigma.ι_comp_desc _ _

def projection (S : Set J) : ∐ K ⟶ subfamily K S := by
  classical
  exact Sigma.desc (fun j => if h : j ∈ S then Sigma.ι (fun j : S => K j.val) ⟨j, h⟩ else 0)

lemma ι_projection_mem (S : Set J) (j : J) (hj : j ∈ S) :
    Sigma.ι K j ≫ projection K S = Sigma.ι (fun j : S => K j.val) ⟨j, hj⟩ := by
  classical
  simp only [projection, Sigma.ι_comp_desc, dite_eq_left hj]

lemma ι_projection_not_mem (S : Set J) (j : J) (hj : j ∉ S) :
    Sigma.ι K j ≫ projection K S = 0 := by
  classical
  simp only [projection, Sigma.ι_comp_desc, dite_eq_right hj]

lemma inclusion_projection (S : Set J) : inclusion K S ≫ projection K S = 𝟙 _ := by
  apply Sigma.hom_ext
  intro j
  rw [← Category.assoc, ι_inclusion, ι_projection_mem K S j.val j.property, Category.comp_id]

instance inclusion_splitMono (S : Set J) : IsSplitMono (inclusion K S) :=
  ⟨⟨{ retraction := projection K S, id := inclusion_projection K S }⟩⟩

/-- 部分族間の成分選択。包含関係はこの写像の定義には不要。 -/
def select (S T : Set J) : subfamily K S ⟶ subfamily K T :=
  inclusion K S ≫ projection K T

lemma ι_select_mem (S T : Set J) (j : S) (hj : j.val ∈ T) :
    Sigma.ι (fun j : S => K j.val) j ≫ select K S T =
      Sigma.ι (fun j : T => K j.val) ⟨j.val, hj⟩ := by
  rw [select, ← Category.assoc, ι_inclusion, ι_projection_mem]

lemma ι_select_not_mem (S T : Set J) (j : S) (hj : j.val ∉ T) :
    Sigma.ι (fun j : S => K j.val) j ≫ select K S T = 0 := by
  rw [select, ← Category.assoc, ι_inclusion, ι_projection_not_mem K T j.val hj]

lemma select_self (S : Set J) : select K S S = 𝟙 _ := inclusion_projection K S

lemma select_inclusion (S T : Set J) (h : S ⊆ T) :
    select K S T ≫ inclusion K T = inclusion K S := by
  apply Sigma.hom_ext
  intro j
  rw [← Category.assoc, ι_select_mem K S T j (h j.property), ι_inclusion, ι_inclusion]

lemma select_comp (S T U : Set J) (h : S ⊆ T) :
    select K S T ≫ select K T U = select K S U := by
  change select K S T ≫ (inclusion K T ≫ projection K U) = _
  rw [← Category.assoc, select_inclusion K S T h]
  rfl

lemma select_zero (S T : Set J) (h : Disjoint S T) : select K S T = 0 := by
  apply Sigma.hom_ext
  intro j
  rw [ι_select_not_mem K S T j (fun hj => Set.disjoint_left.mp h j.property hj),
    Limits.comp_zero]

/-- 互いに素な二部分族から、上位の部分族の恒等射を分解する。 -/
lemma select_partition (S T U : Set J) (hS : S ⊆ U) (hT : T ⊆ U)
    (hST : Disjoint S T) (hU : U ⊆ S ∪ T) :
    select K U S ≫ select K S U + select K U T ≫ select K T U = 𝟙 _ := by
  classical
  apply Sigma.hom_ext
  intro j
  rw [Preadditive.comp_add, ← Category.assoc, ← Category.assoc, Category.comp_id]
  rcases hU j.property with hj | hj
  · rw [ι_select_mem K U S j hj,
      ι_select_mem K S U ⟨j.val, hj⟩ (hS hj),
      ι_select_not_mem K U T j (fun ht => Set.disjoint_left.mp hST hj ht),
      Limits.zero_comp, add_zero]
  · rw [ι_select_not_mem K U S j (fun hs => Set.disjoint_left.mp hST hs hj),
      Limits.zero_comp, zero_add, ι_select_mem K U T j hj,
      ι_select_mem K T U ⟨j.val, hj⟩ (hT hj)]

end SerrePositivity.DifferentialGraded.ComplexCoproduct
end

end CoproductSubfamily
