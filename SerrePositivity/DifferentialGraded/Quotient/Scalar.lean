module

public import SerrePositivity.DifferentialGraded.Quotient.Path.Construction
public import SerrePositivity.DifferentialGraded.Complexes.TensorJoin
public import SerrePositivity.DifferentialGraded.Complexes.TensorCoproduct
public import SerrePositivity.DifferentialGraded.Tensor.ScalarExtension.BalancedTensor
public import SerrePositivity.DifferentialGraded.Tensor.ScalarExtension.CategoriesAndModules
public import SerrePositivity.DifferentialGraded.Quotient.Erasure

/-!
# Quotient.Scalar

## 概要
10 本に分かれていた同主題の構成と比較をまとめる。

## 方針
対応表の依存順に連結し、元の宣言・証明・名前空間を保持する。

## 規約
各元ファイルの section を分離し、variable・option の局所的な作用を保つ。

## 使われ方
DifferentialGraded の入口と、この主題を使う検査・下流モジュールから import する。
-/

/-! ## AppendPrepend（旧 SerrePositivity/DifferentialGraded/Quotient/AppendPrepend.lean） -/

/-! # 有限path連結と先頭Hom作用の結合則 -/

@[expose] public section AppendPrepend
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

/-- 元のHomを先頭へ作用させる操作と有限path連結は結合する。 -/
@[reassoc] lemma appendMap_prepend {S : Set D} (w v : Word S) (x y z t : D) :
    (prependMap A D w x y z ▷ term A D v z t) ≫ appendMap A D w v x z t =
    (α_ (homObject A D x y) (term A D w y z) (term A D v z t)).hom ≫
      (homObject A D x y) ◁ appendMap A D w v y z t ≫ prependMap A D (w ++ v) x y t := by
  cases w with
  | nil => exact prependMap_assoc A D v x y z t
  | cons b w =>
    simpa only [prependMap, appendMap, term_cons, tensorHom_id, List.cons_append] using
      tensorJoin_right_action (homObject A D x y) (homObject A D y b.val)
        (homObject A D x b.val) (epsilonComplex A ⊗ term A D w b.val z)
        (term A D v z t) (epsilonComplex A ⊗ term A D (w ++ v) b.val t)
        (eComp (Complex A) x y b.val)
        ((α_ (epsilonComplex A) (term A D w b.val z) (term A D v z t)).hom ≫
          (epsilonComplex A) ◁ appendMap A D w v b.val z t)

end SerrePositivity.DifferentialGraded.DGQuotient
end

end AppendPrepend

/-! ## InternalComposition（旧 SerrePositivity/DifferentialGraded/Quotient/InternalComposition.lean） -/

/-! # 内部微分を持つ全path直和の合成

有限pathの連結を二つの直和のtensorへ延長する。この段階のchain mapは内部微分に関するもので、
最終微分との両立はε消去のLeibniz則から後続で証明する。
-/

@[expose] public section InternalComposition
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 内部微分に関する全有限pathの合成。 -/
def internalComposition (S : Set D) (x y z : D) :
    internalHom A D S x y ⊗ internalHom A D S y z ⟶ internalHom A D S x z :=
  tensorCoproductDesc (fun w : Word S => term A D w x y)
    (fun v : Word S => term A D v y z) (internalHom A D S x z)
    (fun w v => appendMap A D w v x y z ≫ ι A D S x z (w ++ v))

lemma internalComposition_ι (S : Set D) (x y z : D) (w v : Word S) :
    (ι A D S x y w ⊗ₘ ι A D S y z v) ≫ internalComposition A D S x y z =
      appendMap A D w v x y z ≫ ι A D S x z (w ++ v) :=
  tensorCoproductDesc_ι _ _ _ _ w v

/-- 内部path Hom二つのtensorからのchain mapは、各二つのpath上で決まる。 -/
lemma internalComposition_hom_ext (S : Set D) (x y z : D) {T : Complex A}
    (f g : internalHom A D S x y ⊗ internalHom A D S y z ⟶ T)
    (h : ∀ w v : Word S, (ι A D S x y w ⊗ₘ ι A D S y z v) ≫ f =
      (ι A D S x y w ⊗ₘ ι A D S y z v) ≫ g) : f = g :=
  tensorCoproduct_hom_ext _ _ f g h

lemma internalComposition_original_left (S : Set D) (x y z : D) (w : Word S) :
    (originalHom A D S x y ⊗ₘ ι A D S y z w) ≫ internalComposition A D S x y z =
      prependMap A D w x y z ≫ ι A D S x z w :=
  internalComposition_ι A D S x y z [] w

lemma internalComposition_original_original (S : Set D) (x y z : D) :
    (originalHom A D S x y ⊗ₘ originalHom A D S y z) ≫ internalComposition A D S x y z =
      eComp (Complex A) x y z ≫ originalHom A D S x z :=
  internalComposition_ι A D S x y z [] []

/-- 純tensor上で、二つのpathの斉次成分は連結後のpath包含へ送られる。 -/
lemma internalComposition_apply (S : Set D) (x y z : D) (w v : Word S)
    (p q n : ℤ) (hn : p + q = n) (f : (term A D w x y).X p)
    (g : (term A D v y z).X q) :
    (internalComposition A D S x y z).f n
      (ιTensorObj (internalHom A D S x y) (internalHom A D S y z) p q n hn
        ((ι A D S x y w).f p f ⊗ₜ[A] (ι A D S y z v).f q g)) =
    (ι A D S x z (w ++ v)).f n ((appendMap A D w v x y z).f n
      (ιTensorObj (term A D w x y) (term A D v y z) p q n hn (f ⊗ₜ[A] g))) := by
  have h := congrArg (fun F : term A D w x y ⊗ term A D v y z ⟶ internalHom A D S x z =>
    F.f n (ιTensorObj (term A D w x y) (term A D v y z) p q n hn (f ⊗ₜ[A] g)))
    (internalComposition_ι A D S x y z w v)
  change (internalComposition A D S x y z).f n
    ((ι A D S x y w ⊗ₘ ι A D S y z v).f n
      (ιTensorObj (term A D w x y) (term A D v y z) p q n hn (f ⊗ₜ[A] g))) = _ at h
  rw [tensorMap_apply] at h
  exact h

end SerrePositivity.DifferentialGraded.DGQuotient
end

end InternalComposition

/-! ## InternalUnit（旧 SerrePositivity/DifferentialGraded/Quotient/InternalUnit.lean） -/

/-! # 全path直和の合成の左単位

内部微分の圏で単位写像と左単位則を構成する。最終Hom微分への移送は後続で扱う。
-/

@[expose] public section InternalUnit
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits MonoidalCategory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 元のdg圏の単位を空pathへ入れた写像。 -/
def internalIdentity (S : Set D) (x : D) : 𝟙_ (Complex A) ⟶ internalHom A D S x x :=
  eId (Complex A) x ≫ originalHom A D S x x

lemma internalComposition_left_unit (S : Set D) (x y : D) :
    (λ_ (internalHom A D S x y)).inv ≫ internalIdentity A D S x ▷ internalHom A D S x y ≫
      internalComposition A D S x x y = 𝟙 _ := by
  apply hom_ext A D S x y
  intro w
  simp only [internalIdentity, comp_whiskerRight, Category.assoc, Category.comp_id]
  rw [leftUnitor_inv_naturality_assoc, whisker_exchange_assoc, whisker_exchange_assoc,
    ← tensorHom_def_assoc, internalComposition_original_left, prependMap_left_unit_assoc]

end SerrePositivity.DifferentialGraded.DGQuotient
end

end InternalUnit

/-! ## TensorPathCochainExt（旧 SerrePositivity/DifferentialGraded/Quotient/TensorPathCochainExt.lean） -/

/-! # 左tensorした全path直和のcochainの判定 -/

@[expose] public section TensorPathCochainExt
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 左tensorしたpath直和の任意次数cochainも各pathへの制限で判定できる。 -/
lemma tensorLeftPathCochain_ext (S : Set D) (x y : D) (K : Complex A) {T : Complex A} (p : ℤ)
    (f g : Cochain (K ⊗ internalHom A D S x y) T p)
    (h : ∀ w : Word S, (Cochain.ofHom (K ◁ ι A D S x y w)).comp f (zero_add p) =
      (Cochain.ofHom (K ◁ ι A D S x y w)).comp g (zero_add p)) : f = g := by
  apply Cochain.ext
  intro i n hn
  let ev := HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) i
  apply (isColimitOfPreserves ev
    (tensorLeftCoproductIsColimit K (fun w : Word S => term A D w x y))).hom_ext
  rintro ⟨w⟩
  change (K ◁ ι A D S x y w).f i ≫ f.v i n hn =
    (K ◁ ι A D S x y w).f i ≫ g.v i n hn
  simpa only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v] using
    congrArg (fun z : Cochain (K ⊗ term A D w x y) T p => z.v i n hn) (h w)

end SerrePositivity.DifferentialGraded.DGQuotient
end

end TensorPathCochainExt

/-! ## TensorRightPathCochainExt（旧 SerrePositivity/DifferentialGraded/Quotient/TensorRightPathCochainExt.lean） -/

/-! # 右tensorした全path直和の任意次数cochainの判定 -/

@[expose] public section TensorRightPathCochainExt
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma tensorRightPathCochain_ext (S : Set D) (x y : D) (K : Complex A) {T : Complex A} (p : ℤ)
    (f g : Cochain (internalHom A D S x y ⊗ K) T p)
    (h : ∀ w : Word S, (Cochain.ofHom (ι A D S x y w ▷ K)).comp f (zero_add p) =
      (Cochain.ofHom (ι A D S x y w ▷ K)).comp g (zero_add p)) : f = g := by
  apply Cochain.ext
  intro i n hn
  let ev := HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) i
  apply (isColimitOfPreserves ev
    (tensorRightCoproductIsColimit K (fun w : Word S => term A D w x y))).hom_ext
  rintro ⟨w⟩
  change (ι A D S x y w ▷ K).f i ≫ f.v i n hn =
    (ι A D S x y w ▷ K).f i ≫ g.v i n hn
  simpa only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v] using
    congrArg (fun z : Cochain (term A D w x y ⊗ K) T p => z.v i n hn) (h w)

end SerrePositivity.DifferentialGraded.DGQuotient
end

end TensorRightPathCochainExt

/-! ## TensorTwoPathCochainExt（旧 SerrePositivity/DifferentialGraded/Quotient/TensorTwoPathCochainExt.lean） -/

/-! # 二つの全path直和のtensorからの任意次数cochainの判定 -/

@[expose] public section TensorTwoPathCochainExt
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma tensorTwoPathCochain_ext (S : Set D) (x y z : D) {T : Complex A} (p : ℤ)
    (f g : Cochain (internalHom A D S x y ⊗ internalHom A D S y z) T p)
    (h : ∀ w v : Word S, (Cochain.ofHom (ι A D S x y w ⊗ₘ ι A D S y z v)).comp f
      (zero_add p) = (Cochain.ofHom (ι A D S x y w ⊗ₘ ι A D S y z v)).comp g (zero_add p)) :
    f = g := by
  apply tensorRightPathCochain_ext A D S x y (internalHom A D S y z) p
  intro w
  apply tensorLeftPathCochain_ext A D S y z (term A D w x y) p
  intro v
  simpa only [← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp,
    ← tensorHom_def'] using h w v

end SerrePositivity.DifferentialGraded.DGQuotient
end

end TensorTwoPathCochainExt

/-! ## ScalarExtensionPaths（旧 SerrePositivity/DifferentialGraded/Quotient/ScalarExtensionPaths.lean） -/

/-! # 同じ有限語を添字とする path 項の係数変更

空語も含めて Word S = List S を変更しない。ここでは内部微分を扱う。
-/

@[expose] public section ScalarExtensionPaths
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits MonoidalCategory
open SerrePositivity.DifferentialGraded.ScalarExtension
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
variable (D : Type v) [DGCategory A D]

/-- 同じ有限語の各 Hom と ε に係数変更を施す。 -/
def termBaseChangeIso {S : Set D} : ∀ (w : Word S) (x y : D),
    (extension φ).obj (term A D w x y) ≅ term A' (DGBaseChange φ D) w x y
  | [], _, _ => Iso.refl _
  | b :: w, x, y =>
    tensorIso φ (homObject A D x b.val) (epsilonComplex A ⊗ term A D w b.val y) ≪≫
      cochainTensorIso (Iso.refl _)
        (tensorIso φ (epsilonComplex A) (term A D w b.val y) ≪≫
          cochainTensorIso (sphereIso φ (-1)) (termBaseChangeIso w b.val y))

@[simp]
lemma termBaseChangeIso_nil (S : Set D) (x y : D) :
    termBaseChangeIso φ D ([] : Word S) x y = Iso.refl _ := rfl

lemma termBaseChangeIso_cons_hom {S : Set D} (b : S) (w : Word S) (x y : D) :
    (termBaseChangeIso φ D (b :: w) x y).hom =
      (tensorIso φ (homObject A D x b.val) (epsilonComplex A ⊗ term A D w b.val y)).hom ≫
        (extension φ).obj (homObject A D x b.val) ◁
          ((tensorIso φ (epsilonComplex A) (term A D w b.val y)).hom ≫
            ((sphereIso φ (-1)).hom ⊗ₘ (termBaseChangeIso φ D w b.val y).hom)) := by
  simp only [termBaseChangeIso, Iso.trans_hom, cochainTensorIso,
    MonoidalCategory.tensorIso_hom, Iso.refl_hom, id_tensorHom]

variable [Small.{u} D]

set_option synthInstance.maxHeartbeats 40000
/-- path の直和は同じ Word S を添字とする直和へ移る。 -/
def internalHomBaseChangeIso (S : Set D) (x y : D) :
    (extension φ).obj (internalHom A D S x y) ≅
      internalHom A' (DGBaseChange φ D) S x y :=
  coproductIso φ (fun w : Word S => term A D w x y) ≪≫
    Sigma.mapIso (fun w : Word S => termBaseChangeIso φ D w x y)

@[reassoc (attr := simp)]
lemma map_ι_internalHomBaseChangeIso (S : Set D) (x y : D) (w : Word S) :
    (extension φ).map (ι A D S x y w) ≫ (internalHomBaseChangeIso φ D S x y).hom =
      (termBaseChangeIso φ D w x y).hom ≫ ι A' (DGBaseChange φ D) S x y w := by
  letI : HasColimitsOfSize.{u, u} (Complex A') := ⟨fun _ _ => inferInstance⟩
  simp only [internalHomBaseChangeIso, Iso.trans_hom]
  rw [show ι A D S x y w = Sigma.ι (fun w : Word S => term A D w x y) w from rfl,
    map_ι_coproductIso_assoc, Sigma.ι_mapIso_hom]
  rfl

@[reassoc (attr := simp)]
lemma map_originalHom_internalHomBaseChangeIso (S : Set D) (x y : D) :
    (extension φ).map (originalHom A D S x y) ≫ (internalHomBaseChangeIso φ D S x y).hom =
      originalHom A' (DGBaseChange φ D) S x y := by
  have h := map_ι_internalHomBaseChangeIso φ D S x y []
  simp only [termBaseChangeIso_nil, Iso.refl_hom, Category.id_comp] at h
  convert h using 1 <;> rfl

end SerrePositivity.DifferentialGraded.DGQuotient
end

end ScalarExtensionPaths

/-! ## ScalarExtensionEpsilon（旧 SerrePositivity/DifferentialGraded/Quotient/ScalarExtensionEpsilon.lean） -/

/-! # 係数変更と次数 +1 の ε 消去 -/

@[expose] public section ScalarExtensionEpsilon
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits MonoidalCategory HomologicalComplex CochainComplex HomComplex
open SerrePositivity.DifferentialGraded.ScalarExtension
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')

/-- 生成元 ε↦1 の次数 +1 cochain は係数変更と可換する。 -/
lemma eraseEpsilon_baseChange :
    CochainSquare φ (sphereIso φ (-1)).hom (unitIso φ).hom (eraseEpsilon A) (eraseEpsilon A') := by
  let := φ.toAlgebra
  intro i j hij
  by_cases hi : i = -1
  · subst i
    have hj : j = 0 := by omega
    cases hj
    apply (cancel_epi ((ModuleCat.extendScalars φ).map
      (singleObjXSelf (.up ℤ) (-1) (𝟙_ (ModuleCat A))).inv)).1
    apply ((ModuleCat.extendRestrictScalarsAdj φ).homEquiv _ _).injective
    apply ModuleCat.hom_ext
    apply LinearMap.ext_ring
    change (unitIso φ).hom.f 0
      ((ModuleCat.extendScalars φ).map ((eraseEpsilon A).v (-1) 0 (by omega))
        ((1 : A') ⊗ₜ[A] (singleObjXSelf (.up ℤ) (-1) (𝟙_ (ModuleCat A))).inv (1 : A))) =
      (eraseEpsilon A').v (-1) 0 (by omega)
        ((sphereIso φ (-1)).hom.f (-1)
          ((1 : A') ⊗ₜ[A] (singleObjXSelf (.up ℤ) (-1) (𝟙_ (ModuleCat A))).inv (1 : A)))
    have hm := ModuleCat.ExtendScalars.map_tmul φ
      ((eraseEpsilon A).v (-1) 0 (by omega)) (1 : A')
      ((singleObjXSelf (.up ℤ) (-1) (𝟙_ (ModuleCat A))).inv (1 : A))
    erw [hm]
    erw [eraseEpsilon_generator A]
    erw [sphereIso_one φ (-1)]
  · have hz := (ModuleCat.extendScalars φ).map_isZero
      (isZero_single_obj_X (.up ℤ) (-1) (𝟙_ (ModuleCat A)) i hi)
    exact hz.eq_of_src _ _

end SerrePositivity.DifferentialGraded.DGQuotient
end

end ScalarExtensionEpsilon

/-! ## ScalarExtensionComposition（旧 SerrePositivity/DifferentialGraded/Quotient/ScalarExtensionComposition.lean） -/

/-! # 係数変更と有限 path の先頭合成 -/

@[expose] public section ScalarExtensionComposition
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded.ScalarExtension
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
variable (D : Type v) [DGCategory A D]

lemma termBaseChangeIso_cons_compare {S : Set D} (b : S) (w : Word S) (x y : D) :
    (termBaseChangeIso φ D (b :: w) x y).hom =
      compareTensor φ (𝟙 ((extension φ).obj (homObject A D x b.val)))
        (compareTensor φ (sphereIso φ (-1)).hom (termBaseChangeIso φ D w b.val y).hom) := by
  rw [termBaseChangeIso_cons_hom]
  simp only [compareTensor, id_tensorHom]

lemma composition_baseChange (x y z : D) :
    (extension φ).map (eComp (Complex A) x y z) ≫ 𝟙 _ =
      compareTensor φ (𝟙 ((extension φ).obj (homObject A D x y)))
        (𝟙 ((extension φ).obj (homObject A D y z))) ≫
          eComp (Complex A') (C := DGBaseChange φ D) x y z := by
  change _ ≫ 𝟙 _ = ((tensorIso φ _ _).hom ≫ (𝟙 _ ⊗ₘ 𝟙 _)) ≫
    ((tensorIso φ _ _).inv ≫ (extension φ).map (eComp (Complex A) x y z))
  simp only [tensorHom_id, id_whiskerRight, Category.comp_id, Iso.hom_inv_id_assoc]

lemma prependMap_baseChange {S : Set D} (w : Word S) (x y z : D) :
    (extension φ).map (prependMap A D w x y z) ≫ (termBaseChangeIso φ D w x z).hom =
      compareTensor φ (𝟙 ((extension φ).obj (homObject A D x y)))
        (termBaseChangeIso φ D w y z).hom ≫ prependMap A' (DGBaseChange φ D) w x y z := by
  cases w with
  | nil => exact composition_baseChange φ D x y z
  | cons b w =>
    let U := homObject A D x y
    let V := homObject A D y b.val
    let W := homObject A D x b.val
    let T := epsilonComplex A ⊗ term A D w b.val z
    let T' := epsilonComplex A' ⊗ term A' (DGBaseChange φ D) w b.val z
    let t : (extension φ).obj T ⟶ T' :=
      compareTensor φ (sphereIso φ (-1)).hom (termBaseChangeIso φ D w b.val z).hom
    let c : U ⊗ V ⟶ W := eComp (Complex A) x y b.val
    let c' := eComp (Complex A') (C := DGBaseChange φ D) x y b.val
    have ht := compareTensor_naturality φ c (𝟙 T) c' (𝟙 T')
      (a := compareTensor φ (𝟙 ((extension φ).obj U)) (𝟙 ((extension φ).obj V)))
      (b := t) (c := 𝟙 ((extension φ).obj W)) (d := t)
      (composition_baseChange φ D x y b.val) (by simp)
    have ha := compareTensor_associator_inv φ
      (𝟙 ((extension φ).obj U)) (𝟙 ((extension φ).obj V)) t
    simp only [prependMap, CategoryTheory.Functor.map_comp, Category.assoc,
      termBaseChangeIso_cons_compare]
    change (extension φ).map (α_ U V T).inv ≫
      (extension φ).map (c ⊗ₘ 𝟙 T) ≫ compareTensor φ (𝟙 _) t =
        compareTensor φ (𝟙 _) (compareTensor φ (𝟙 _) t) ≫
          (α_ _ _ T').inv ≫ (c' ⊗ₘ 𝟙 T')
    rw [ht, ← Category.assoc, ha, Category.assoc]

set_option maxHeartbeats 800000 in
-- 再帰する path の tensor 比較の型を各段階で照合する。
lemma appendMap_baseChange {S : Set D} (w v : Word S) (x y z : D) :
    (extension φ).map (appendMap A D w v x y z) ≫
        (termBaseChangeIso φ D (w ++ v) x z).hom =
      compareTensor φ (termBaseChangeIso φ D w x y).hom (termBaseChangeIso φ D v y z).hom ≫
        appendMap A' (DGBaseChange φ D) w v x y z := by
  induction w generalizing x y z with
  | nil => exact prependMap_baseChange φ D v x y z
  | cons b w ih =>
    let H := homObject A D x b.val
    let E := epsilonComplex A
    let P := term A D w b.val y
    let Q := term A D v y z
    let R := term A D (w ++ v) b.val z
    let H' := homObject A' (DGBaseChange φ D) x b.val
    let E' := epsilonComplex A'
    let P' := term A' (DGBaseChange φ D) w b.val y
    let Q' := term A' (DGBaseChange φ D) v y z
    let R' := term A' (DGBaseChange φ D) (w ++ v) b.val z
    let e : (extension φ).obj E ⟶ E' := (sphereIso φ (-1)).hom
    let p : (extension φ).obj P ⟶ P' := (termBaseChangeIso φ D w b.val y).hom
    let q : (extension φ).obj Q ⟶ Q' := (termBaseChangeIso φ D v y z).hom
    let r : (extension φ).obj R ⟶ R' := (termBaseChangeIso φ D (w ++ v) b.val z).hom
    let f : P ⊗ Q ⟶ R := appendMap A D w v b.val y z
    let f' : P' ⊗ Q' ⟶ R' := appendMap A' (DGBaseChange φ D) w v b.val y z
    have ht := compareTensor_naturality φ (𝟙 E) f (𝟙 E') f'
      (a := e) (b := compareTensor φ p q) (c := e) (d := r) (by simp) (ih b.val y z)
    have ha := compareTensor_associator φ e p q
    let g : (E ⊗ P) ⊗ Q ⟶ E ⊗ R := (α_ E P Q).hom ≫ E ◁ f
    let g' : (E' ⊗ P') ⊗ Q' ⟶ E' ⊗ R' := (α_ E' P' Q').hom ≫ E' ◁ f'
    have hg : (extension φ).map g ≫ compareTensor φ e r =
        compareTensor φ (compareTensor φ e p) q ≫ g' := by
      dsimp only [g, g']
      rw [CategoryTheory.Functor.map_comp, Category.assoc]
      erw [ht]
      rw [← Category.assoc, ha, Category.assoc]
      rw [id_tensorHom]
    have houter := compareTensor_naturality φ (𝟙 H) g (𝟙 H') g'
      (a := 𝟙 H') (b := compareTensor φ (compareTensor φ e p) q)
      (c := 𝟙 H') (d := compareTensor φ e r)
      (by rw [CategoryTheory.Functor.map_id, Category.comp_id]; rfl) hg
    have hα := compareTensor_associator φ (𝟙 H') (compareTensor φ e p) q
    simp only [appendMap, List.cons_append, CategoryTheory.Functor.map_comp, Category.assoc,
      termBaseChangeIso_cons_compare]
    change (extension φ).map (α_ H (E ⊗ P) Q).hom ≫
      (extension φ).map (H ◁ g) ≫ compareTensor φ (𝟙 H') (compareTensor φ e r) =
        compareTensor φ (compareTensor φ (𝟙 H') (compareTensor φ e p)) q ≫
          (α_ H' (E' ⊗ P') Q').hom ≫ H' ◁ g'
    erw [houter]
    rw [← Category.assoc, hα, Category.assoc]
    rw [id_tensorHom]

variable [Small.{u} D]

lemma internalComposition_baseChange (S : Set D) (x y z : D) :
    (extension φ).map (internalComposition A D S x y z) ≫
        (internalHomBaseChangeIso φ D S x z).hom =
      compareTensor φ (internalHomBaseChangeIso φ D S x y).hom
        (internalHomBaseChangeIso φ D S y z).hom ≫
          internalComposition A' (DGBaseChange φ D) S x y z := by
  apply ((adjunction φ).homEquiv _ _).injective
  apply internalComposition_hom_ext A D S x y z
  intro w v
  let c := compareTensor φ (termBaseChangeIso φ D w x y).hom (termBaseChangeIso φ D v y z).hom
  let t := appendMap A' (DGBaseChange φ D) w v x y z ≫
    ι A' (DGBaseChange φ D) S x z (w ++ v)
  have hl : (extension φ).map (ι A D S x y w ⊗ₘ ι A D S y z v) ≫
      ((extension φ).map (internalComposition A D S x y z) ≫
        (internalHomBaseChangeIso φ D S x z).hom) = c ≫ t := by
    rw [← CategoryTheory.Functor.map_comp_assoc, internalComposition_ι,
      CategoryTheory.Functor.map_comp, Category.assoc, map_ι_internalHomBaseChangeIso,
      ← Category.assoc, appendMap_baseChange, Category.assoc]
  have ht := compareTensor_naturality φ (ι A D S x y w) (ι A D S y z v)
    (ι A' (DGBaseChange φ D) S x y w) (ι A' (DGBaseChange φ D) S y z v)
    (map_ι_internalHomBaseChangeIso φ D S x y w)
    (map_ι_internalHomBaseChangeIso φ D S y z v)
  have hr : (extension φ).map (ι A D S x y w ⊗ₘ ι A D S y z v) ≫
      (compareTensor φ (internalHomBaseChangeIso φ D S x y).hom
        (internalHomBaseChangeIso φ D S y z).hom ≫
          internalComposition A' (DGBaseChange φ D) S x y z) = c ≫ t := by
    rw [← Category.assoc, ht, Category.assoc, internalComposition_ι]
  have h := congrArg ((adjunction φ).homEquiv _ _) (hl.trans hr.symm)
  rw [(adjunction φ).homEquiv_naturality_left,
    (adjunction φ).homEquiv_naturality_left] at h
  exact h

end SerrePositivity.DifferentialGraded.DGQuotient
end

end ScalarExtensionComposition

/-! ## ScalarExtensionErasure（旧 SerrePositivity/DifferentialGraded/Quotient/ScalarExtensionErasure.lean） -/

/-! # 固定 path 上の ε 消去と係数変更 -/

@[expose] public section ScalarExtensionErasure
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits MonoidalCategory HomologicalComplex CochainComplex HomComplex
open SerrePositivity.DifferentialGraded.ScalarExtension
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')

lemma eraseHead_baseChange {P : Complex A} {P' : Complex A'} (a : (extension φ).obj P ⟶ P') :
    CochainSquare φ (compareTensor φ (sphereIso φ (-1)).hom a) a
      (eraseHead A P) (eraseHead A' P') := by
  have hε := cochainSquare_tensorRight φ a (eraseEpsilon_baseChange φ)
  have hunitor := cochainSquare_ofHom φ (compareTensor φ (unitIso φ).hom a) a
    (λ_ P).hom (λ_ P').hom (compareTensor_leftUnitor φ a)
  exact cochainSquare_comp φ hε hunitor (add_zero 1)

lemma eraseMiddle_baseChange {P Q : Complex A} {P' Q' : Complex A'}
    (a : (extension φ).obj P ⟶ P') (b : (extension φ).obj Q ⟶ Q') :
    CochainSquare φ (compareTensor φ a (compareTensor φ (sphereIso φ (-1)).hom b))
      (compareTensor φ a b) (eraseMiddle A P Q) (eraseMiddle A' P' Q') := by
  rw [eraseMiddle_eq_tensorLeft, eraseMiddle_eq_tensorLeft]
  exact cochainSquare_tensorLeft φ a (eraseHead_baseChange φ b)

variable (D : Type v) [DGCategory A D]

lemma eraseFirst_baseChange {S : Set D} (b : S) (w : Word S) (x y : D) :
    CochainSquare φ (termBaseChangeIso φ D (b :: w) x y).hom
      (termBaseChangeIso φ D w x y).hom (eraseFirst A D b w x y)
        (eraseFirst A' (DGBaseChange φ D) b w x y) := by
  rw [termBaseChangeIso_cons_compare]
  have hm := eraseMiddle_baseChange φ
    (𝟙 ((extension φ).obj (homObject A D x b.val)))
    (termBaseChangeIso φ D w b.val y).hom
  have hp := cochainSquare_ofHom φ
    (compareTensor φ (𝟙 ((extension φ).obj (homObject A D x b.val)))
      (termBaseChangeIso φ D w b.val y).hom)
    (termBaseChangeIso φ D w x y).hom
    (prependMap A D w x b.val y) (prependMap A' (DGBaseChange φ D) w x b.val y)
    (prependMap_baseChange φ D w x b.val y)
  exact cochainSquare_comp φ hm hp (add_zero 1)

lemma eraseFace_baseChange {S : Set D} (w : Word S) (i : ℕ) (x y : D) :
    CochainSquare φ (termBaseChangeIso φ D w x y).hom
      (termBaseChangeIso φ D (w.eraseIdx i) x y).hom (eraseFace A D w i x y)
        (eraseFace A' (DGBaseChange φ D) w i x y) := by
  induction w generalizing i x y with
  | nil => exact cochainSquare_zero φ _ _
  | cons b w ih =>
    cases i with
    | zero => exact eraseFirst_baseChange φ D b w x y
    | succ i =>
      have hε := cochainSquare_tensorLeft φ (sphereIso φ (-1)).hom (ih i b.val y)
      have hH := cochainSquare_tensorLeft φ
        (𝟙 ((extension φ).obj (homObject A D x b.val))) hε
      simp only [List.eraseIdx_cons_succ, termBaseChangeIso_cons_compare]
      convert hH using 1 <;> rfl

variable [Small.{u} D]

lemma eraseSummand_baseChange {S : Set D} (w : Word S) (i : ℕ) (x y : D) :
    CochainSquare φ (termBaseChangeIso φ D w x y).hom
      (internalHomBaseChangeIso φ D S x y).hom (eraseSummand A D w i x y)
        (eraseSummand A' (DGBaseChange φ D) w i x y) :=
  cochainSquare_comp φ (eraseFace_baseChange φ D w i x y)
    (cochainSquare_ofHom φ _ _ (ι A D S x y (w.eraseIdx i))
      (ι A' (DGBaseChange φ D) S x y (w.eraseIdx i))
        (map_ι_internalHomBaseChangeIso φ D S x y (w.eraseIdx i))) (add_zero 1)

lemma eraseRow_baseChange {S : Set D} (w : Word S) (x y : D) :
    CochainSquare φ (termBaseChangeIso φ D w x y).hom
      (internalHomBaseChangeIso φ D S x y).hom (eraseRow A D w x y)
        (eraseRow A' (DGBaseChange φ D) w x y) := by
  have hs (s : Finset ℕ) : CochainSquare φ (termBaseChangeIso φ D w x y).hom
      (internalHomBaseChangeIso φ D S x y).hom
      (∑ i ∈ s, eraseSummand A D w i x y)
      (∑ i ∈ s, eraseSummand A' (DGBaseChange φ D) w i x y) := by
    induction s using Finset.induction_on with
    | empty =>
      simpa only [Finset.sum_empty] using (cochainSquare_zero φ
        (termBaseChangeIso φ D w x y).hom (internalHomBaseChangeIso φ D S x y).hom)
    | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      exact cochainSquare_add φ (eraseSummand_baseChange φ D w i x y) ih
  exact hs (Finset.range w.length)

lemma erasure_baseChange (S : Set D) (x y : D) :
    CochainSquare φ (internalHomBaseChangeIso φ D S x y).hom
      (internalHomBaseChangeIso φ D S x y).hom (erasure A D S x y)
        (erasure A' (DGBaseChange φ D) S x y) := by
  intro i j hij
  let E := HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) i
  let hc := isColimitOfHasCoproductOfPreservesColimit E (fun w : Word S => term A D w x y)
  apply (isColimitOfPreserves (ModuleCat.extendScalars φ) hc).hom_ext
  rintro ⟨w⟩
  change (ModuleCat.extendScalars φ).map ((ι A D S x y w).f i) ≫
      (ModuleCat.extendScalars φ).map ((erasure A D S x y).v i j hij) ≫
        (internalHomBaseChangeIso φ D S x y).hom.f j =
    (ModuleCat.extendScalars φ).map ((ι A D S x y w).f i) ≫
      (internalHomBaseChangeIso φ D S x y).hom.f i ≫
        (erasure A' (DGBaseChange φ D) S x y).v i j hij
  have hι := congrArg (fun f => f.f i) (map_ι_internalHomBaseChangeIso φ D S x y w)
  have hrow := eraseRow_baseChange φ D w x y i j hij
  have hsrc := congrArg (fun f => f.v i j hij) (erasure_precomp A D S x y w)
  have htgt := congrArg (fun f => f.v i j hij)
    (erasure_precomp A' (DGBaseChange φ D) S x y w)
  simp only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v] at hsrc htgt
  simp only [HomologicalComplex.comp_f] at hι
  change (ModuleCat.extendScalars φ).map ((ι A D S x y w).f i) ≫
      (internalHomBaseChangeIso φ D S x y).hom.f i =
    (termBaseChangeIso φ D w x y).hom.f i ≫ (ι A' (DGBaseChange φ D) S x y w).f i at hι
  rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, hsrc, hrow,
    ← Category.assoc, hι, Category.assoc, htgt]

end SerrePositivity.DifferentialGraded.DGQuotient
end

end ScalarExtensionErasure
