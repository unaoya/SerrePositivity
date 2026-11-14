module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.DifferentialGraded.Quotient.Append
public import SerrePositivity.DifferentialGraded.Quotient.Composition
public import SerrePositivity.DifferentialGraded.Quotient.Scalar
public import SerrePositivity.DifferentialGraded.Functor.ModuleValued
public import SerrePositivity.DifferentialGraded.Quotient.Erasure
public import SerrePositivity.DifferentialGraded.Complexes.TensorZeroCochain
public import SerrePositivity.DifferentialGraded.Quotient.Path.Construction
public import SerrePositivity.DifferentialGraded.Complexes.TensorShift
public import SerrePositivity.DifferentialGraded.Complexes.TensorJoin



public import SerrePositivity.DifferentialGraded.Complexes.Perturbation

/-!
# Quotient.Path.Evaluation

## 概要
指定収縮による path 評価と内部微分・合成の整合性をまとめる。

## 方針
対応表の依存順に連結し、元の宣言・証明・名前空間を保持する。

## 規約
各元ファイルの section を分離し、variable・option の局所的な作用を保つ。

## 使われ方
DifferentialGraded の入口と、この主題を使う検査・下流モジュールから import する。
-/

/-! ## PathGeneration（旧 SerrePositivity/DifferentialGraded/Quotient/PathGeneration.lean） -/

/-! # 元のHomと指定εの反復合成によるpathの生成式 -/

@[expose] public section PathGeneration
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma prefixPath_generator {S : Set D} (b : S) (x y : D) (p q n : ℤ)
    (hn : p + ((-1) + q) = n) (a : (homObject A D x b.val).X p)
    (t : (internalHom A D S b.val y).X q) :
    (prefixPath A D b x y).f n
      (ιTensorObj (homObject A D x b.val) (epsilonComplex A ⊗ internalHom A D S b.val y)
        p ((-1) + q) n hn (a ⊗ₜ[A]
          ιTensorObj (epsilonComplex A) (internalHom A D S b.val y) (-1) q ((-1) + q) rfl
            ((singleObjXSelf (.up ℤ) (-1) (𝟙_ (ModuleCat.{u} A))).inv (1 : A) ⊗ₜ[A] t))) =
    forward A (x := (⟨x⟩ : QuotientObject D S)) (y := ⟨b.val⟩) (z := ⟨y⟩)
      ((originalHomInclusion A D S x b.val).f p a)
      (forward A (x := (⟨b.val⟩ : QuotientObject D S)) (y := ⟨b.val⟩) (z := ⟨y⟩)
        (epsilonElement A D S b) t rfl) hn := by
  have h := congrArg (fun f : homObject A D x b.val ⊗
      (epsilonComplex A ⊗ internalHom A D S b.val y) ⟶ internalHom A D S x y =>
    f.f n (ιTensorObj (homObject A D x b.val) (epsilonComplex A ⊗ internalHom A D S b.val y)
      p ((-1) + q) n hn (a ⊗ₜ[A]
        ιTensorObj (epsilonComplex A) (internalHom A D S b.val y) (-1) q ((-1) + q) rfl
          ((singleObjXSelf (.up ℤ) (-1) (𝟙_ (ModuleCat.{u} A))).inv (1 : A) ⊗ₜ[A] t))))
    (prefixPath_generated A D b x y)
  simp only [internalPrepend, chain_comp_apply, whiskerLeft_apply, whiskerRight_apply] at h
  change _ = (quotientComposition A D S x b.val y).f n
    (ιTensorObj (quotientHom A D S x b.val) (quotientHom A D S b.val y) p ((-1) + q) n hn
      ((originalHomInclusion A D S x b.val).f p a ⊗ₜ[A]
        (quotientComposition A D S b.val b.val y).f ((-1) + q)
          (ιTensorObj (quotientHom A D S b.val b.val) (quotientHom A D S b.val y)
            (-1) q ((-1) + q) rfl (epsilonElement A D S b ⊗ₜ[A] t))))
  rw [quotientComposition_apply, quotientComposition_apply, originalHomInclusion_f]
  exact h.symm

lemma path_inclusion_generator {S : Set D} (b : S) (w : Word S) (x y : D) (p q n : ℤ)
    (hn : p + ((-1) + q) = n) (a : (homObject A D x b.val).X p)
    (t : (term A D w b.val y).X q) :
    (ι A D S x y (b :: w)).f n
      (ιTensorObj (homObject A D x b.val) (epsilonComplex A ⊗ term A D w b.val y)
        p ((-1) + q) n hn (a ⊗ₜ[A]
          ιTensorObj (epsilonComplex A) (term A D w b.val y) (-1) q ((-1) + q) rfl
            ((singleObjXSelf (.up ℤ) (-1) (𝟙_ (ModuleCat.{u} A))).inv (1 : A) ⊗ₜ[A] t))) =
    forward A (x := (⟨x⟩ : QuotientObject D S)) (y := ⟨b.val⟩) (z := ⟨y⟩)
      ((originalHomInclusion A D S x b.val).f p a)
      (forward A (x := (⟨b.val⟩ : QuotientObject D S)) (y := ⟨b.val⟩) (z := ⟨y⟩)
        (epsilonElement A D S b) ((ι A D S b.val y w).f q t) rfl) hn := by
  have h := congrArg (fun f : homObject A D x b.val ⊗
      (epsilonComplex A ⊗ term A D w b.val y) ⟶ internalHom A D S x y =>
    f.f n (ιTensorObj (homObject A D x b.val) (epsilonComplex A ⊗ term A D w b.val y)
      p ((-1) + q) n hn (a ⊗ₜ[A]
        ιTensorObj (epsilonComplex A) (term A D w b.val y) (-1) q ((-1) + q) rfl
          ((singleObjXSelf (.up ℤ) (-1) (𝟙_ (ModuleCat.{u} A))).inv (1 : A) ⊗ₜ[A] t))))
    (prefixPath_ι A D b x y w)
  simp only [chain_comp_apply, whiskerLeft_apply] at h
  exact h.symm.trans (prefixPath_generator A D b x y p q n hn a ((ι A D S b.val y w).f q t))

end SerrePositivity.DifferentialGraded.DGQuotient
end

end PathGeneration

/-! ## ScalarExtension（旧 SerrePositivity/DifferentialGraded/Quotient/ScalarExtension.lean） -/

/-! # 明示的 dg 商の最終 Hom の係数変更

固定した有限語添字の同型が、内部微分と ε 消去の両方に可換する。
係数環の flatness は要求しない。
-/

@[expose] public section ScalarExtension
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits MonoidalCategory HomologicalComplex CochainComplex
open SerrePositivity.DifferentialGraded.ScalarExtension
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
variable (D : Type v) [DGCategory A D] [Small.{u} D]

/-- ε 消去を加えた最終微分に関する固定 path 係数変更同型。 -/
def quotientHomBaseChangeIso (S : Set D) (x y : D) :
    (extension φ).obj (quotientHom A D S x y) ≅
      quotientHom A' (DGBaseChange φ D) S x y :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (HomologicalComplex.eval (ModuleCat.{u} A') (.up ℤ) n).mapIso
      (internalHomBaseChangeIso φ D S x y)) (fun i j hij => by
      change i + 1 = j at hij
      subst j
      change (internalHomBaseChangeIso φ D S x y).hom.f i ≫
          (quotientHom A' (DGBaseChange φ D) S x y).d i (i + 1) =
        (ModuleCat.extendScalars φ).map ((quotientHom A D S x y).d i (i + 1)) ≫
          (internalHomBaseChangeIso φ D S x y).hom.f (i + 1)
      rw [quotientHom_d, quotientHom_d, Preadditive.comp_add,
        CategoryTheory.Functor.map_add, Preadditive.add_comp]
      exact congrArg₂ (· + ·) ((internalHomBaseChangeIso φ D S x y).hom.comm i (i + 1))
        (erasure_baseChange φ D S x y i (i + 1) rfl).symm)

lemma quotientHomBaseChangeIso_hom_f (S : Set D) (x y : D) (n : ℤ) :
    (quotientHomBaseChangeIso φ D S x y).hom.f n =
      (internalHomBaseChangeIso φ D S x y).hom.f n := rfl

@[reassoc]
lemma originalHomInclusion_baseChange (S : Set D) (x y : D) :
    (extension φ).map (originalHomInclusion A D S x y) ≫
        (quotientHomBaseChangeIso φ D S x y).hom =
      originalHomInclusion A' (DGBaseChange φ D) S x y := by
  apply HomologicalComplex.hom_ext
  intro n
  have h := congrArg (fun f => f.f n) (map_originalHom_internalHomBaseChangeIso φ D S x y)
  simp only [HomologicalComplex.comp_f] at h ⊢
  rw [quotientHomBaseChangeIso_hom_f, originalHomInclusion_f]
  convert h using 1 <;> rfl

lemma quotientIdentity_baseChange (S : Set D) (x : D) :
    (unitIso φ).inv ≫ (extension φ).map (quotientIdentity A D S x) ≫
        (quotientHomBaseChangeIso φ D S x x).hom =
      quotientIdentity A' (DGBaseChange φ D) S x := by
  simp only [quotientIdentity, CategoryTheory.Functor.map_comp, Category.assoc]
  rw [originalHomInclusion_baseChange]
  rfl

private lemma matrix_four {C : Type*} [Category* C]
    {V₀ V₁ V₂ V₃ V₄ W₁ W₂ W₃ : C}
    {a : V₀ ⟶ V₁} {b : V₁ ⟶ V₂} {c : V₂ ⟶ V₃} {d : V₃ ⟶ V₄}
    {p : V₀ ⟶ W₁} {q : W₁ ⟶ V₂} {r : W₁ ⟶ W₂}
    {s : W₂ ⟶ V₃} {t : W₂ ⟶ W₃} {u : W₃ ⟶ V₄}
    (h₁ : a ≫ b = p ≫ q) (h₂ : q ≫ c = r ≫ s) (h₃ : s ≫ d = t ≫ u) :
    a ≫ b ≫ c ≫ d = p ≫ r ≫ t ≫ u := by
  rw [← Category.assoc a b (c ≫ d), h₁]
  simp only [Category.assoc]
  rw [← Category.assoc q c d, h₂]
  simp only [Category.assoc]
  rw [h₃]

lemma quotientComposition_baseChange (S : Set D) (x y z : D) :
    (extension φ).map (quotientComposition A D S x y z) ≫
        (quotientHomBaseChangeIso φ D S x z).hom =
      compareTensor φ (quotientHomBaseChangeIso φ D S x y).hom
        (quotientHomBaseChangeIso φ D S y z).hom ≫
          quotientComposition A' (DGBaseChange φ D) S x y z := by
  apply HomologicalComplex.hom_ext
  intro n
  apply cochainTensorBaseChange_hom_ext φ (quotientHom A D S x y) (quotientHom A D S y z)
  intro i j hij
  let uq := (ModuleCat.extendScalars φ).map
    (ιTensorObj (quotientHom A D S x y) (quotientHom A D S y z) i j n hij)
  let ui := (ModuleCat.extendScalars φ).map
    (ιTensorObj (internalHom A D S x y) (internalHom A D S y z) i j n hij)
  let fq := (ModuleCat.extendScalars φ).map ((quotientComposition A D S x y z).f n)
  let fi := (ModuleCat.extendScalars φ).map ((internalComposition A D S x y z).f n)
  let eq := (quotientHomBaseChangeIso φ D S x z).hom.f n
  let ei := (internalHomBaseChangeIso φ D S x z).hom.f n
  let dq := (cochainTensorBaseChangeXIso φ (quotientHom A D S x y) (quotientHom A D S y z) n).hom
  let di := (cochainTensorBaseChangeXIso φ (internalHom A D S x y) (internalHom A D S y z) n).hom
  let tq := ((quotientHomBaseChangeIso φ D S x y).hom ⊗ₘ
    (quotientHomBaseChangeIso φ D S y z).hom).f n
  let ti := ((internalHomBaseChangeIso φ D S x y).hom ⊗ₘ
    (internalHomBaseChangeIso φ D S y z).hom).f n
  let cq := (quotientComposition A' (DGBaseChange φ D) S x y z).f n
  let ci := (internalComposition A' (DGBaseChange φ D) S x y z).f n
  let gq := ιTensorObj ((extension φ).obj (quotientHom A D S x y))
    ((extension φ).obj (quotientHom A D S y z)) i j n hij
  let gi := ιTensorObj ((extension φ).obj (internalHom A D S x y))
    ((extension φ).obj (internalHom A D S y z)) i j n hij
  let kq := ιTensorObj (quotientHom A' (DGBaseChange φ D) S x y)
    (quotientHom A' (DGBaseChange φ D) S y z) i j n hij
  let ki := ιTensorObj (internalHom A' (DGBaseChange φ D) S x y)
    (internalHom A' (DGBaseChange φ D) S y z) i j n hij
  let ds := CategoryTheory.Functor.OplaxMonoidal.δ (ModuleCat.extendScalars φ)
    ((internalHom A D S x y).X i) ((internalHom A D S y z).X j)
  let ts := (internalHomBaseChangeIso φ D S x y).hom.f i ⊗ₘ
    (internalHomBaseChangeIso φ D S y z).hom.f j
  have hs : uq ≫ fq = ui ≫ fi := by
    have h := congrArg (ModuleCat.extendScalars φ).map
      (quotientComposition_ι A D S x y z i j n hij)
    simpa only [CategoryTheory.Functor.map_comp] using h
  have he : eq = ei := quotientHomBaseChangeIso_hom_f φ D S x z n
  have hl : uq ≫ fq ≫ eq = ui ≫ fi ≫ ei := by
    rw [← Category.assoc, hs, Category.assoc, he]
  have hdq : uq ≫ dq = ds ≫ gq :=
    map_ι_cochainTensorBaseChangeXIso φ (quotientHom A D S x y) (quotientHom A D S y z) i j n hij
  have hdi : ui ≫ di = ds ≫ gi :=
    map_ι_cochainTensorBaseChangeXIso φ (internalHom A D S x y) (internalHom A D S y z) i j n hij
  have hmq : gq ≫ tq = ts ≫ kq := by
    have h := ιTensorObj_cochainTensorMap (quotientHomBaseChangeIso φ D S x y).hom
      (quotientHomBaseChangeIso φ D S y z).hom i j n hij
    have hc := congrArg₂ (fun f g => f ⊗ₘ g)
      (quotientHomBaseChangeIso_hom_f φ D S x y i)
      (quotientHomBaseChangeIso_hom_f φ D S y z j)
    exact h.trans (congrArg (fun f => f ≫ kq) hc)
  have hmi : gi ≫ ti = ts ≫ ki :=
    ιTensorObj_cochainTensorMap (internalHomBaseChangeIso φ D S x y).hom
      (internalHomBaseChangeIso φ D S y z).hom i j n hij
  have hq : kq ≫ cq = ki ≫ ci := quotientComposition_ι A' (DGBaseChange φ D) S x y z i j n hij
  have hrq : uq ≫ dq ≫ tq ≫ cq = ds ≫ ts ≫ ki ≫ ci := matrix_four hdq hmq hq
  have hri : ui ≫ di ≫ ti ≫ ci = ds ≫ ts ≫ ki ≫ ci := matrix_four hdi hmi rfl
  have hi : ui ≫ fi ≫ ei = ui ≫ di ≫ ti ≫ ci := by
    have h := congrArg (fun f => ui ≫ f.f n) (internalComposition_baseChange φ D S x y z)
    exact h
  change uq ≫ fq ≫ eq = uq ≫ dq ≫ tq ≫ cq
  exact hl.trans (hi.trans (hri.trans hrq.symm))

/-- 最終 Hom 上の同型を持つ、係数変更と明示的商を交換する実際の dg 関手。 -/
def quotientBaseChangeDGFunctor (S : Set D) :
    DGFunctor A' (DGBaseChange φ (QuotientObject D S))
      (QuotientObject (DGBaseChange φ D) S) where
  obj x := ⟨x.val⟩
  map x y := (quotientHomBaseChangeIso φ D S x.val y.val).hom
  map_id x := quotientIdentity_baseChange φ D S x.val
  map_comp x y z := by
    have h := congrArg (fun f => (tensorIso φ (quotientHom A D S x.val y.val)
      (quotientHom A D S y.val z.val)).inv ≫ f)
      (quotientComposition_baseChange φ D S x.val y.val z.val)
    simp only [compareTensor, Category.assoc, Iso.inv_hom_id_assoc] at h
    exact h

instance quotientBaseChangeDGFunctor_hom_isIso (S : Set D)
    (x y : DGBaseChange φ (QuotientObject D S)) :
    IsIso ((quotientBaseChangeDGFunctor φ D S).map x y) :=
  Iso.isIso_hom (quotientHomBaseChangeIso φ D S x.val y.val)

/-- 最終 Hom の比較も同じ有限語 w の包含成分を保つ。 -/
lemma quotientHomBaseChangeIso_path_component (S : Set D) (x y : D) (w : Word S) (n : ℤ) :
    (ModuleCat.extendScalars φ).map ((ι A D S x y w).f n) ≫
        (quotientHomBaseChangeIso φ D S x y).hom.f n =
      (termBaseChangeIso φ D w x y).hom.f n ≫ (ι A' (DGBaseChange φ D) S x y w).f n := by
  have h := congrArg (fun f => f.f n) (map_ι_internalHomBaseChangeIso φ D S x y w)
  convert h using 1 <;> rfl

lemma quotientBaseChangeDGFunctor_inclusion (S : Set D) :
    (dgFunctor φ (inclusion A D S)).comp (quotientBaseChangeDGFunctor φ D S) =
      inclusion A' (DGBaseChange φ D) S := by
  apply EnrichedFunctor.ext (Complex A')
    (F := (dgFunctor φ (inclusion A D S)).comp (quotientBaseChangeDGFunctor φ D S))
    (G := inclusion A' (DGBaseChange φ D) S) (fun _ => rfl)
  intro x y
  exact originalHomInclusion_baseChange φ D S x y

end SerrePositivity.DifferentialGraded.DGQuotient
end

end ScalarExtension

/-! ## EpsilonContraction（旧 SerrePositivity/DifferentialGraded/Quotient/EpsilonContraction.lean） -/

/-! # 指定ε生成元の収縮方程式 -/

@[expose] public section EpsilonContraction
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

lemma eraseFirst_epsilonTerm {S : Set D} (b : S) :
    (eraseFirst A D b [] b.val b.val).v (-1) 0 (by omega)
      ((epsilonTerm A D b).f (-1)
        ((singleObjXSelf (.up ℤ) (-1) (𝟙_ (ModuleCat.{u} A))).inv (1 : A))) =
    (unitElement A b.val).val := by
  change ((eraseMiddle A (homObject A D b.val b.val) (homObject A D b.val b.val)).comp
    (Cochain.ofHom (eComp (Complex A) b.val b.val b.val)) (add_zero 1)).v (-1) 0 (by omega)
      ((epsilonTerm A D b).f (-1)
        ((singleObjXSelf (.up ℤ) (-1) (𝟙_ (ModuleCat.{u} A))).inv (1 : A))) = _
  rw [epsilonTerm_generator, cochain_comp_ofHom_apply, eraseMiddle_generator]
  simp only [Int.negOnePow_zero, one_smul]
  exact forward_unit A (unitElement A b.val).val

variable [Small.{u} D]

lemma erasure_epsilonElement (S : Set D) (b : S) :
    (erasure A D S b.val b.val).v (-1) 0 (by omega) (epsilonElement A D S b) =
      (originalHom A D S b.val b.val).f 0 (unitElement A b.val).val := by
  have h := congrArg (fun f : Cochain (term A D [b] b.val b.val)
      (internalHom A D S b.val b.val) 1 =>
      f.v (-1) 0 (by omega) ((epsilonTerm A D b).f (-1)
        ((singleObjXSelf (.up ℤ) (-1) (𝟙_ (ModuleCat.{u} A))).inv (1 : A))))
    (erasure_precomp A D S b.val b.val [b])
  rw [eraseRow_singleton, cochain_ofHom_comp_apply, cochain_comp_ofHom_apply,
    eraseFirst_epsilonTerm] at h
  exact h

lemma internal_d_epsilonElement (S : Set D) (b : S) :
    (internalHom A D S b.val b.val).d (-1) 0 (epsilonElement A D S b) = 0 :=
  (complexSphereCycle A (-1) (epsilon A D S b)).property

/-- 最終dg商における指定収縮の方程式dε_b=id_b。 -/
lemma differential_epsilonElement (S : Set D) (b : S) :
    (quotientHom A D S b.val b.val).d (-1) 0 (epsilonElement A D S b) =
      (unitElement A (⟨b.val⟩ : QuotientObject D S)).val := by
  rw [show (quotientHom A D S b.val b.val).d (-1) 0 =
      (internalHom A D S b.val b.val).d (-1) 0 +
        (erasure A D S b.val b.val).v (-1) 0 (by omega) from
      quotientHom_d A D S b.val b.val (-1)]
  change (internalHom A D S b.val b.val).d (-1) 0 (epsilonElement A D S b) +
    (erasure A D S b.val b.val).v (-1) 0 (by omega) (epsilonElement A D S b) = _
  rw [internal_d_epsilonElement, zero_add, erasure_epsilonElement]
  rfl

end SerrePositivity.DifferentialGraded.DGQuotient
end

end EpsilonContraction

/-! ## ContractedFunctor（旧 SerrePositivity/DifferentialGraded/Quotient/ContractedFunctor.lean） -/

/-! # 指定収縮データを持つdg関手と商からの制限 -/

@[expose] public section ContractedFunctor
universe u v w t

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

/-- Sの各対象の像に、選択した次数−1の収縮元を持つdg関手。 -/
structure ContractedFunctor (S : Set D) (E : Type w) [DGCategory A E] where
  toDGFunctor : DGFunctor A D E
  homotopy : ∀ b : S, GradedHom A (toDGFunctor.obj b.val) (toDGFunctor.obj b.val) (-1)
  d_homotopy : ∀ b : S,
    (homObject A E (toDGFunctor.obj b.val) (toDGFunctor.obj b.val)).d (-1) 0 (homotopy b) =
      (unitElement A (toDGFunctor.obj b.val)).val

variable {D} {E : Type w} [DGCategory A E] {T : Type t} [DGCategory A T]

/-- 指定収縮データをdg関手で後合成する。 -/
def ContractedFunctor.postcomp {S : Set D} (C : ContractedFunctor A D S E)
    (G : DGFunctor A E T) : ContractedFunctor A D S T where
  toDGFunctor := C.toDGFunctor.comp G
  homotopy b := (G.map (C.toDGFunctor.obj b.val) (C.toDGFunctor.obj b.val)).f (-1) (C.homotopy b)
  d_homotopy b := G.map_contractingElement A (C.toDGFunctor.obj b.val)
    (C.homotopy b) (C.d_homotopy b)

variable (D) [Small.{u} D]

/-- 商の包含と指定εは、選択済み収縮データを持つ。 -/
def canonicalContractedFunctor (S : Set D) : ContractedFunctor A D S (QuotientObject D S) where
  toDGFunctor := inclusion A D S
  homotopy b := epsilonElement A D S b
  d_homotopy b := differential_epsilonElement A D S b

/-- 商からのdg関手を制限し、指定εの像を収縮として保持する。 -/
def restrictContractedFunctor (S : Set D) (G : DGFunctor A (QuotientObject D S) E) :
    ContractedFunctor A D S E := (canonicalContractedFunctor A D S).postcomp A G

lemma restrictContractedFunctor_homotopy (S : Set D)
    (G : DGFunctor A (QuotientObject D S) E) (b : S) :
    (restrictContractedFunctor A D S G).homotopy b =
      (G.map ⟨b.val⟩ ⟨b.val⟩).f (-1) (epsilonElement A D S b) := rfl

end SerrePositivity.DifferentialGraded.DGQuotient
end

end ContractedFunctor

/-! ## ContractionCochain（旧 SerrePositivity/DifferentialGraded/Quotient/ContractionCochain.lean） -/

/-! # 指定収縮元からεの評価cochainを構成する -/

@[expose] public section ContractionCochain
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]
  {S : Set D} {E : Type w} [DGCategory A E]

/-- εを指定収縮元へ送る次数0 cochain。閉零chain mapではない。 -/
def contractionCochain (C : ContractedFunctor A D S E) (b : S) :
    Cochain (epsilonComplex A)
      (homObject A E (C.toDGFunctor.obj b.val) (C.toDGFunctor.obj b.val)) 0 :=
  Cochain.fromSingleMk (p := -1) (q := -1)
    (moduleElementMap A _ (C.homotopy b)) (add_zero (-1))

lemma contractionCochain_generator (C : ContractedFunctor A D S E) (b : S) :
    (contractionCochain A C b).v (-1) (-1) (add_zero (-1))
      ((singleObjXSelf (.up ℤ) (-1) (𝟙_ (ModuleCat.{u} A))).inv (1 : A)) = C.homotopy b := by
  rw [contractionCochain, Cochain.fromSingleMk_v]
  change (moduleElementMap A _ (C.homotopy b))
    (((singleObjXSelf (.up ℤ) (-1) (𝟙_ (ModuleCat.{u} A))).inv ≫
      (singleObjXSelf (.up ℤ) (-1) (𝟙_ (ModuleCat.{u} A))).hom) (1 : A)) = _
  rw [Iso.inv_hom_id]
  exact one_smul A (C.homotopy b)

/-- 収縮cochainの微分は、εを消して像対象の単位を挿入するcochain。 -/
lemma contractionCochain_differential (C : ContractedFunctor A D S E) (b : S) :
    δ 0 1 (contractionCochain A C b) =
    (eraseEpsilon A).comp (Cochain.ofHom (eId (Complex A) (C.toDGFunctor.obj b.val)))
      (add_zero 1) := by
  rw [contractionCochain, Cochain.δ_fromSingleMk _ _ 1 0 (by omega), eraseEpsilon,
    ← Cochain.fromSingleMk_postcomp]
  congr 1
  apply (moduleElementEquiv A _).injective
  change (homObject A E (C.toDGFunctor.obj b.val) (C.toDGFunctor.obj b.val)).d (-1) 0
    ((1 : A) • C.homotopy b) = (unitElement A (C.toDGFunctor.obj b.val)).val
  rw [one_smul]
  exact C.d_homotopy b

end SerrePositivity.DifferentialGraded.DGQuotient
end

end ContractionCochain

/-! ## ContractionAction（旧 SerrePositivity/DifferentialGraded/Quotient/ContractionAction.lean） -/

/-! # 指定収縮のHomへの作用と、その微分のε消去表示 -/

@[expose] public section ContractionAction
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]
  {S : Set D} {E : Type w} [DGCategory A E]

/-- 像対象のHomへ、選択した収縮cochainを先頭から作用させる。 -/
def contractionAction (C : ContractedFunctor A D S E) (b : S) (y : E) :
    Cochain (epsilonComplex A ⊗ homObject A E (C.toDGFunctor.obj b.val) y)
      (homObject A E (C.toDGFunctor.obj b.val) y) 0 :=
  ((tensorRightHom (homObject A E (C.toDGFunctor.obj b.val) y) (epsilonComplex A)
    (homObject A E (C.toDGFunctor.obj b.val) (C.toDGFunctor.obj b.val))).f 0
      (contractionCochain A C b)).comp
    (Cochain.ofHom (eComp (Complex A) (C.toDGFunctor.obj b.val) (C.toDGFunctor.obj b.val) y))
      (zero_add 0)

lemma contractionAction_differential (C : ContractedFunctor A D S E) (b : S) (y : E) :
    δ 0 1 (contractionAction A C b y) =
      eraseHead A (homObject A E (C.toDGFunctor.obj b.val) y) := by
  have hu : (eId (Complex A) (C.toDGFunctor.obj b.val) ▷
      homObject A E (C.toDGFunctor.obj b.val) y) ≫
      eComp (Complex A) (C.toDGFunctor.obj b.val) (C.toDGFunctor.obj b.val) y =
    (λ_ (homObject A E (C.toDGFunctor.obj b.val) y)).hom := by
    apply (cancel_epi (λ_ (homObject A E (C.toDGFunctor.obj b.val) y)).inv).1
    rw [e_id_comp, Iso.inv_hom_id]
  rw [contractionAction, δ_comp_ofHom,
    homComplexMap_differential (tensorRightHom _ _ _) 0 1,
    contractionCochain_differential, tensorRightHom_cochain_comp, tensorRightHom_ofHom,
    Cochain.comp_assoc_of_third_is_zero_cochain, ← Cochain.ofHom_comp, hu]
  rfl

lemma contractionAction_evaluate (C : ContractedFunctor A D S E) (b : S) (y : E)
    (P : Complex A) (f : Cochain P (homObject A E (C.toDGFunctor.obj b.val) y) 0) :
    (tensorZeroCochain (contractionCochain A C b) f).comp
      (Cochain.ofHom (eComp (Complex A) (C.toDGFunctor.obj b.val) (C.toDGFunctor.obj b.val) y))
        (zero_add 0) =
    ((tensorLeftHom (epsilonComplex A) P (homObject A E (C.toDGFunctor.obj b.val) y)).f 0 f).comp
      (contractionAction A C b y) (zero_add 0) := by
  have h := tensorCochain_interchange (epsilonComplex A)
    (homObject A E (C.toDGFunctor.obj b.val) (C.toDGFunctor.obj b.val))
    P (homObject A E (C.toDGFunctor.obj b.val) y) 0 0 0 (zero_add 0) (zero_add 0)
    (contractionCochain A C b) f
  simp only [mul_zero, Int.negOnePow_zero, one_smul] at h
  rw [tensorZeroCochain, h, Cochain.comp_assoc_of_third_is_zero_cochain]
  rfl

lemma contractionAction_evaluation_differential (C : ContractedFunctor A D S E) (b : S) (y : E)
    (P : Complex A) (f : Cochain P (homObject A E (C.toDGFunctor.obj b.val) y) 0) :
    δ 0 1 ((tensorZeroCochain (contractionCochain A C b) f).comp
      (Cochain.ofHom (eComp (Complex A) (C.toDGFunctor.obj b.val) (C.toDGFunctor.obj b.val) y))
        (zero_add 0)) =
    (eraseHead A P).comp f (add_zero 1) +
    ((tensorLeftHom (epsilonComplex A) P (homObject A E (C.toDGFunctor.obj b.val) y)).f 1
      (δ 0 1 f)).comp (contractionAction A C b y) (add_zero 1) := by
  rw [contractionAction_evaluate,
    δ_comp _ _ (zero_add 0) 1 1 1 (zero_add 1) (zero_add 1) (zero_add 1),
    contractionAction_differential,
    homComplexMap_differential (tensorLeftHom _ _ _) 0 1,
    eraseHead_cochain_zero]
  simp only [Int.negOnePow_zero, one_smul]

end SerrePositivity.DifferentialGraded.DGQuotient
end

end ContractionAction

/-! ## PathEvaluation（旧 SerrePositivity/DifferentialGraded/Quotient/PathEvaluation.lean） -/

/-! # 指定収縮付きdg関手による有限pathの評価 -/

@[expose] public section PathEvaluation
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]
  {S : Set D} {E : Type w} [DGCategory A E]

/-- 各HomをFで写し、各εを選択した収縮元へ送って豊穣合成する次数0 cochain。 -/
def pathEvaluation (C : ContractedFunctor A D S E) : ∀ (w : Word S) (x y : D),
    Cochain (term A D w x y) (homObject A E (C.toDGFunctor.obj x) (C.toDGFunctor.obj y)) 0
  | [], x, y => Cochain.ofHom (C.toDGFunctor.map x y)
  | b :: w, x, y =>
    (tensorZeroCochain (Cochain.ofHom (C.toDGFunctor.map x b.val))
      ((tensorZeroCochain (contractionCochain A C b) (pathEvaluation C w b.val y)).comp
        (Cochain.ofHom (eComp (Complex A) (C.toDGFunctor.obj b.val)
          (C.toDGFunctor.obj b.val) (C.toDGFunctor.obj y))) (zero_add 0))).comp
      (Cochain.ofHom (eComp (Complex A) (C.toDGFunctor.obj x)
        (C.toDGFunctor.obj b.val) (C.toDGFunctor.obj y))) (zero_add 0)

@[simp] lemma pathEvaluation_nil (C : ContractedFunctor A D S E) (x y : D) :
    pathEvaluation A C [] x y = Cochain.ofHom (C.toDGFunctor.map x y) := rfl

/-- 前方Hom・標準ε・後方pathの純tensor評価。追加符号は生じない。 -/
lemma pathEvaluation_cons_generator (C : ContractedFunctor A D S E) (b : S) (w : Word S)
    (x y : D) (p q n : ℤ) (hn : p + ((-1) + q) = n)
    (f : (homObject A D x b.val).X p) (t : (term A D w b.val y).X q) :
    (pathEvaluation A C (b :: w) x y).v n n (add_zero n)
      (ιTensorObj (homObject A D x b.val) (epsilonComplex A ⊗ term A D w b.val y)
        p ((-1) + q) n hn
        (f ⊗ₜ[A] ιTensorObj (epsilonComplex A) (term A D w b.val y) (-1) q ((-1) + q) rfl
          ((singleObjXSelf (.up ℤ) (-1) (𝟙_ (ModuleCat.{u} A))).inv (1 : A) ⊗ₜ[A] t))) =
    forward A ((C.toDGFunctor.map x b.val).f p f)
      (forward A (C.homotopy b) ((pathEvaluation A C w b.val y).v q q (add_zero q) t) rfl) hn := by
  change ((tensorZeroCochain (Cochain.ofHom (C.toDGFunctor.map x b.val))
      ((tensorZeroCochain (contractionCochain A C b) (pathEvaluation A C w b.val y)).comp
        (Cochain.ofHom (eComp (Complex A) (C.toDGFunctor.obj b.val)
          (C.toDGFunctor.obj b.val) (C.toDGFunctor.obj y))) (zero_add 0))).comp
      (Cochain.ofHom (eComp (Complex A) (C.toDGFunctor.obj x)
        (C.toDGFunctor.obj b.val) (C.toDGFunctor.obj y))) (zero_add 0)).v n n (add_zero n)
      (ιTensorObj (homObject A D x b.val) (epsilonComplex A ⊗ term A D w b.val y)
        p ((-1) + q) n hn
        (f ⊗ₜ[A] ιTensorObj (epsilonComplex A) (term A D w b.val y) (-1) q ((-1) + q) rfl
          ((singleObjXSelf (.up ℤ) (-1) (𝟙_ (ModuleCat.{u} A))).inv (1 : A) ⊗ₜ[A] t))) = _
  rw [cochain_comp_ofHom_apply, tensorZeroCochain_apply,
    cochain_comp_ofHom_apply, tensorZeroCochain_apply, contractionCochain_generator]
  rfl

/-- 両側の単位を持つ単一ε pathは、選択した収縮元そのものへ評価される。 -/
lemma pathEvaluation_epsilonTerm (C : ContractedFunctor A D S E) (b : S) :
    (pathEvaluation A C [b] b.val b.val).v (-1) (-1) (add_zero (-1))
      ((epsilonTerm A D b).f (-1)
        ((singleObjXSelf (.up ℤ) (-1) (𝟙_ (ModuleCat.{u} A))).inv (1 : A))) = C.homotopy b := by
  have he := congrArg (fun v : (term A D [b] b.val b.val).X (-1) =>
    (pathEvaluation A C [b] b.val b.val).v (-1) (-1) (add_zero (-1)) v)
    (epsilonTerm_generator A D b)
  have h := pathEvaluation_cons_generator A C b [] b.val b.val 0 0 (-1) (by omega)
    (unitElement A b.val).val (unitElement A b.val).val
  simp only [term_nil, pathEvaluation_nil, Cochain.ofHom_v, DGFunctor.map_unitElement,
    unit_forward, forward_unit] at h
  exact he.trans h

end SerrePositivity.DifferentialGraded.DGQuotient
end

end PathEvaluation

/-! ## PathEvaluationPrepend（旧 SerrePositivity/DifferentialGraded/Quotient/PathEvaluationPrepend.lean） -/

/-! # 元のHomを先頭合成する操作と有限path評価の整合性 -/

@[expose] public section PathEvaluationPrepend
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]
  {S : Set D} {E : Type w} [DGCategory A E]

lemma pathEvaluation_prepend (C : ContractedFunctor A D S E) (w : Word S) (x y z : D) :
    (Cochain.ofHom (prependMap A D w x y z)).comp (pathEvaluation A C w x z) (zero_add 0) =
    (tensorZeroCochain (Cochain.ofHom (C.toDGFunctor.map x y)) (pathEvaluation A C w y z)).comp
      (Cochain.ofHom (eComp (Complex A) (C.toDGFunctor.obj x)
        (C.toDGFunctor.obj y) (C.toDGFunctor.obj z))) (zero_add 0) := by
  cases w with
  | nil =>
    simpa only [pathEvaluation_nil, prependMap_nil, tensorZeroCochain_ofHom,
      ← Cochain.ofHom_comp] using
      congrArg (fun f => Cochain.ofHom f) (C.toDGFunctor.map_comp x y z)
  | cons b w =>
    have h := tensorJoin_evaluation
      (homObject A D x y) (homObject A D y b.val) (homObject A D x b.val)
      (homObject A E (C.toDGFunctor.obj x) (C.toDGFunctor.obj y))
      (homObject A E (C.toDGFunctor.obj y) (C.toDGFunctor.obj b.val))
      (homObject A E (C.toDGFunctor.obj x) (C.toDGFunctor.obj b.val))
      (epsilonComplex A ⊗ term A D w b.val z)
      (homObject A E (C.toDGFunctor.obj b.val) (C.toDGFunctor.obj z))
      (homObject A E (C.toDGFunctor.obj y) (C.toDGFunctor.obj z))
      (homObject A E (C.toDGFunctor.obj x) (C.toDGFunctor.obj z))
      (C.toDGFunctor.map x y) (C.toDGFunctor.map y b.val) (C.toDGFunctor.map x b.val)
      (eComp (Complex A) x y b.val)
      (eComp (Complex A) (C.toDGFunctor.obj x) (C.toDGFunctor.obj y) (C.toDGFunctor.obj b.val))
      (eComp (Complex A) (C.toDGFunctor.obj x) (C.toDGFunctor.obj b.val) (C.toDGFunctor.obj z))
      (eComp (Complex A) (C.toDGFunctor.obj y) (C.toDGFunctor.obj b.val) (C.toDGFunctor.obj z))
      (eComp (Complex A) (C.toDGFunctor.obj x) (C.toDGFunctor.obj y) (C.toDGFunctor.obj z))
      (C.toDGFunctor.map_comp x y b.val)
      (e_assoc' (Complex A) (C.toDGFunctor.obj x) (C.toDGFunctor.obj y)
        (C.toDGFunctor.obj b.val) (C.toDGFunctor.obj z)).symm
      ((tensorZeroCochain (contractionCochain A C b) (pathEvaluation A C w b.val z)).comp
        (Cochain.ofHom (eComp (Complex A) (C.toDGFunctor.obj b.val)
          (C.toDGFunctor.obj b.val) (C.toDGFunctor.obj z))) (zero_add 0))
    simpa only [pathEvaluation, prependMap, tensorHom_id] using h

end SerrePositivity.DifferentialGraded.DGQuotient
end

end PathEvaluationPrepend

/-! ## PathEvaluationAppend（旧 SerrePositivity/DifferentialGraded/Quotient/PathEvaluationAppend.lean） -/

/-! # 指定収縮による評価は任意二pathの連結を保つ -/

@[expose] public section PathEvaluationAppend
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]
  {S : Set D} {E : Type w} [DGCategory A E]

lemma pathEvaluation_append (C : ContractedFunctor A D S E) (w v : Word S) (x y z : D) :
    (Cochain.ofHom (appendMap A D w v x y z)).comp
      (pathEvaluation A C (w ++ v) x z) (zero_add 0) =
    (tensorZeroCochain (pathEvaluation A C w x y) (pathEvaluation A C v y z)).comp
      (Cochain.ofHom (eComp (Complex A) (C.toDGFunctor.obj x)
        (C.toDGFunctor.obj y) (C.toDGFunctor.obj z))) (zero_add 0) := by
  induction w generalizing x with
  | nil => simpa only [appendMap_nil_left, List.nil_append, pathEvaluation_nil] using
      pathEvaluation_prepend A C v x y z
  | cons b w ih =>
    have hinner := tensorCarry_evaluation (contractionCochain A C b)
      (pathEvaluation A C w b.val y) (pathEvaluation A C v y z)
      (pathEvaluation A C (w ++ v) b.val z)
      (appendMap A D w v b.val y z)
      (eComp (Complex A) (C.toDGFunctor.obj b.val) (C.toDGFunctor.obj y) (C.toDGFunctor.obj z))
      (eComp (Complex A) (C.toDGFunctor.obj b.val) (C.toDGFunctor.obj b.val) (C.toDGFunctor.obj y))
      (eComp (Complex A) (C.toDGFunctor.obj b.val) (C.toDGFunctor.obj b.val) (C.toDGFunctor.obj z))
      (eComp (Complex A) (C.toDGFunctor.obj b.val) (C.toDGFunctor.obj y) (C.toDGFunctor.obj z))
      (ih b.val)
      (e_assoc' (Complex A) (C.toDGFunctor.obj b.val) (C.toDGFunctor.obj b.val)
        (C.toDGFunctor.obj y) (C.toDGFunctor.obj z)).symm
    have h := tensorCarry_evaluation (Cochain.ofHom (C.toDGFunctor.map x b.val))
      ((tensorZeroCochain (contractionCochain A C b) (pathEvaluation A C w b.val y)).comp
        (Cochain.ofHom (eComp (Complex A) (C.toDGFunctor.obj b.val)
          (C.toDGFunctor.obj b.val) (C.toDGFunctor.obj y))) (zero_add 0))
      (pathEvaluation A C v y z)
      ((tensorZeroCochain (contractionCochain A C b) (pathEvaluation A C (w ++ v) b.val z)).comp
        (Cochain.ofHom (eComp (Complex A) (C.toDGFunctor.obj b.val)
          (C.toDGFunctor.obj b.val) (C.toDGFunctor.obj z))) (zero_add 0))
      ((α_ (epsilonComplex A) (term A D w b.val y) (term A D v y z)).hom ≫
        (epsilonComplex A) ◁ appendMap A D w v b.val y z)
      (eComp (Complex A) (C.toDGFunctor.obj b.val) (C.toDGFunctor.obj y) (C.toDGFunctor.obj z))
      (eComp (Complex A) (C.toDGFunctor.obj x) (C.toDGFunctor.obj b.val) (C.toDGFunctor.obj y))
      (eComp (Complex A) (C.toDGFunctor.obj x) (C.toDGFunctor.obj b.val) (C.toDGFunctor.obj z))
      (eComp (Complex A) (C.toDGFunctor.obj x) (C.toDGFunctor.obj y) (C.toDGFunctor.obj z))
      hinner
      (e_assoc' (Complex A) (C.toDGFunctor.obj x) (C.toDGFunctor.obj b.val)
        (C.toDGFunctor.obj y) (C.toDGFunctor.obj z)).symm
    simpa only [pathEvaluation, appendMap, List.cons_append] using h

end SerrePositivity.DifferentialGraded.DGQuotient
end

end PathEvaluationAppend

/-! ## EvaluationPrefix（旧 SerrePositivity/DifferentialGraded/Quotient/EvaluationPrefix.lean） -/

/-! # 固定前方Homとεによる評価作用・非空pathの微分入力 -/

@[expose] public section EvaluationPrefix
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]
  {S : Set D} {E : Type w} [DGCategory A E]

/-- 前方の元のHomをFで送り、既に評価された後方Homと合成するchain map。 -/
def evaluationOriginalAction (C : ContractedFunctor A D S E) (b : S) (x y : D) :
    homObject A D x b.val ⊗ homObject A E (C.toDGFunctor.obj b.val) (C.toDGFunctor.obj y) ⟶
      homObject A E (C.toDGFunctor.obj x) (C.toDGFunctor.obj y) :=
  (C.toDGFunctor.map x b.val ▷ homObject A E (C.toDGFunctor.obj b.val) (C.toDGFunctor.obj y)) ≫
    eComp (Complex A) (C.toDGFunctor.obj x) (C.toDGFunctor.obj b.val) (C.toDGFunctor.obj y)

/-- 前方Homと指定εを評価する固定の次数0 cochain。 -/
def evaluationPrefixAction (C : ContractedFunctor A D S E) (b : S) (x y : D) :
    Cochain (homObject A D x b.val ⊗
      (epsilonComplex A ⊗ homObject A E (C.toDGFunctor.obj b.val) (C.toDGFunctor.obj y)))
      (homObject A E (C.toDGFunctor.obj x) (C.toDGFunctor.obj y)) 0 :=
  ((tensorLeftHom (homObject A D x b.val)
    (epsilonComplex A ⊗ homObject A E (C.toDGFunctor.obj b.val) (C.toDGFunctor.obj y))
    (homObject A E (C.toDGFunctor.obj b.val) (C.toDGFunctor.obj y))).f 0
      (contractionAction A C b (C.toDGFunctor.obj y))).comp
    (Cochain.ofHom (evaluationOriginalAction A C b x y)) (zero_add 0)

lemma evaluationPrefixAction_differential (C : ContractedFunctor A D S E) (b : S) (x y : D) :
    δ 0 1 (evaluationPrefixAction A C b x y) =
    (eraseMiddle A (homObject A D x b.val)
      (homObject A E (C.toDGFunctor.obj b.val) (C.toDGFunctor.obj y))).comp
      (Cochain.ofHom (evaluationOriginalAction A C b x y)) (add_zero 1) := by
  rw [evaluationPrefixAction, δ_comp_ofHom,
    homComplexMap_differential (tensorLeftHom _ _ _) 0 1, contractionAction_differential,
    eraseMiddle_eq_tensorLeft]

lemma pathEvaluation_cons_action (C : ContractedFunctor A D S E) (b : S) (w : Word S) (x y : D) :
    pathEvaluation A C (b :: w) x y =
    ((tensorLeftHom (homObject A D x b.val)
      (epsilonComplex A ⊗ term A D w b.val y)
      (epsilonComplex A ⊗ homObject A E (C.toDGFunctor.obj b.val) (C.toDGFunctor.obj y))).f 0
      ((tensorLeftHom (epsilonComplex A) (term A D w b.val y)
        (homObject A E (C.toDGFunctor.obj b.val) (C.toDGFunctor.obj y))).f 0
          (pathEvaluation A C w b.val y))).comp
      (evaluationPrefixAction A C b x y) (zero_add 0) := by
  change (tensorZeroCochain (Cochain.ofHom (C.toDGFunctor.map x b.val))
      ((tensorZeroCochain (contractionCochain A C b) (pathEvaluation A C w b.val y)).comp
        (Cochain.ofHom (eComp (Complex A) (C.toDGFunctor.obj b.val)
          (C.toDGFunctor.obj b.val) (C.toDGFunctor.obj y))) (zero_add 0))).comp
      (Cochain.ofHom (eComp (Complex A) (C.toDGFunctor.obj x)
        (C.toDGFunctor.obj b.val) (C.toDGFunctor.obj y))) (zero_add 0) = _
  rw [contractionAction_evaluate, tensorZeroCochain_ofHom_left, tensorLeftHom_cochain_comp]
  simp only [Cochain.comp_assoc_of_third_is_zero_cochain, ← Cochain.ofHom_comp]
  rfl

lemma evaluationPrefixAction_evaluation_differential (C : ContractedFunctor A D S E)
    (b : S) (x y : D) (P : Complex A)
    (f : Cochain P (homObject A E (C.toDGFunctor.obj b.val) (C.toDGFunctor.obj y)) 0) :
    δ 0 1 (((tensorLeftHom (homObject A D x b.val) (epsilonComplex A ⊗ P)
      (epsilonComplex A ⊗ homObject A E (C.toDGFunctor.obj b.val) (C.toDGFunctor.obj y))).f 0
      ((tensorLeftHom (epsilonComplex A) P
        (homObject A E (C.toDGFunctor.obj b.val) (C.toDGFunctor.obj y))).f 0 f)).comp
      (evaluationPrefixAction A C b x y) (zero_add 0)) =
    (eraseMiddle A (homObject A D x b.val) P).comp
      ((tensorZeroCochain (Cochain.ofHom (C.toDGFunctor.map x b.val)) f).comp
        (Cochain.ofHom (eComp (Complex A) (C.toDGFunctor.obj x)
          (C.toDGFunctor.obj b.val) (C.toDGFunctor.obj y))) (zero_add 0)) (add_zero 1) +
    ((tensorLeftHom (homObject A D x b.val) (epsilonComplex A ⊗ P)
      (epsilonComplex A ⊗ homObject A E (C.toDGFunctor.obj b.val) (C.toDGFunctor.obj y))).f 1
      ((tensorLeftHom (epsilonComplex A) P
        (homObject A E (C.toDGFunctor.obj b.val) (C.toDGFunctor.obj y))).f 1 (δ 0 1 f))).comp
      (evaluationPrefixAction A C b x y) (add_zero 1) := by
  rw [δ_comp _ _ (zero_add 0) 1 1 1 (zero_add 1) (zero_add 1) (zero_add 1),
    evaluationPrefixAction_differential,
    homComplexMap_differential (tensorLeftHom _ _ _) 0 1,
    homComplexMap_differential (tensorLeftHom _ _ _) 0 1]
  simp only [Int.negOnePow_zero, one_smul]
  rw [← Cochain.comp_assoc_of_third_is_zero_cochain, eraseMiddle_cochain_zero,
    Cochain.comp_assoc_of_third_is_zero_cochain, tensorZeroCochain_ofHom_left,
    Cochain.comp_assoc_of_third_is_zero_cochain, ← Cochain.ofHom_comp]
  rfl

end SerrePositivity.DifferentialGraded.DGQuotient
end

end EvaluationPrefix

/-! ## InternalEvaluation（旧 SerrePositivity/DifferentialGraded/Quotient/InternalEvaluation.lean） -/

/-! # 指定収縮付きdg関手による全path直和の評価cochain -/

@[expose] public section InternalEvaluation
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D] [Small.{u} D]
  {S : Set D} {E : Type w} [DGCategory A E]

/-- 各有限pathの評価を貼り合わせた次数0 cochain。微分との整合性は別に証明する。 -/
def internalEvaluation (C : ContractedFunctor A D S E) (x y : D) :
    Cochain (internalHom A D S x y)
      (homObject A E (C.toDGFunctor.obj x) (C.toDGFunctor.obj y)) 0 :=
  pathCochainDesc A D S x y _ 0 (fun w => pathEvaluation A C w x y)

lemma internalEvaluation_precomp (C : ContractedFunctor A D S E) (x y : D) (w : Word S) :
    (Cochain.ofHom (ι A D S x y w)).comp (internalEvaluation A C x y) (zero_add 0) =
      pathEvaluation A C w x y := pathCochainDesc_precomp A D S x y _ 0 _ w

lemma internalEvaluation_original (C : ContractedFunctor A D S E) (x y : D) :
    (Cochain.ofHom (originalHom A D S x y)).comp (internalEvaluation A C x y) (zero_add 0) =
      Cochain.ofHom (C.toDGFunctor.map x y) := internalEvaluation_precomp A C x y []

lemma internalEvaluation_epsilon (C : ContractedFunctor A D S E) (b : S) :
    (Cochain.ofHom (epsilon A D S b)).comp (internalEvaluation A C b.val b.val) (zero_add 0) =
      contractionCochain A C b := by
  rw [epsilon, Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain,
    internalEvaluation_precomp]
  apply (Cochain.fromSingleEquiv (add_zero (-1))).injective
  apply (moduleElementEquiv A _).injective
  change ((Cochain.ofHom (epsilonTerm A D b)).comp (pathEvaluation A C [b] b.val b.val)
      (zero_add 0)).v (-1) (-1) (add_zero (-1))
      ((singleObjXSelf (.up ℤ) (-1) (𝟙_ (ModuleCat.{u} A))).inv (1 : A)) =
    (contractionCochain A C b).v (-1) (-1) (add_zero (-1))
      ((singleObjXSelf (.up ℤ) (-1) (𝟙_ (ModuleCat.{u} A))).inv (1 : A))
  rw [cochain_ofHom_comp_apply, pathEvaluation_epsilonTerm, contractionCochain_generator]

end SerrePositivity.DifferentialGraded.DGQuotient
end

end InternalEvaluation

/-! ## InternalEvaluationPrefix（旧 SerrePositivity/DifferentialGraded/Quotient/InternalEvaluationPrefix.lean） -/

/-! # 全path直和への前方Hom・ε追加と評価の整合性 -/

@[expose] public section InternalEvaluationPrefix
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D] [Small.{u} D]
  {S : Set D} {E : Type w} [DGCategory A E]

lemma internalEvaluation_prefixPath (C : ContractedFunctor A D S E) (b : S) (x y : D) :
    (Cochain.ofHom (prefixPath A D b x y)).comp (internalEvaluation A C x y) (zero_add 0) =
    ((tensorLeftHom (homObject A D x b.val)
      (epsilonComplex A ⊗ internalHom A D S b.val y)
      (epsilonComplex A ⊗ homObject A E (C.toDGFunctor.obj b.val) (C.toDGFunctor.obj y))).f 0
      ((tensorLeftHom (epsilonComplex A) (internalHom A D S b.val y)
        (homObject A E (C.toDGFunctor.obj b.val) (C.toDGFunctor.obj y))).f 0
          (internalEvaluation A C b.val y))).comp
      (evaluationPrefixAction A C b x y) (zero_add 0) := by
  apply prefixPathCochain_ext A D b x y 0
  intro w
  have ht :
      (Cochain.ofHom ((homObject A D x b.val) ◁ ((epsilonComplex A) ◁ ι A D S b.val y w))).comp
        ((tensorLeftHom (homObject A D x b.val)
          (epsilonComplex A ⊗ internalHom A D S b.val y)
          (epsilonComplex A ⊗ homObject A E (C.toDGFunctor.obj b.val) (C.toDGFunctor.obj y))).f 0
          ((tensorLeftHom (epsilonComplex A) (internalHom A D S b.val y)
            (homObject A E (C.toDGFunctor.obj b.val) (C.toDGFunctor.obj y))).f 0
              (internalEvaluation A C b.val y))) (zero_add 0) =
      (tensorLeftHom (homObject A D x b.val) (epsilonComplex A ⊗ term A D w b.val y)
        (epsilonComplex A ⊗ homObject A E (C.toDGFunctor.obj b.val) (C.toDGFunctor.obj y))).f 0
        ((tensorLeftHom (epsilonComplex A) (term A D w b.val y)
          (homObject A E (C.toDGFunctor.obj b.val) (C.toDGFunctor.obj y))).f 0
            (pathEvaluation A C w b.val y)) := by
    rw [← tensorLeftHom_ofHom (homObject A D x b.val), ← tensorLeftHom_cochain_comp,
      ← tensorLeftHom_ofHom (epsilonComplex A), ← tensorLeftHom_cochain_comp,
      internalEvaluation_precomp]
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp,
    prefixPath_ι, internalEvaluation_precomp,
    ← Cochain.comp_assoc_of_first_is_zero_cochain, ht]
  exact pathEvaluation_cons_action A C b w x y

end SerrePositivity.DifferentialGraded.DGQuotient
end

end InternalEvaluationPrefix

/-! ## InternalEvaluationPrepend（旧 SerrePositivity/DifferentialGraded/Quotient/InternalEvaluationPrepend.lean） -/

/-! # 全path評価と元のHomによる先頭作用の整合性 -/

@[expose] public section InternalEvaluationPrepend
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D] [Small.{u} D]
  {S : Set D} {E : Type w} [DGCategory A E]

lemma internalEvaluation_prepend (C : ContractedFunctor A D S E) (x y z : D) :
    (Cochain.ofHom (internalPrepend A D S x y z)).comp (internalEvaluation A C x z) (zero_add 0) =
    (tensorZeroCochain (Cochain.ofHom (C.toDGFunctor.map x y)) (internalEvaluation A C y z)).comp
      (Cochain.ofHom (eComp (Complex A) (C.toDGFunctor.obj x)
        (C.toDGFunctor.obj y) (C.toDGFunctor.obj z))) (zero_add 0) := by
  apply tensorLeftPathCochain_ext A D S y z (homObject A D x y) 0
  intro w
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp,
    internalPrepend_ι, Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain,
    internalEvaluation_precomp]
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain, tensorZeroCochain_precomp_right,
    internalEvaluation_precomp]
  exact pathEvaluation_prepend A C w x y z

end SerrePositivity.DifferentialGraded.DGQuotient
end

end InternalEvaluationPrepend

/-! ## InternalEvaluationComposition（旧 SerrePositivity/DifferentialGraded/Quotient/InternalEvaluationComposition.lean） -/

/-! # 全path直和の評価は内部合成を保つ -/

@[expose] public section InternalEvaluationComposition
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D] [Small.{u} D]
  {S : Set D} {E : Type w} [DGCategory A E]

lemma internalEvaluation_composition (C : ContractedFunctor A D S E) (x y z : D) :
    (Cochain.ofHom (internalComposition A D S x y z)).comp (internalEvaluation A C x z)
      (zero_add 0) =
    (tensorZeroCochain (internalEvaluation A C x y) (internalEvaluation A C y z)).comp
      (Cochain.ofHom (eComp (Complex A) (C.toDGFunctor.obj x)
        (C.toDGFunctor.obj y) (C.toDGFunctor.obj z))) (zero_add 0) := by
  apply tensorTwoPathCochain_ext A D S x y z 0
  intro w v
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp,
    internalComposition_ι, Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain,
    internalEvaluation_precomp,
    ← Cochain.comp_assoc_of_first_is_zero_cochain, tensorZeroCochain_precomp,
    internalEvaluation_precomp, internalEvaluation_precomp]
  exact pathEvaluation_append A C w v x y z

end SerrePositivity.DifferentialGraded.DGQuotient
end

end InternalEvaluationComposition

/-! ## HomogeneousNaturality（旧 SerrePositivity/DifferentialGraded/Quotient/HomogeneousNaturality.lean） -/

/-!
概要：実 Drinfeld 商の全次数自然性は元 Hom と指定 ε で判定できる。
方針：同じ有限 path の生成式と任意次数 cochain の判定を使う。
規約：ε に関する自然性を落とさず、元 Hom の自然性だけから延長しない。
使われ方：D-8 e の同じ収縮・商の全パラメータ作用。
-/

@[expose] public section HomogeneousNaturality
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  (S : Set D) {E : Type w} [DGCategory R E]

lemma homogeneousNaturality_of_generators
    (F G : DGFunctor R (QuotientObject D S) E) {k : ℤ}
    (a : ∀ x, GradedHom R (F.obj x) (G.obj x) k)
    (ho : ∀ (x y : D) (p : ℤ) (f : GradedHom R x y p),
      homogeneousNaturalityAt R F G a (x := ⟨x⟩) (y := ⟨y⟩)
        ((originalHomInclusion R D S x y).f p f))
    (he : ∀ b : S, homogeneousNaturalityAt R F G a
      (x := ⟨b.val⟩) (y := ⟨b.val⟩) (p := -1) (epsilonElement R D S b)) :
    ∀ (x y : QuotientObject D S) (p : ℤ) (f : GradedHom R x y p),
      homogeneousNaturalityAt R F G a f := by
  let L (x y : D) := homogeneousNaturalityLeftCochain R F G a ⟨x⟩ ⟨y⟩
  let T (x y : D) := homogeneousNaturalityRightCochain R F G a ⟨x⟩ ⟨y⟩
  have hw (w : Word S) (x y : D) :
      (Cochain.ofHom (ι R D S x y w)).comp (L x y) (zero_add k) =
        (Cochain.ofHom (ι R D S x y w)).comp (T x y) (zero_add k) := by
    induction w generalizing x y with
    | nil =>
      apply Cochain.ext
      intro p n hpn
      subst n
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro f
      simp only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v]
      exact ho x y p f
    | cons b w ih =>
      apply epsilonMiddleCochain_ext R
      intro p q n m hn hm f t
      subst m
      subst n
      simp only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v]
      change homogeneousNaturalityAt R F G a ((ι R D S x y (b :: w)).f (p + (-1 + q))
        (ιTensorObj (homObject R D x b.val) (epsilonComplex R ⊗ term R D w b.val y)
          p (-1 + q) (p + (-1 + q)) rfl
          (f ⊗ₜ[R] ιTensorObj (epsilonComplex R) (term R D w b.val y)
            (-1) q (-1 + q) rfl
            ((singleObjXSelf (.up ℤ) (-1) (𝟙_ (ModuleCat.{u} R))).inv (1 : R) ⊗ₜ[R] t))))
      rw [path_inclusion_generator]
      have ht := congrArg (fun z => z t) (Cochain.congr_v (ih b.val y) q (q + k) rfl)
      simp only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v] at ht
      have htail : homogeneousNaturalityAt R F G a
          (x := ⟨b.val⟩) (y := ⟨y⟩) (p := q) ((ι R D S b.val y w).f q t) := ht
      exact homogeneousNaturalityAt_forward R F G a _ _ (ho x b.val p f)
        (homogeneousNaturalityAt_forward R F G a _ _ (he b) htail)
  intro x y p f
  rcases x with ⟨x⟩
  rcases y with ⟨y⟩
  have h : L x y = T x y := pathCochain_ext R D S x y k (L x y) (T x y) (fun w => hw w x y)
  exact (homogeneousNaturalityAt_iff_cochain R F G a ⟨x⟩ ⟨y⟩).2 h p f

end SerrePositivity.DifferentialGraded.DGQuotient
end

end HomogeneousNaturality

/-! ## PathEvaluationDifferential（旧 SerrePositivity/DifferentialGraded/Quotient/PathEvaluationDifferential.lean） -/

/-! # 非空path評価の微分を先頭消去と後方微分へ分ける -/

@[expose] public section PathEvaluationDifferential
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]
  {S : Set D} {E : Type w} [DGCategory A E]

/-- 前方評価を保持して後方の任意次数cochainを合成する。 -/
def pathEvaluationTail (C : ContractedFunctor A D S E) (b : S) (w : Word S)
    (x y : D) (p : ℤ)
    (f : Cochain (term A D w b.val y)
      (homObject A E (C.toDGFunctor.obj b.val) (C.toDGFunctor.obj y)) p) :
    Cochain (term A D (b :: w) x y)
      (homObject A E (C.toDGFunctor.obj x) (C.toDGFunctor.obj y)) p :=
  ((tensorLeftHom (homObject A D x b.val)
    (epsilonComplex A ⊗ term A D w b.val y)
    (epsilonComplex A ⊗ homObject A E (C.toDGFunctor.obj b.val) (C.toDGFunctor.obj y))).f p
    ((tensorLeftHom (epsilonComplex A) (term A D w b.val y)
      (homObject A E (C.toDGFunctor.obj b.val) (C.toDGFunctor.obj y))).f p f)).comp
    (evaluationPrefixAction A C b x y) (add_zero p)

lemma pathEvaluation_cons_differential (C : ContractedFunctor A D S E)
    (b : S) (w : Word S) (x y : D) :
    δ 0 1 (pathEvaluation A C (b :: w) x y) =
    (eraseFirst A D b w x y).comp (pathEvaluation A C w x y) (add_zero 1) +
    pathEvaluationTail A C b w x y 1 (δ 0 1 (pathEvaluation A C w b.val y)) := by
  rw [pathEvaluation_cons_action, evaluationPrefixAction_evaluation_differential,
    ← pathEvaluation_prepend, ← Cochain.comp_assoc_of_second_is_zero_cochain]
  rfl

end SerrePositivity.DifferentialGraded.DGQuotient
end

end PathEvaluationDifferential

/-! ## EvaluationErasure（旧 SerrePositivity/DifferentialGraded/Quotient/EvaluationErasure.lean） -/

/-! # 全path評価のHom微分とε消去作用素の整合性 -/

@[expose] public section EvaluationErasure
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D] [Small.{u} D]
  {S : Set D} {E : Type w} [DGCategory A E]

lemma pathEvaluationTail_internalEvaluation (C : ContractedFunctor A D S E)
    (b : S) (w : Word S) (x y : D) (p : ℤ)
    (f : Cochain (term A D w b.val y) (internalHom A D S b.val y) p) :
    pathEvaluationTail A C b w x y p
      (f.comp (internalEvaluation A C b.val y) (add_zero p)) =
    (prefixTailCochain A D b w x y p f).comp (internalEvaluation A C x y) (add_zero p) := by
  rw [pathEvaluationTail, tensorLeftHom_cochain_comp, tensorLeftHom_cochain_comp,
    Cochain.comp_assoc_of_third_is_zero_cochain, ← internalEvaluation_prefixPath,
    ← Cochain.comp_assoc_of_second_is_zero_cochain]
  rfl

lemma pathEvaluation_differential (C : ContractedFunctor A D S E) (w : Word S) (x y : D) :
    δ 0 1 (pathEvaluation A C w x y) =
      (eraseRow A D w x y).comp (internalEvaluation A C x y) (add_zero 1) := by
  induction w generalizing x with
  | nil => rw [pathEvaluation_nil, δ_ofHom, eraseRow_nil, Cochain.zero_comp]
  | cons b w ih =>
    rw [pathEvaluation_cons_differential, ih b.val, pathEvaluationTail_internalEvaluation,
      eraseRow_cons, Cochain.add_comp _ _ _ (add_zero 1),
      Cochain.comp_assoc_of_second_is_zero_cochain, internalEvaluation_precomp]

lemma internalEvaluation_differential (C : ContractedFunctor A D S E) (x y : D) :
    δ 0 1 (internalEvaluation A C x y) =
      (erasure A D S x y).comp (internalEvaluation A C x y) (add_zero 1) := by
  apply pathCochain_ext A D S x y 1
  intro w
  rw [← δ_ofHom_comp, internalEvaluation_precomp,
    ← Cochain.comp_assoc_of_first_is_zero_cochain, erasure_precomp]
  exact pathEvaluation_differential A C w x y

end SerrePositivity.DifferentialGraded.DGQuotient
end

end EvaluationErasure

/-! ## Evaluation（旧 SerrePositivity/DifferentialGraded/Quotient/Evaluation.lean） -/

/-! # 指定収縮付きdg関手の最終商Hom上の評価chain map -/

@[expose] public section Evaluation
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D] [Small.{u} D]
  {S : Set D} {E : Type w} [DGCategory A E]

/-- 指定収縮を使う評価は、最終Hom微分についての実際のchain mapとなる。 -/
def quotientEvaluation (C : ContractedFunctor A D S E) (x y : D) :
    quotientHom A D S x y ⟶ homObject A E (C.toDGFunctor.obj x) (C.toDGFunctor.obj y) :=
  perturbSourceMap (internalHom A D S x y)
    (homObject A E (C.toDGFunctor.obj x) (C.toDGFunctor.obj y))
    (erasure A D S x y) (erasure_closed A D S x y) (erasure_square_zero A D S x y)
    (internalEvaluation A C x y) (internalEvaluation_differential A C x y)

lemma quotientEvaluation_f (C : ContractedFunctor A D S E) (x y : D) (i : ℤ) :
    (quotientEvaluation A C x y).f i = (internalEvaluation A C x y).v i i (add_zero i) := rfl

lemma quotientEvaluation_original (C : ContractedFunctor A D S E) (x y : D) :
    originalHomInclusion A D S x y ≫ quotientEvaluation A C x y = C.toDGFunctor.map x y := by
  apply HomologicalComplex.Hom.ext
  funext i
  rw [HomologicalComplex.comp_f, originalHomInclusion_f, quotientEvaluation_f]
  have h := congrArg (fun f : Cochain (homObject A D x y)
      (homObject A E (C.toDGFunctor.obj x) (C.toDGFunctor.obj y)) 0 =>
    f.v i i (add_zero i)) (internalEvaluation_original A C x y)
  simpa only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v] using h

lemma quotientEvaluation_epsilon (C : ContractedFunctor A D S E) (b : S) :
    (quotientEvaluation A C b.val b.val).f (-1) (epsilonElement A D S b) = C.homotopy b := by
  have h := congrArg (fun f : Cochain (epsilonComplex A)
      (homObject A E (C.toDGFunctor.obj b.val) (C.toDGFunctor.obj b.val)) 0 =>
    f.v (-1) (-1) (add_zero (-1))
      ((singleObjXSelf (.up ℤ) (-1) (𝟙_ (ModuleCat.{u} A))).inv (1 : A)))
    (internalEvaluation_epsilon A C b)
  rw [cochain_ofHom_comp_apply, contractionCochain_generator] at h
  exact h

lemma quotientEvaluation_path (C : ContractedFunctor A D S E) (w : Word S) (x y : D) (i : ℤ) :
    (ι A D S x y w).f i ≫ (quotientEvaluation A C x y).f i =
      (pathEvaluation A C w x y).v i i (add_zero i) := by
  rw [quotientEvaluation_f]
  have h := congrArg (fun f : Cochain (term A D w x y)
      (homObject A E (C.toDGFunctor.obj x) (C.toDGFunctor.obj y)) 0 =>
    f.v i i (add_zero i)) (internalEvaluation_precomp A C x y w)
  simpa only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v] using h

lemma quotientEvaluation_unit (C : ContractedFunctor A D S E) (x : D) :
    quotientIdentity A D S x ≫ quotientEvaluation A C x x =
      eId (Complex A) (C.toDGFunctor.obj x) := by
  rw [quotientIdentity, Category.assoc, quotientEvaluation_original, C.toDGFunctor.map_id]

end SerrePositivity.DifferentialGraded.DGQuotient
end

end Evaluation

/-! ## EvaluationComposition（旧 SerrePositivity/DifferentialGraded/Quotient/EvaluationComposition.lean） -/

/-! # 最終Homの評価chain mapの合成保存 -/

@[expose] public section EvaluationComposition
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D] [Small.{u} D]
  {S : Set D} {E : Type w} [DGCategory A E]

lemma quotientEvaluation_composition (C : ContractedFunctor A D S E) (x y z : D) :
    quotientComposition A D S x y z ≫ quotientEvaluation A C x z =
    (quotientEvaluation A C x y ⊗ₘ quotientEvaluation A C y z) ≫
      eComp (Complex A) (C.toDGFunctor.obj x) (C.toDGFunctor.obj y) (C.toDGFunctor.obj z) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply mapBifunctor.hom_ext
  intro p q hn
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro a b
  change (quotientEvaluation A C x z).f n
      ((quotientComposition A D S x y z).f n
        (ιTensorObj (quotientHom A D S x y) (quotientHom A D S y z) p q n hn (a ⊗ₜ[A] b))) =
    (eComp (Complex A) (C.toDGFunctor.obj x) (C.toDGFunctor.obj y) (C.toDGFunctor.obj z)).f n
      ((quotientEvaluation A C x y ⊗ₘ quotientEvaluation A C y z).f n
        (ιTensorObj (quotientHom A D S x y) (quotientHom A D S y z) p q n hn (a ⊗ₜ[A] b)))
  rw [quotientComposition_apply, tensorMap_apply]
  simp only [quotientEvaluation_f]
  have h := congrArg (fun f : Cochain (internalHom A D S x y ⊗ internalHom A D S y z)
      (homObject A E (C.toDGFunctor.obj x) (C.toDGFunctor.obj z)) 0 =>
    f.v n n (add_zero n)
      (ιTensorObj (internalHom A D S x y) (internalHom A D S y z) p q n hn (a ⊗ₜ[A] b)))
    (internalEvaluation_composition A C x y z)
  rw [cochain_ofHom_comp_apply, cochain_comp_ofHom_apply, tensorZeroCochain_apply] at h
  exact h

end SerrePositivity.DifferentialGraded.DGQuotient
end

end EvaluationComposition

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite Drinfeld "Construction §3.1"] _root_.SerrePositivity.DifferentialGraded.DGQuotient.differential_epsilonElement
