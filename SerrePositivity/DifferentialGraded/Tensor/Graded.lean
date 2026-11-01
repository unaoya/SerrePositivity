module

public import SerrePositivity.DifferentialGraded.Tensor.Triple
public import SerrePositivity.DifferentialGraded.Tensor.Associator.Components
public import SerrePositivity.DifferentialGraded.Tensor.Bimodule.Actions
public import SerrePositivity.DifferentialGraded.Complexes.TensorGeneratorMaps
public import SerrePositivity.DifferentialGraded.Tensor.BalancedElements
public import SerrePositivity.DifferentialGraded.Tensor.Enriched
public import SerrePositivity.DifferentialGraded.Module.Cylinder
public import SerrePositivity.DifferentialGraded.Module.GradedSplitElements
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import SerrePositivity.DifferentialGraded.Module.Semifree.Resolution
public import SerrePositivity.DifferentialGraded.Module.Homotopy
public import SerrePositivity.DifferentialGraded.Functor.Basic
public import SerrePositivity.DifferentialGraded.Module.RestrictionColimits
public import SerrePositivity.DifferentialGraded.Module.RestrictionGradedSplit
public import SerrePositivity.DifferentialGraded.Tensor.ScalarExtension.CategoriesAndModules

/-!
# Tensor.Graded

## 概要
12 本に分かれていた同主題の構成と比較をまとめる。

## 方針
対応表の依存順に連結し、元の宣言・証明・名前空間を保持する。

## 規約
各元ファイルの section を分離し、variable・option の局所的な作用を保つ。

## 使われ方
DifferentialGraded の入口と、この主題を使う検査・下流モジュールから import する。
-/

/-! ## TriangleGenerators（旧 SerrePositivity/DifferentialGraded/Tensor/TriangleGenerators.lean） -/

/-! # 単位と結合比較の三角図式を三重包含上で計算する -/

@[expose] public section TriangleGenerators
universe u v w z

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory MonoidalCategory
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [Small.{u} B] [Small.{u} C]

lemma triangleLeft_ι (P : Bimodule A B C) (Q : Bimodule A C E)
    (b : B) (x y : C) (e : E) :
    associatorLeftι A B C C E P (Bimodule.diagonal A C) Q b x y e ≫
      composeValueMap A B C E (rightBimoduleUnitIso A B C P).hom
        (𝟙 (BimoduleCategory.of A C E Q)) b e =
    Q.value y e ◁ BalancedTensor.leftAction A C (P.leftAt b) x y ≫
      BalancedTensor.ι A C (Q.rightAt e) (P.leftAt b) y := by
  have ho := ι_composeValueMap A B C E (rightBimoduleUnitIso A B C P).hom
    (𝟙 (BimoduleCategory.of A C E Q)) b y e
  rw [CategoryTheory.Functor.map_id, rightBimoduleUnitIso_hom_value] at ho
  exact tensorLeft_generator_map
    (BalancedTensor.ι A C ((Bimodule.diagonal A C).rightAt y) (P.leftAt b) x)
    (BalancedTensor.ι A C (Q.rightAt e) ((compose A B C C P (Bimodule.diagonal A C)).leftAt b) y)
    (composeValueMap A B C E (rightBimoduleUnitIso A B C P).hom
      (𝟙 (BimoduleCategory.of A C E Q)) b e)
    (rightUnitValueIso A B C P b y).hom
    (BalancedTensor.ι A C (Q.rightAt e) (P.leftAt b) y)
    (BalancedTensor.leftAction A C (P.leftAt b) x y) ho
    (BalancedTensor.ι_yonedaEvaluation A C y (P.leftAt b) x)

lemma triangleRight_ι (P : Bimodule A B C) (Q : Bimodule A C E)
    (b : B) (x y : C) (e : E) :
    associatorLeftι A B C C E P (Bimodule.diagonal A C) Q b x y e ≫
      ((associatorValueIso A B C C E P (Bimodule.diagonal A C) Q b e).hom ≫
        composeValueMap A B C E (𝟙 (BimoduleCategory.of A B C P))
          (leftBimoduleUnitIso A C E Q).hom b e) =
    (α_ (Q.value y e) (x ⟶[Complex A] y) (P.value b x)).inv ≫
      (BalancedTensor.rightAction A C (Q.rightAt e) x y ▷ P.value b x) ≫
        BalancedTensor.ι A C (Q.rightAt e) (P.leftAt b) x := by
  have ho := ι_composeValueMap A B C E (𝟙 (BimoduleCategory.of A B C P))
    (leftBimoduleUnitIso A C E Q).hom b x e
  rw [CategoryTheory.Functor.map_id, leftBimoduleUnitIso_hom_value] at ho
  have hc := congrArg (fun k => k ≫ composeValueMap A B C E
    (𝟙 (BimoduleCategory.of A B C P)) (leftBimoduleUnitIso A C E Q).hom b e)
    (associatorLeftι_hom A B C C E P (Bimodule.diagonal A C) Q b x y e)
  have ht := tensorRight_generator_map
    (BalancedTensor.ι A C (Q.rightAt e) ((Bimodule.diagonal A C).leftAt x) y)
    (BalancedTensor.ι A C ((compose A C C E (Bimodule.diagonal A C) Q).rightAt e)
      (P.leftAt b) x)
    (composeValueMap A B C E (𝟙 (BimoduleCategory.of A B C P))
      (leftBimoduleUnitIso A C E Q).hom b e)
    (leftUnitValueIso A C E Q x e).hom
    (BalancedTensor.ι A C (Q.rightAt e) (P.leftAt b) x)
    (BalancedTensor.rightAction A C (Q.rightAt e) x y) ho
    (ι_leftUnitValueIso_hom A C E Q x y e)
  exact (Category.assoc _ _ _).symm.trans (hc.trans ht)

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end TriangleGenerators

/-! ## Triangle（旧 SerrePositivity/DifferentialGraded/Tensor/Triangle.lean） -/

/-! # 閉零bimodule圏の単位・結合比較の三角coherence -/

@[expose] public section Triangle
universe u v w z

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory MonoidalCategory
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [Small.{u} B] [Small.{u} C]

lemma triangleValue (P : Bimodule A B C) (Q : Bimodule A C E) (b : B) (e : E) :
    composeValueMap A B C E (rightBimoduleUnitIso A B C P).hom
      (𝟙 (BimoduleCategory.of A C E Q)) b e =
    (associatorValueIso A B C C E P (Bimodule.diagonal A C) Q b e).hom ≫
      composeValueMap A B C E (𝟙 (BimoduleCategory.of A B C P))
        (leftBimoduleUnitIso A C E Q).hom b e := by
  apply associatorLeft_hom_ext A B C C E P (Bimodule.diagonal A C) Q b e
  intro x y
  have hb := tensor_associator_balance
    (BalancedTensor.rightAction A C (Q.rightAt e) x y)
    (BalancedTensor.leftAction A C (P.leftAt b) x y)
    (BalancedTensor.ι A C (Q.rightAt e) (P.leftAt b) x)
    (BalancedTensor.ι A C (Q.rightAt e) (P.leftAt b) y)
    (BalancedTensor.condition A C (Q.rightAt e) (P.leftAt b) x y)
  exact (triangleLeft_ι A B C E P Q b x y e).trans
    (hb.trans (triangleRight_ι A B C E P Q b x y e).symm)

/-- 対角Cを中間に挿入する三角図式は、実際の閉零bimodule射として可換。 -/
lemma triangle (P : Bimodule A B C) (Q : Bimodule A C E) :
    composeMap A B C E (rightBimoduleUnitIso A B C P).hom
      (𝟙 (BimoduleCategory.of A C E Q)) =
    (associatorIso A B C C E P (Bimodule.diagonal A C) Q).hom ≫
      composeMap A B C E (𝟙 (BimoduleCategory.of A B C P))
        (leftBimoduleUnitIso A C E Q).hom := by
  apply BimoduleCategory.value_hom_ext A B E
  intro b e
  simp only [CategoryTheory.Functor.map_comp, composeMap_value_eval,
    associatorIso_hom_value_eval]
  exact triangleValue A B C E P Q b e

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end Triangle

/-! ## ModuleCylinderKFlat（旧 SerrePositivity/DifferentialGraded/Tensor/ModuleCylinderKFlat.lean） -/

/-! # K-flat複体とのtensorとdg加群cylinderの相対K-flat性

## 概要
K-flat複体とのtensorとdg加群cylinderの相対K-flat性。

## 方針
balanced tensor・全Hom自然性・作用の既存計算と普遍性を使い、条件を明示して比較する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Bimodule/CylinderKFlat.lean。局所導来合成の計算部品、一般Morita・
相対tensor・Hochschild型構成での作用と符号の比較に使える。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section ModuleCylinderKFlat
universe u v

noncomputable section
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory
variable (A : Type u) [CommRing A]

lemma complexKFlat_interval : complexKFlat A (dgInterval A) := by
  intro L hL
  exact cochainAcyclic_of_homotopyEquiv (complexKFlat_unit A L hL)
    (tensorIntervalHomotopyEquiv A L).symm

variable (D : Type v) [DGCategory A D] [Small.{u} D]

lemma moduleRelativeKFlat_tensor (K : Complex A) (hK : complexKFlat A K)
    (M : RightModule A D) (hM : moduleRelativeKFlat A D M) :
    moduleRelativeKFlat A D (tensorModule K M) := by
  intro N hN
  exact cochainAcyclic_of_iso (hK _ (hM N hN)) (BalancedTensor.tensorModuleIso A D K M N).symm

lemma modulePrecylinder_relativeKFlat (M : ModuleCategory A D)
    (hM : moduleRelativeKFlat A D (ForgetEnrichment.to (Complex A) M)) :
    moduleRelativeKFlat A D
      (ForgetEnrichment.to (Complex A) (modulePrecylinder A D M).I) :=
  moduleRelativeKFlat_tensor A D (dgInterval A) (complexKFlat_interval A) _ hM

end SerrePositivity.DifferentialGraded
end

end ModuleCylinderKFlat

/-! ## GradedSplitElements（旧 SerrePositivity/DifferentialGraded/Tensor/GradedSplitElements.lean） -/

/-! # 全作用と可換するgraded splittingのbalanced tensorへの像 -/

@[expose] public section GradedSplitElements
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory Limits Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 固定左加群とのtensor写像を、元のbalanced tensor対象間の射として読む。 -/
def rightTensorMap {M N : ModuleCategory A D} (L : LeftModule A D) (f : M ⟶ N) :
    obj A D (ForgetEnrichment.to (Complex A) M) L ⟶
      obj A D (ForgetEnrichment.to (Complex A) N) L :=
  (rightTensorFunctor A D L).map f

lemma rightTensorMap_element {M N : ModuleCategory A D} (L : LeftModule A D)
    (f : M ⟶ N) (x : D) {r s n : ℤ}
    (m : ((ForgetEnrichment.to (Complex A) M).obj (op x)).X r)
    (v : (L.obj x).X s) (hn : r + s = n) :
    (rightTensorMap A D L f).f n
      (element A D (ForgetEnrichment.to (Complex A) M) L x m v hn) =
    element A D (ForgetEnrichment.to (Complex A) N) L x
      (((moduleEvaluation A D x).map f).f r m) v hn := by
  have h := map_element A D f (𝟙 (ForgetEnrichment.of (Complex A) L)) x m v hn
  simpa only [rightTensorMap, rightTensorFunctor, ForgetEnrichment.to_of,
    CategoryTheory.Functor.map_id,
    HomologicalComplex.id_f, ModuleCat.id_apply] using h

variable {M N P : ModuleCategory A D} {f : M ⟶ N} {g : N ⟶ P}

/-- tensor後のretractionは閉じているとは限らない次数零cochain。 -/
def tensorRetractionCochain (s : ModuleGradedSplit A D f g) (L : LeftModule A D) :
    Cochain (obj A D (ForgetEnrichment.to (Complex A) N) L)
      (obj A D (ForgetEnrichment.to (Complex A) M) L) 0 :=
  (rightHomMap A D (ForgetEnrichment.to (Complex A) N)
    (ForgetEnrichment.to (Complex A) M) L).f 0 s.retractionElement

/-- tensor後のsectionも主Homから得た次数零cochain。 -/
def tensorSectionCochain (s : ModuleGradedSplit A D f g) (L : LeftModule A D) :
    Cochain (obj A D (ForgetEnrichment.to (Complex A) P) L)
      (obj A D (ForgetEnrichment.to (Complex A) N) L) 0 :=
  (rightHomMap A D (ForgetEnrichment.to (Complex A) P)
    (ForgetEnrichment.to (Complex A) N) L).f 0 s.sectionElement

lemma tensorRetractionCochain_element (s : ModuleGradedSplit A D f g) (L : LeftModule A D)
    (x : D) {r t a : ℤ} (ha : r + t = a)
    (m : ((ForgetEnrichment.to (Complex A) N).obj (op x)).X r) (v : (L.obj x).X t) :
    (tensorRetractionCochain A D s L).v a a (add_zero a)
      (element A D (ForgetEnrichment.to (Complex A) N) L x m v ha) =
    element A D (ForgetEnrichment.to (Complex A) M) L x (s.retraction x r m) v ha := by
  change (((rightHomMap A D (ForgetEnrichment.to (Complex A) N)
    (ForgetEnrichment.to (Complex A) M) L).f 0 s.retractionElement).v a a (add_zero a))
    (element A D (ForgetEnrichment.to (Complex A) N) L x m v ha) = _
  rw [rightHomMap_element_of_sum A D L _ x m v ha (zero_add r) (add_zero a),
    s.retractionElement_π]
  rfl

lemma tensorSectionCochain_element (s : ModuleGradedSplit A D f g) (L : LeftModule A D)
    (x : D) {r t a : ℤ} (ha : r + t = a)
    (m : ((ForgetEnrichment.to (Complex A) P).obj (op x)).X r) (v : (L.obj x).X t) :
    (tensorSectionCochain A D s L).v a a (add_zero a)
      (element A D (ForgetEnrichment.to (Complex A) P) L x m v ha) =
    element A D (ForgetEnrichment.to (Complex A) N) L x (s.section_ x r m) v ha := by
  change (((rightHomMap A D (ForgetEnrichment.to (Complex A) P)
    (ForgetEnrichment.to (Complex A) N) L).f 0 s.sectionElement).v a a (add_zero a))
    (element A D (ForgetEnrichment.to (Complex A) P) L x m v ha) = _
  rw [rightHomMap_element_of_sum A D L _ x m v ha (zero_add r) (add_zero a),
    s.sectionElement_π]
  rfl

end SerrePositivity.DifferentialGraded.BalancedTensor
end

end GradedSplitElements

/-! ## GradedSplitLaws（旧 SerrePositivity/DifferentialGraded/Tensor/GradedSplitLaws.lean） -/

/-! # balanced tensor後の次数付き分裂の恒等式 -/

@[expose] public section GradedSplitLaws
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory Limits Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable {M N P : ModuleCategory A D} {f : M ⟶ N} {g : N ⟶ P}

lemma tensor_inclusion_retraction (s : ModuleGradedSplit A D f g) (L : LeftModule A D) :
    (Cochain.ofHom (rightTensorMap A D L f)).comp
      (tensorRetractionCochain A D s L) (zero_add 0) =
      Cochain.ofHom (𝟙 (obj A D (ForgetEnrichment.to (Complex A) M) L)) := by
  apply cochain_zero_element_ext A D (ForgetEnrichment.to (Complex A) M) L
  intro x r t a ha m v
  simp only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, ModuleCat.comp_apply]
  rw [rightTensorMap_element A D L f x m v ha,
    tensorRetractionCochain_element A D s L x ha _ v]
  have h := congrArg (fun k => k m) (s.inclusion_retraction x r)
  change s.retraction x r (((moduleEvaluation A D x).map f).f r m) = m at h
  rw [h]
  rfl

lemma tensor_section_projection (s : ModuleGradedSplit A D f g) (L : LeftModule A D) :
    (tensorSectionCochain A D s L).comp
      (Cochain.ofHom (rightTensorMap A D L g)) (add_zero 0) =
      Cochain.ofHom (𝟙 (obj A D (ForgetEnrichment.to (Complex A) P) L)) := by
  apply cochain_zero_element_ext A D (ForgetEnrichment.to (Complex A) P) L
  intro x r t a ha m v
  simp only [Cochain.comp_zero_cochain_v, Cochain.ofHom_v, ModuleCat.comp_apply]
  rw [tensorSectionCochain_element A D s L x ha m v,
    rightTensorMap_element A D L g x (s.section_ x r m) v ha]
  have h := congrArg (fun k => k m) (s.section_projection x r)
  change ((moduleEvaluation A D x).map g).f r (s.section_ x r m) = m at h
  rw [h]
  rfl

lemma element_add_left (M : RightModule A D) (L : LeftModule A D) (x : D)
    {r t a : ℤ} (ha : r + t = a) (m m' : (M.obj (op x)).X r) (v : (L.obj x).X t) :
    element A D M L x (m + m') v ha =
      element A D M L x m v ha + element A D M L x m' v ha := by
  simp only [element, TensorProduct.add_tmul, map_add]

lemma tensor_decomposition (s : ModuleGradedSplit A D f g) (L : LeftModule A D) :
    (tensorRetractionCochain A D s L).comp
        (Cochain.ofHom (rightTensorMap A D L f)) (add_zero 0) +
      (Cochain.ofHom (rightTensorMap A D L g)).comp
        (tensorSectionCochain A D s L) (zero_add 0) =
      Cochain.ofHom (𝟙 (obj A D (ForgetEnrichment.to (Complex A) N) L)) := by
  apply cochain_zero_element_ext A D (ForgetEnrichment.to (Complex A) N) L
  intro x r t a ha m v
  simp only [Cochain.add_v, Cochain.comp_zero_cochain_v,
    Cochain.ofHom_v, ModuleCat.hom_add, LinearMap.add_apply, ModuleCat.comp_apply]
  rw [tensorRetractionCochain_element A D s L x ha m v,
    rightTensorMap_element A D L f x (s.retraction x r m) v ha,
    rightTensorMap_element A D L g x m v ha,
    tensorSectionCochain_element A D s L x ha _ v, ← element_add_left]
  have h := congrArg (fun k => k m) (s.decomposition x r)
  change ((moduleEvaluation A D x).map f).f r (s.retraction x r m) +
    s.section_ x r (((moduleEvaluation A D x).map g).f r m) = m at h
  rw [h]
  rfl

end SerrePositivity.DifferentialGraded.BalancedTensor
end

end GradedSplitLaws

/-! ## GradedSplit（旧 SerrePositivity/DifferentialGraded/Tensor/GradedSplit.lean） -/

/-! # graded-split拡張のbalanced tensorによる保存 -/

@[expose] public section GradedSplit
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory Limits Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable {M N P : ModuleCategory A D} {f : M ⟶ N} {g : N ⟶ P}

/-- 全作用と可換するgraded-split拡張をtensorした短い複体。 -/
def tensorShortComplex (s : ModuleGradedSplit A D f g) (L : LeftModule A D) :
    ShortComplex (Complex A) :=
  ShortComplex.mk (rightTensorMap A D L f) (rightTensorMap A D L g) (by
    change (rightTensorFunctor A D L).map f ≫ (rightTensorFunctor A D L).map g = 0
    rw [← CategoryTheory.Functor.map_comp, s.inclusion_projection, CategoryTheory.Functor.map_zero])

/-- tensor後のsection/retractionは各次数で短い複体を分裂する。 -/
def tensorDegreeSplitting (s : ModuleGradedSplit A D f g) (L : LeftModule A D) (n : ℤ) :
    ((tensorShortComplex A D s L).map
      (HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) n)).Splitting where
  r := (tensorRetractionCochain A D s L).v n n (add_zero n)
  s := (tensorSectionCochain A D s L).v n n (add_zero n)
  f_r := by
    have h := Cochain.congr_v (tensor_inclusion_retraction A D s L) n n (add_zero n)
    simpa only [tensorShortComplex, ShortComplex.map, HomologicalComplex.eval_map,
      HomologicalComplex.eval_obj,
      Cochain.zero_cochain_comp_v, Cochain.ofHom_v, HomologicalComplex.id_f] using h
  s_g := by
    have h := Cochain.congr_v (tensor_section_projection A D s L) n n (add_zero n)
    simpa only [tensorShortComplex, ShortComplex.map, HomologicalComplex.eval_map,
      HomologicalComplex.eval_obj,
      Cochain.comp_zero_cochain_v, Cochain.ofHom_v, HomologicalComplex.id_f] using h
  id := by
    have h := Cochain.congr_v (tensor_decomposition A D s L) n n (add_zero n)
    simpa only [tensorShortComplex, ShortComplex.map, HomologicalComplex.eval_map,
      HomologicalComplex.eval_obj,
      Cochain.add_v, Cochain.comp_zero_cochain_v, Cochain.ofHom_v,
      HomologicalComplex.id_f] using h

/-- graded-split拡張は任意の左加群とのtensorで短完全列になる。 -/
lemma tensorShortComplex_shortExact (s : ModuleGradedSplit A D f g) (L : LeftModule A D) :
    (tensorShortComplex A D s L).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  exact (tensorDegreeSplitting A D s L n).shortExact

/-- tensor後のacyclic性はgraded-split拡張の両端から中央へ伝わる。 -/
lemma tensor_acyclic_of_gradedSplit (s : ModuleGradedSplit A D f g) (L : LeftModule A D)
    (hM : (obj A D (ForgetEnrichment.to (Complex A) M) L).Acyclic)
    (hP : (obj A D (ForgetEnrichment.to (Complex A) P) L).Acyclic) :
    (obj A D (ForgetEnrichment.to (Complex A) N) L).Acyclic :=
  (tensorShortComplex_shortExact A D s L).acyclic_X₂ hM hP

end BalancedTensor

open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable {M N P : ModuleCategory A D} {f : M ⟶ N} {g : N ⟶ P}

/-- 相対K-flat性は全作用と可換するgraded-split拡張で閉じる。 -/
lemma moduleRelativeKFlat_of_gradedSplit (s : ModuleGradedSplit A D f g)
    (hM : moduleRelativeKFlat A D (ForgetEnrichment.to (Complex A) M))
    (hP : moduleRelativeKFlat A D (ForgetEnrichment.to (Complex A) P)) :
    moduleRelativeKFlat A D (ForgetEnrichment.to (Complex A) N) := by
  intro L hL
  exact BalancedTensor.tensor_acyclic_of_gradedSplit A D s L (hM L hL) (hP L hL)

end SerrePositivity.DifferentialGraded
end

end GradedSplit

/-! ## Semifree（旧 SerrePositivity/DifferentialGraded/Tensor/Semifree.lean） -/

/-! # 非有界semifree dg加群の相対K-flat性 -/

@[expose] public section Semifree
universe u v

noncomputable section
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- semifree filtrationの各段階は相対K-flat。 -/
lemma ModuleSemifreeFiltration.relativeKFlat_stage {M : ModuleCategory A D}
    (F : ModuleSemifreeFiltration A D M) (n : ℕ) :
    moduleRelativeKFlat A D (ForgetEnrichment.to (Complex A) (F.stage n)) := by
  induction n with
  | zero => exact sphereFreePresentation_relativeKFlat A D F.initial
  | succ n ih =>
    exact moduleRelativeKFlat_of_gradedSplit A D (F.split n) ih
      (sphereFreePresentation_relativeKFlat A D (F.quotientPresentation n))

/-- 網羅的filtrationの実際の余極限から相対K-flat性を得る。 -/
lemma ModuleSemifreeFiltration.relativeKFlat {M : ModuleCategory A D}
    (F : ModuleSemifreeFiltration A D M) :
    moduleRelativeKFlat A D (ForgetEnrichment.to (Complex A) M) := by
  have hc := moduleRelativeKFlat_sequentialColimit A D (Functor.ofSequence F.transition)
    (fun n => F.relativeKFlat_stage A D n)
  let e : colimit (Functor.ofSequence F.transition) ≅ M :=
    (colimit.isColimit _).coconePointUniqueUpToIso F.isColimit ≪≫ F.iso
  exact moduleRelativeKFlat_of_iso A D e.symm hc

/-- 任意可換環・非有界dg加群のsemifree性は相対K-flat性を含意する。 -/
lemma moduleSemifree_relativeKFlat {M : ModuleCategory A D} (h : moduleSemifree A D M) :
    moduleRelativeKFlat A D (ForgetEnrichment.to (Complex A) M) := by
  obtain ⟨F⟩ := h
  exact F.relativeKFlat A D

/-- 任意dg加群の既存semifree解像度は相対K-flat解像度にもなる。 -/
theorem exists_relativeKFlat_resolution (M : ModuleCategory A D) :
    ∃ (P : ModuleCategory A D) (q : P ⟶ M),
      moduleSemifree A D P ∧ moduleRelativeKFlat A D (ForgetEnrichment.to (Complex A) P) ∧
        moduleDegreewiseSurjective A D q ∧ moduleQuasiIso A D q := by
  obtain ⟨P, q, hP, hs, hq⟩ := exists_semifree_resolution A D M
  exact ⟨P, q, hP, moduleSemifree_relativeKFlat A D hP, hs, hq⟩

end SerrePositivity.DifferentialGraded
end

end Semifree

/-! ## Homotopy（旧 SerrePositivity/DifferentialGraded/Tensor/Homotopy.lean） -/

/-! # balanced tensorによる全dg自然なホモトピーの保存 -/

@[expose] public section Homotopy
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory Limits Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 主Hom写像の閉零制限は既存balanced tensorの射になる。 -/
lemma rightHomMap_closedElement (L : LeftModule A D) {M N : ModuleCategory A D} (f : M ⟶ N) :
    (rightHomMap A D (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) N) L).f 0
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) f)).val =
      Cochain.ofHom (rightTensorMap A D L f) := by
  apply cochain_zero_element_ext A D (ForgetEnrichment.to (Complex A) M) L
  intro x r s a ha m v
  rw [rightHomMap_element_of_sum A D L _ x m v ha (zero_add r) (add_zero a),
    ← moduleEvaluation_cochain A D x f]
  simp only [Cochain.ofHom_v]
  exact (rightTensorMap_element A D L f x m v ha).symm

/-- tensorの主dg関手と通常関手は閉零射で一致する。 -/
lemma rightTensorDG_map (L : LeftModule A D) {M N : ModuleCategory A D} (f : M ⟶ N) :
    (closedToComplex A).map ((rightTensorDG A D L).onClosed.map f) =
      rightTensorMap A D L f := by
  apply Cochain.ofHom_injective
  have h := mapFromUnit_cochain A
    (obj A D (ForgetEnrichment.to (Complex A) M) L)
    (obj A D (ForgetEnrichment.to (Complex A) N) L)
    (ForgetEnrichment.homTo (Complex A) f ≫
      rightHomMap A D (ForgetEnrichment.to (Complex A) M)
        (ForgetEnrichment.to (Complex A) N) L)
  rw [cycleFromUnit_postcomp] at h
  exact h.trans (rightHomMap_closedElement A D L f)

/-- 対象ごとの独立なホモトピーでなく、全dg自然な加群ホモトピーをtensorで送る。 -/
lemma rightTensorMap_homotopy (L : LeftModule A D) {M N : ModuleCategory A D} {f g : M ⟶ N}
    (h : ModuleHomotopy A D f g) :
    Nonempty (Homotopy (rightTensorMap A D L f) (rightTensorMap A D L g)) := by
  have hb := (moduleHomotopy_nonempty_iff A D f g).1 ⟨h⟩
  have ht := (rightTensorDG A D L).preserves_boundary f g hb
  have hc := (complex_boundary_iff A _ _ _ _).1 ht
  change Nonempty (Homotopy
    ((closedToComplex A).map ((rightTensorDG A D L).onClosed.map f))
    ((closedToComplex A).map ((rightTensorDG A D L).onClosed.map g))) at hc
  rw [rightTensorDG_map, rightTensorDG_map] at hc
  exact hc

/-- 固定左加群とのtensorを、主K(D)から既存K(A)への関手に降ろす。 -/
def rightTensorHomotopyFunctor (L : LeftModule A D) : ModuleHomotopyCategory A D ⥤
    _root_.HomotopyCategory (ModuleCat.{u} A) (.up ℤ) :=
  CategoryTheory.Quotient.lift _ (rightTensorFunctor A D L ⋙
    _root_.HomotopyCategory.quotient (ModuleCat.{u} A) (.up ℤ)) (by
      intro M N f g hb
      obtain ⟨h⟩ := (moduleHomotopy_nonempty_iff A D f g).2 hb
      obtain ⟨ht⟩ := rightTensorMap_homotopy A D L h
      exact _root_.HomotopyCategory.eq_of_homotopy _ _ ht)

lemma rightTensorHomotopyFunctor_fac (L : LeftModule A D) :
    moduleToHomotopy A D ⋙ rightTensorHomotopyFunctor A D L =
      rightTensorFunctor A D L ⋙
        _root_.HomotopyCategory.quotient (ModuleCat.{u} A) (.up ℤ) :=
  CategoryTheory.Quotient.lift_spec _ _ _

end SerrePositivity.DifferentialGraded.BalancedTensor
end

end Homotopy

/-! ## LeftNaturality（旧 SerrePositivity/DifferentialGraded/Tensor/LeftNaturality.lean） -/

/-! # 固定左加群を動かすtensor関手の自然変換 -/

@[expose] public section LeftNaturality
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

def rightTensorLeftMap {L L' : LeftModuleCategory A D} (g : L ⟶ L') :
    rightTensorFunctor A D (ForgetEnrichment.to (Complex A) L) ⟶
      rightTensorFunctor A D (ForgetEnrichment.to (Complex A) L') where
  app M := map A D (𝟙 M) g
  naturality {M N} f := by
    change map A D f (𝟙 L) ≫ map A D (𝟙 N) g = map A D (𝟙 M) g ≫ map A D f (𝟙 L')
    rw [← map_comp, ← map_comp]
    simp only [Category.id_comp, Category.comp_id]

lemma rightTensorLeftMap_id (L : LeftModuleCategory A D) :
    rightTensorLeftMap A D (𝟙 L) = 𝟙 _ := by
  apply NatTrans.ext
  funext M
  exact map_id A D M L

lemma rightTensorLeftMap_comp {L L' L'' : LeftModuleCategory A D} (f : L ⟶ L') (g : L' ⟶ L'') :
    rightTensorLeftMap A D (f ≫ g) = rightTensorLeftMap A D f ≫ rightTensorLeftMap A D g := by
  apply NatTrans.ext
  funext M
  change map A D (𝟙 M) (f ≫ g) = map A D (𝟙 M) f ≫ map A D (𝟙 M) g
  simpa only [Category.id_comp] using map_comp A D (𝟙 M) (𝟙 M) f g

/-- 全Hom境界による主K(D)上でも左加群の射は自然変換を与える。 -/
def rightTensorHomotopyLeftMap {L L' : LeftModuleCategory A D} (g : L ⟶ L') :
    rightTensorHomotopyFunctor A D (ForgetEnrichment.to (Complex A) L) ⟶
      rightTensorHomotopyFunctor A D (ForgetEnrichment.to (Complex A) L') :=
  CategoryTheory.Quotient.natTransLift _
    (eqToHom (rightTensorHomotopyFunctor_fac A D (ForgetEnrichment.to (Complex A) L)) ≫
      Functor.whiskerRight (rightTensorLeftMap A D g)
        (_root_.HomotopyCategory.quotient (ModuleCat.{u} A) (.up ℤ)) ≫
      eqToHom (rightTensorHomotopyFunctor_fac A D (ForgetEnrichment.to (Complex A) L')).symm)

lemma rightTensorHomotopyLeftMap_app {L L' : LeftModuleCategory A D} (g : L ⟶ L')
    (M : ModuleCategory A D) :
    (rightTensorHomotopyLeftMap A D g).app ((moduleToHomotopy A D).obj M) =
      (_root_.HomotopyCategory.quotient (ModuleCat.{u} A) (.up ℤ)).map (map A D (𝟙 M) g) := by
  simp only [rightTensorHomotopyLeftMap, CategoryTheory.Quotient.natTransLift_app,
    NatTrans.comp_app, eqToHom_app]
  rfl

lemma rightTensorHomotopyLeftMap_id (L : LeftModuleCategory A D) :
    rightTensorHomotopyLeftMap A D (𝟙 L) = 𝟙 _ := by
  apply NatTrans.ext
  funext X
  obtain ⟨M⟩ := X
  change (rightTensorHomotopyLeftMap A D (𝟙 L)).app ((moduleToHomotopy A D).obj M) = 𝟙 _
  rw [rightTensorHomotopyLeftMap_app, map_id, CategoryTheory.Functor.map_id]
  rfl

lemma rightTensorHomotopyLeftMap_comp {L L' L'' : LeftModuleCategory A D}
    (f : L ⟶ L') (g : L' ⟶ L'') :
    rightTensorHomotopyLeftMap A D (f ≫ g) =
      rightTensorHomotopyLeftMap A D f ≫ rightTensorHomotopyLeftMap A D g := by
  apply NatTrans.ext
  funext X
  obtain ⟨M⟩ := X
  change (rightTensorHomotopyLeftMap A D (f ≫ g)).app ((moduleToHomotopy A D).obj M) =
    (rightTensorHomotopyLeftMap A D f).app ((moduleToHomotopy A D).obj M) ≫
      (rightTensorHomotopyLeftMap A D g).app ((moduleToHomotopy A D).obj M)
  rw [rightTensorHomotopyLeftMap_app, rightTensorHomotopyLeftMap_app,
    rightTensorHomotopyLeftMap_app, ← CategoryTheory.Functor.map_comp]
  congr 1
  simpa only [Category.id_comp] using map_comp A D (𝟙 M) (𝟙 M) f g

/-- 左加群の閉零圏から、主K(D)上のtensor関手の圏への関手。 -/
def rightTensorHomotopyBifunctor : LeftModuleCategory A D ⥤
    (ModuleHomotopyCategory A D ⥤ _root_.HomotopyCategory (ModuleCat.{u} A) (.up ℤ)) where
  obj L := rightTensorHomotopyFunctor A D (ForgetEnrichment.to (Complex A) L)
  map g := rightTensorHomotopyLeftMap A D g
  map_id L := rightTensorHomotopyLeftMap_id A D L
  map_comp f g := rightTensorHomotopyLeftMap_comp A D f g

end SerrePositivity.DifferentialGraded.BalancedTensor
end

end LeftNaturality

/-! ## ObjectwiseKFlat（旧 SerrePositivity/DifferentialGraded/Tensor/ObjectwiseKFlat.lean） -/

/-! # local A-K-flat Homの下でのobjectwise K-flat性

相対K-flat性とは別の条件を使い、Hom複体のK-flat仮定をこの結果にだけ置く。
-/

@[expose] public section ObjectwiseKFlat
universe u v w w'

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits HomologicalComplex
variable (A : Type u) [CommRing A]

/-- A上K-flat性は次数ごと分裂する複体拡張で閉じる。 -/
lemma complexKFlat_of_degreewiseSplit (S : ShortComplex (Complex A))
    (σ : ∀ n, (S.map (HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) n)).Splitting)
    (h₁ : complexKFlat A S.X₁) (h₃ : complexKFlat A S.X₃) : complexKFlat A S.X₂ := by
  intro L hL
  exact cochainTensor_acyclic_of_degreewiseSplit S σ L (h₁ L hL) (h₃ L hL)

variable (D : Type v) [DGCategory A D]

/-- 各Hom複体のA上K-flat性。対象集合のsmallnessとは独立。 -/
def localHomKFlat : Prop := ∀ x y : D, complexKFlat A (x ⟶[Complex A] y)

/-- 右dg加群の各評価複体のA上K-flat性。相対条件とは区別する。 -/
def moduleObjectwiseKFlat (M : RightModule A D) : Prop :=
  ∀ x : D, complexKFlat A (M.obj (Opposite.op x))

variable [Small.{u} D]

/-- local HomがA上K-flatなら、K-flat生成複体による自由加群はobjectwise K-flat。 -/
lemma freeAt_objectwiseKFlat (hD : localHomKFlat A D) (x : D) (K : Complex A)
    (hK : complexKFlat A K) :
    moduleObjectwiseKFlat A D (ForgetEnrichment.to (Complex A) ((freeAt x).obj K)) := by
  intro y
  exact complexKFlat_tensor A hK (hD y x)

/-- 評価が余極限を保つことを使うobjectwise K-flat性のexact余極限閉性。 -/
lemma moduleObjectwiseKFlat_colimit {J : Type w} [Category.{w'} J] [Small.{u} J]
    [HasExactColimitsOfShape J (ModuleCat.{u} A)] (F : J ⥤ ModuleCategory A D)
    (h : ∀ j, moduleObjectwiseKFlat A D (ForgetEnrichment.to (Complex A) (F.obj j))) :
    moduleObjectwiseKFlat A D (ForgetEnrichment.to (Complex A) (colimit F)) := by
  intro x
  have hc := complexKFlat_colimit A (F ⋙ moduleEvaluation A D x) (fun j => h j x)
  exact complexKFlat_of_iso A (moduleEvaluationColimitIso A D F x) hc

/-- 全作用に関するgraded-split拡張はobjectwise K-flat性を保つ。 -/
lemma moduleObjectwiseKFlat_of_gradedSplit {M N P : ModuleCategory A D}
    {f : M ⟶ N} {g : N ⟶ P} (s : ModuleGradedSplit A D f g)
    (hM : moduleObjectwiseKFlat A D (ForgetEnrichment.to (Complex A) M))
    (hP : moduleObjectwiseKFlat A D (ForgetEnrichment.to (Complex A) P)) :
    moduleObjectwiseKFlat A D (ForgetEnrichment.to (Complex A) N) := by
  intro x
  let S : ShortComplex (Complex A) := ShortComplex.mk
    ((moduleEvaluation A D x).map f) ((moduleEvaluation A D x).map g) (by
      rw [← CategoryTheory.Functor.map_comp, s.inclusion_projection,
        CategoryTheory.Functor.map_zero])
  have σ : ∀ n, (S.map (HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) n)).Splitting :=
    fun n =>
      { r := s.retraction x n
        s := s.section_ x n
        f_r := s.inclusion_retraction x n
        s_g := s.section_projection x n
        id := s.decomposition x n }
  exact complexKFlat_of_degreewiseSplit A S σ (hM x) (hP x)

/-- sphere-free表示のobjectwise結果にだけlocal HomのA上K-flat性を要求する。 -/
lemma sphereFreePresentation_objectwiseKFlat (hD : localHomKFlat A D)
    {M : ModuleCategory A D} (S : ModuleSphereFreePresentation A D M) :
    moduleObjectwiseKFlat A D (ForgetEnrichment.to (Complex A) M) := by
  have := S.smallIndex
  have : HasExactColimitsOfShape (Discrete S.Index) (ModuleCat.{u} A) :=
    HasExactColimitsOfShape.of_domain_equivalence (ModuleCat.{u} A)
      (Discrete.equivalence (equivShrink.{u} S.Index).symm)
  have hc := moduleObjectwiseKFlat_colimit A D
    (Discrete.functor fun i => freeSphere A D (S.object i) (S.degree i))
    (fun i => freeAt_objectwiseKFlat A D hD (S.object i.as) _ (complexSphere_kFlat A _))
  intro x
  exact complexKFlat_of_iso A ((moduleEvaluation A D x).mapIso S.iso) (hc x)

/-- local K-flat Homの下でsemifree filtrationの各段階はobjectwise K-flat。 -/
lemma ModuleSemifreeFiltration.objectwiseKFlat_stage (hD : localHomKFlat A D)
    {M : ModuleCategory A D} (F : ModuleSemifreeFiltration A D M) (n : ℕ) :
    moduleObjectwiseKFlat A D (ForgetEnrichment.to (Complex A) (F.stage n)) := by
  induction n with
  | zero => exact sphereFreePresentation_objectwiseKFlat A D hD F.initial
  | succ n ih =>
    exact moduleObjectwiseKFlat_of_gradedSplit A D (F.split n) ih
      (sphereFreePresentation_objectwiseKFlat A D hD (F.quotientPresentation n))

/-- local K-flat Homの下でsemifree加群はobjectwise K-flat。 -/
lemma moduleSemifree_objectwiseKFlat (hD : localHomKFlat A D)
    {M : ModuleCategory A D} (hM : moduleSemifree A D M) :
    moduleObjectwiseKFlat A D (ForgetEnrichment.to (Complex A) M) := by
  obtain ⟨F⟩ := hM
  have : AB5OfSize.{0, 0} (ModuleCat.{u} A) := AB5OfSize_of_univLE (ModuleCat.{u} A)
  have hc := moduleObjectwiseKFlat_colimit A D (Functor.ofSequence F.transition)
    (fun n => F.objectwiseKFlat_stage A D hD n)
  let e : colimit (Functor.ofSequence F.transition) ≅ M :=
    (colimit.isColimit _).coconePointUniqueUpToIso F.isColimit ≪≫ F.iso
  intro x
  exact complexKFlat_of_iso A ((moduleEvaluation A D x).mapIso e).symm (hc x)

/-- local K-flat Homの下では相対/評価ごとの両条件を満たすsemifree解像度を取れる。 -/
theorem exists_objectwiseKFlat_resolution (hD : localHomKFlat A D) (M : ModuleCategory A D) :
    ∃ (P : ModuleCategory A D) (q : P ⟶ M),
      moduleSemifree A D P ∧ moduleRelativeKFlat A D (ForgetEnrichment.to (Complex A) P) ∧
        moduleObjectwiseKFlat A D (ForgetEnrichment.to (Complex A) P) ∧
        moduleDegreewiseSurjective A D q ∧ moduleQuasiIso A D q := by
  obtain ⟨P, q, hP, hk, hs, hq⟩ := exists_relativeKFlat_resolution A D M
  exact ⟨P, q, hP, hk, moduleSemifree_objectwiseKFlat A D hD hP, hs, hq⟩

end SerrePositivity.DifferentialGraded
end

end ObjectwiseKFlat

/-! ## RestrictionSemifree（旧 SerrePositivity/DifferentialGraded/Tensor/RestrictionSemifree.lean） -/

/-! # 生成cellの制限からsemifree加群の制限の相対K-flat性を得る

## 概要
生成cellの制限からsemifree加群の制限の相対K-flat性を得る。

## 方針
balanced tensor・全Hom自然性・作用の既存計算と普遍性を使い、条件を明示して比較する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Tensor/BimoduleRestrictionKFlat.lean。局所導来合成の計算部品、
一般Morita・相対tensor・Hochschild型構成での作用と符号の比較に使える。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section RestrictionSemifree
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits Opposite
variable (A : Type u) [CommRing A] (D : Type v) (E : Type w)
  [DGCategory A D] [DGCategory A E] [Small.{u} D] [Small.{u} E]
  (F : DGFunctor A Dᵒᵖ Eᵒᵖ)

/-- 制限されたsphere-free段階は、各生成cellの制限が相対K-flatなら相対K-flat。 -/
lemma sphereFreePresentation_restriction_relativeKFlat
    (hfree : ∀ (x : E) (n : ℤ), moduleRelativeKFlat A D
      (ForgetEnrichment.to (Complex A) ((moduleRestriction A D E F).obj (freeSphere A E x n))))
    {M : ModuleCategory A E} (S : ModuleSphereFreePresentation A E M) :
    moduleRelativeKFlat A D
      (ForgetEnrichment.to (Complex A) ((moduleRestriction A D E F).obj M)) := by
  have := S.smallIndex
  have : HasExactColimitsOfShape (Discrete S.Index) (ModuleCat.{u} A) :=
    HasExactColimitsOfShape.of_domain_equivalence (ModuleCat.{u} A)
      (Discrete.equivalence (equivShrink.{u} S.Index).symm)
  let G := Discrete.functor fun t => freeSphere A E (S.object t) (S.degree t)
  have hc := moduleRelativeKFlat_colimit A D (G ⋙ moduleRestriction A D E F)
    (fun t => hfree (S.object t.as) (S.degree t.as))
  exact moduleRelativeKFlat_of_iso A D
    (((moduleRestriction A D E F).mapIso S.iso) ≪≫
      moduleRestrictionColimitIso A D E F G) hc

lemma ModuleSemifreeFiltration.restriction_relativeKFlat_stage
    (hfree : ∀ (x : E) (n : ℤ), moduleRelativeKFlat A D
      (ForgetEnrichment.to (Complex A) ((moduleRestriction A D E F).obj (freeSphere A E x n))))
    {M : ModuleCategory A E} (S : ModuleSemifreeFiltration A E M) (n : ℕ) :
    moduleRelativeKFlat A D
      (ForgetEnrichment.to (Complex A) ((moduleRestriction A D E F).obj (S.stage n))) := by
  induction n with
  | zero => exact sphereFreePresentation_restriction_relativeKFlat A D E F hfree S.initial
  | succ n ih =>
    exact moduleRelativeKFlat_of_gradedSplit A D ((S.split n).restrict A D E F) ih
      (sphereFreePresentation_restriction_relativeKFlat A D E F hfree (S.quotientPresentation n))

/-- 制限の余極限保存とfiltrationの網羅性から、全体の相対K-flat性を得る。 -/
lemma ModuleSemifreeFiltration.restriction_relativeKFlat
    (hfree : ∀ (x : E) (n : ℤ), moduleRelativeKFlat A D
      (ForgetEnrichment.to (Complex A) ((moduleRestriction A D E F).obj (freeSphere A E x n))))
    {M : ModuleCategory A E} (S : ModuleSemifreeFiltration A E M) :
    moduleRelativeKFlat A D
      (ForgetEnrichment.to (Complex A) ((moduleRestriction A D E F).obj M)) := by
  let G := Functor.ofSequence S.transition
  have : AB5OfSize.{0, 0} (ModuleCat.{u} A) := AB5OfSize_of_univLE (ModuleCat.{u} A)
  have hc := moduleRelativeKFlat_colimit A D (G ⋙ moduleRestriction A D E F)
    (fun n => S.restriction_relativeKFlat_stage A D E F hfree n)
  let e : colimit G ≅ M := (colimit.isColimit G).coconePointUniqueUpToIso S.isColimit ≪≫ S.iso
  exact moduleRelativeKFlat_of_iso A D
    (((moduleRestriction A D E F).mapIso e.symm) ≪≫ moduleRestrictionColimitIso A D E F G) hc

lemma moduleSemifree_restriction_relativeKFlat
    (hfree : ∀ (x : E) (n : ℤ), moduleRelativeKFlat A D
      (ForgetEnrichment.to (Complex A) ((moduleRestriction A D E F).obj (freeSphere A E x n))))
    {M : ModuleCategory A E} (hM : moduleSemifree A E M) :
    moduleRelativeKFlat A D
      (ForgetEnrichment.to (Complex A) ((moduleRestriction A D E F).obj M)) := by
  obtain ⟨S⟩ := hM
  exact S.restriction_relativeKFlat A D E F hfree

end SerrePositivity.DifferentialGraded
end

end RestrictionSemifree

/-! ## RestrictionComparisonNaturality（旧 SerrePositivity/DifferentialGraded/Tensor/RestrictionComparisonNaturality.lean） -/

/-! # 固定左因子とのtensorの制限比較自然変換

## 概要
固定左因子とのtensorの制限比較自然変換。

## 方針
balanced tensor・全Hom自然性・作用の既存計算と普遍性を使い、条件を明示して比較する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。局所導来合成の計算部品、一般Morita・相対tensor・Hochschild型構成での作用と符号の比較に使える。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section RestrictionComparisonNaturality
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory MonoidalCategory Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

/-- 実際の閉零加群制限と固定左因子tensorに関する比較自然変換。 -/
def restrictionTensorComparison (N : LeftModule A E) :
    moduleRestriction A D E F.op ⋙ rightTensorFunctor A D (F.comp N) ⟶
      rightTensorFunctor A E N where
  app M := restrictionComparison A D E F (ForgetEnrichment.to (Complex A) M) N
  naturality {M M'} f := by
    apply hom_ext
    intro x
    have hD := ι_map A D ((moduleRestriction A D E F.op).map f)
      (𝟙 (ForgetEnrichment.of (Complex A) (F.comp N))) x
    have hE := ι_map A E f (𝟙 (ForgetEnrichment.of (Complex A) N)) (F.obj x)
    simp only [moduleRestriction_map_eval, CategoryTheory.Functor.map_id] at hD hE
    change ι A D (restrictModule A D E F.op (ForgetEnrichment.to (Complex A) M))
      (F.comp N) x ≫ map A D ((moduleRestriction A D E F.op).map f)
        (𝟙 (ForgetEnrichment.of (Complex A) (F.comp N))) ≫ _ = _
    calc
      _ = ((moduleEvaluation A E (F.obj x)).map f ⊗ₘ 𝟙 (N.obj (F.obj x))) ≫
          ι A D (restrictModule A D E F.op (ForgetEnrichment.to (Complex A) M'))
            (F.comp N) x ≫ restrictionComparison A D E F
              (ForgetEnrichment.to (Complex A) M') N :=
        (Category.assoc _ _ _).symm.trans
          ((congrArg (fun k => k ≫ restrictionComparison A D E F
            (ForgetEnrichment.to (Complex A) M') N) hD).trans (Category.assoc _ _ _))
      _ = ((moduleEvaluation A E (F.obj x)).map f ⊗ₘ 𝟙 (N.obj (F.obj x))) ≫
          ι A E (ForgetEnrichment.to (Complex A) M') N (F.obj x) := by
        rw [ι_restrictionComparison]
      _ = ι A E (ForgetEnrichment.to (Complex A) M) N (F.obj x) ≫
          map A E f (𝟙 (ForgetEnrichment.of (Complex A) N)) := hE.symm
      _ = _ := (ι_restrictionComparison_assoc A D E F
        (ForgetEnrichment.to (Complex A) M) N x _).symm

lemma restrictionTensorComparison_app (N : LeftModule A E) (M : ModuleCategory A E) :
    (restrictionTensorComparison A D E F N).app M =
      restrictionComparison A D E F (ForgetEnrichment.to (Complex A) M) N := rfl

end SerrePositivity.DifferentialGraded.BalancedTensor
end

end RestrictionComparisonNaturality
