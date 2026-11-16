module

public import SerrePositivity.HomologicalAlgebra.UnboundedSemifreeModel
public import SerrePositivity.HomologicalAlgebra.RestrictedBaseChangeComplex
public import SerrePositivity.HomologicalAlgebra.CochainTensor.Cone
public import SerrePositivity.HomologicalAlgebra.CochainTensor.Symmetric
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ComplexCompletion.Basic

/-!
# 固定した係数分解で計算する非有界の底変換

## 概要
大きい環を元の環の加群として半自由分解し、固定した K-flat 複体とのテンソルを使う。

## 方針
実在する非有界半自由分解から係数模型を選ぶ。入力が K-flat なら通常の係数拡大を
係数制限したものへ標準の擬同型を作る。

## 規約
係数分解には大きい環の作用を仮定しない。全ての複体と比較射は元の環上である。

## 使われ方
BS 著者版 Lemma 4.22 の自然な Tot 比較の、元の係数環上の計算模型。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.DerivedCompletion

namespace SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal

variable {R S : Type u} [CommRing R] [CommRing S]

/-- S を R 加群として解消する実際の半自由係数模型。S の作用は要求しない。 -/
structure ScalarResolution (f : R →+* S) where
  complex : Complex R
  augmentation : complex ⟶ cochainSingleZero (baseChangeScalarModule f)
  quasiIso : QuasiIso augmentation
  semifree : SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree R complex
  kFlat : complexKFlat R complex

/-- 既存の非有界半自由分解から固定係数模型の存在が従う。 -/
theorem scalarResolution_nonempty (f : R →+* S) : Nonempty (ScalarResolution f) := by
  obtain ⟨P, q, hP, hq, _, hFlat, _⟩ := exists_unbounded_baseChange_model
    (RingHom.id R) (cochainSingleZero (baseChangeScalarModule f))
  exact ⟨⟨P, q, hq, hP, hFlat⟩⟩

/-- 固定係数模型を一度だけ選ぶ。存在を仮定しない。 -/
def scalarResolution (f : R →+* S) : ScalarResolution f :=
  Classical.choice (scalarResolution_nonempty f)

namespace ScalarResolution

variable {f : R →+* S} (L : ScalarResolution f)

/-- 同じ固定係数模型とのテンソル関手。入力ごとに分解を選び直さない。 -/
abbrev tensorFunctor : Complex R ⥤ Complex R := cochainTensorFixedLeft L.complex

/-- 固定係数模型は任意の非有界な入力の擬同型を保つ。 -/
theorem tensorFunctor_map_quasiIso {P Q : Complex R} (g : P ⟶ Q) [QuasiIso g] :
    QuasiIso (L.tensorFunctor.map g) :=
  complexKFlat_quasiIso_right R L.kFlat g

/-- 固定係数分解の増大写像による自然変換。 -/
def augmentationNat : L.tensorFunctor ⟶
    cochainTensorFixedLeft (cochainSingleZero (baseChangeScalarModule f)) where
  app P := cochainTensorMap L.augmentation (𝟙 P)
  naturality P Q g := by
    change cochainTensorMap (𝟙 L.complex) g ≫ cochainTensorMap L.augmentation (𝟙 Q) =
      cochainTensorMap L.augmentation (𝟙 P) ≫
        cochainTensorMap (𝟙 (cochainSingleZero (baseChangeScalarModule f))) g
    simp only [cochainTensorMap_comp, Category.id_comp, Category.comp_id]

/-- 係数制限した通常の底変換への、元の環上の標準比較射。 -/
def comparison (P : Complex R) :
    L.tensorFunctor.obj P ⟶
      ((ModuleCat.restrictScalars f).mapHomologicalComplex (.up ℤ)).obj (baseChange f P) :=
  L.augmentationNat.app P ≫ (restrictedBaseChangeComplexIso f P).inv

/-- 入力が K-flat なら、比較射は擬同型である。 -/
theorem comparison_quasiIso (P : Complex R) (hP : complexKFlat R P) :
    QuasiIso (L.comparison P) := by
  haveI : QuasiIso L.augmentation := L.quasiIso
  haveI : QuasiIso (cochainTensorMap L.augmentation (𝟙 P)) :=
    complexKFlat_quasiIso_left R hP L.augmentation
  change QuasiIso (cochainTensorMap L.augmentation (𝟙 P) ≫
    (restrictedBaseChangeComplexIso f P).inv)
  infer_instance

/-- 半自由入力に対しては、K-flat 性を別の仮定として要求しない。 -/
theorem comparison_quasiIso_of_semifree (P : Complex R)
    (hP : SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree R P) :
    QuasiIso (L.comparison P) :=
  L.comparison_quasiIso P (semifreeComplex_isKFlat hP)

/-- 同じ標準比較は入力の鎖写像について自然である。 -/
@[reassoc] theorem comparison_naturality {P Q : Complex R} (g : P ⟶ Q) :
    L.tensorFunctor.map g ≫ L.comparison Q =
      L.comparison P ≫ ((ModuleCat.restrictScalars f).mapHomologicalComplex (.up ℤ)).map
        (((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).map g) := by
  dsimp only [comparison]
  rw [← Category.assoc, L.augmentationNat.naturality]
  simp only [Category.assoc]
  congr 1
  apply (cancel_mono (restrictedBaseChangeComplexIso f Q).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [restrictedBaseChangeComplexIso_naturality]
  simp only [Iso.inv_hom_id_assoc]
  rfl

/-- 実際の主元完備化を施した、同じ R 線形の底変換模型。 -/
abbrev completedTensorFunctor (a : R) : Complex R ⥤ Complex R :=
  L.tensorFunctor ⋙ complexCompletionFunctor R a

/-- 固定係数模型と既存の完備化を組み合わせても擬同型を保つ。 -/
theorem completedTensorFunctor_map_quasiIso (a : R) {P Q : Complex R}
    (g : P ⟶ Q) [QuasiIso g] : QuasiIso ((L.completedTensorFunctor a).map g) := by
  haveI : QuasiIso (L.tensorFunctor.map g) := L.tensorFunctor_map_quasiIso g
  exact complexCompletionFunctor_map_quasiIso R a (L.tensorFunctor.map g)

end ScalarResolution
end SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal
