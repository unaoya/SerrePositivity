module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletionMonoidal
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Restriction.Completion
public import SerrePositivity.HomologicalAlgebra.DerivedBaseChangeTensor
import SerrePositivity.HomologicalAlgebra.DerivedRestrictionConservative

/-!
# 完備導来底変換と完備化同値

## 概要
主元完備化で同型になる射は、導来底変換してから完備化しても同型になる。

## 方針
係数制限後の導来底変換を係数環との導来テンソルで読み、完備化同値とテンソルの両立を使う。

## 規約
上に有界な導来圏で扱う。環写像に平坦性は課さない。

## 使われ方
BS 著者版 Theorem 6.4 の分冪 de Rham の係数変更を未完備の有界模型で計算する。
-/

public noncomputable section

universe u

namespace SerrePositivity.DerivedCompletion

open CategoryTheory MonoidalCategory
attribute [local instance] HasDerivedCategory.standard

set_option backward.isDefEq.respectTransparency false

variable {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S) (a : R)

local notation "D" => DerivedCategory.Minus (ModuleCat R)

/-- 導来底変換の後の主元完備化は、もとの完備化同値を反転する。 -/
theorem completedBaseChange_map_isIso_of_completion {X Y : D} (f : X ⟶ Y)
    (hf : IsIso ((derivedComplexCompletionFunctor R a).map f.hom)) :
    IsIso ((derivedComplexCompletionFunctor S (φ a)).map
      ((boundedAboveDerivedBaseChange φ).map f).hom) := by
  let F := derivedComplexCompletionFunctor R a
  let Z := derivedBaseChangeScalarObject φ
  let g := (boundedAboveDerivedBaseChange φ).map f
  have hTensor : IsIso (F.map (Z ◁ f).hom) :=
    completionEquivalence_whiskerLeft R a f hf Z
  let e := Functor.isoWhiskerRight (boundedAboveDerivedBaseChangeTensorNatIso φ)
    (DerivedCategory.Minus.ι ⋙ F)
  have hRes : IsIso (F.map ((derivedRestrictScalars φ).map g.hom)) :=
    (NatIso.isIso_map_iff e f).mpr hTensor
  have h : IsIso ((derivedRestrictScalars φ).map
      ((derivedComplexCompletionFunctor S (φ a)).map g.hom)) :=
    (NatIso.isIso_map_iff (derivedRestrictionCompletionIso φ a) g.hom).mpr hRes
  exact isIso_of_reflects_iso _ (derivedRestrictScalars φ)

end SerrePositivity.DerivedCompletion
