module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletedBaseChangeEquivalence
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletionReflection

/-!
# 自由模型で計算する完備導来底変換

## 概要
有界な射影模型から完備化同値で移った対象の完備導来底変換を計算する。

## 方針
元の射影模型で導来底変換を計算し、完備化同値を両側で反転する。

## 規約
底変換前の複体は上に有界。底変換後に与える複体は導来完備とする。

## 使われ方
BS 著者版 Theorem 6.4 の有限な分冪 de Rham 列の係数変更。
-/

public noncomputable section

open CategoryTheory

universe u

namespace SerrePositivity.DerivedCompletion

attribute [local instance] HasDerivedCategory.standard

set_option backward.isDefEq.respectTransparency false

variable {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) (a : A)

local notation "D" => DerivedCategory.Minus (ModuleCat A)
local notation "F" => derivedComplexCompletionFunctor B (φ a)
local notation "L" => boundedAboveDerivedBaseChange φ

/-- 導来底変換後の完備化を、射影模型の古典的底変換から来る完備複体で計算する。 -/
def completedBaseChangeModelIso {X Y : D} (f : X ⟶ Y)
    (hf : IsIso ((derivedComplexCompletionFunctor A a).map f.hom))
    (P : BoundedAboveDerivedModel X.obj) {T : CochainComplex (ModuleCat.{u} B) ℤ}
    (g : baseChange φ P.complex ⟶ T)
    (hg : IsIso ((F).map (DerivedCategory.Q.map g)))
    (hT : IsComplete B (φ a) (DerivedCategory.Q.obj T)) :
    (F).obj ((L).obj Y).obj ≅ DerivedCategory.Q.obj T := by
  let f' := (F).map ((L).map f).hom
  have : IsIso f' := completedBaseChange_map_isIso_of_completion φ a f hf
  have := hg
  have := derivedComplexCompletionUnit_isIso_of_isComplete B (φ a) (DerivedCategory.Q.obj T) hT
  exact (asIso f').symm ≪≫ (F).mapIso (boundedAboveDerivedBaseChangeModelIso φ X P) ≪≫
    asIso ((F).map (DerivedCategory.Q.map g)) ≪≫
    (asIso ((derivedComplexCompletionUnit B (φ a)).app (DerivedCategory.Q.obj T))).symm

/-- 模型同型は、もとの模型から来る余鎖写像の完備化と可換。 -/
theorem completedBaseChangeModelIso_hom_comm {X Y : D} (f : X ⟶ Y)
    (hf : IsIso ((derivedComplexCompletionFunctor A a).map f.hom))
    (P : BoundedAboveDerivedModel X.obj) {T : CochainComplex (ModuleCat.{u} B) ℤ}
    (g : baseChange φ P.complex ⟶ T)
    (hg : IsIso ((F).map (DerivedCategory.Q.map g)))
    (hT : IsComplete B (φ a) (DerivedCategory.Q.obj T)) :
    (F).map ((L).map f).hom ≫ (completedBaseChangeModelIso φ a f hf P g hg hT).hom ≫
      (derivedComplexCompletionUnit B (φ a)).app (DerivedCategory.Q.obj T) =
    (F).map ((boundedAboveDerivedBaseChangeModelIso φ X P).hom ≫ DerivedCategory.Q.map g) := by
  have := completedBaseChange_map_isIso_of_completion φ a f hf
  have := hg
  have := derivedComplexCompletionUnit_isIso_of_isComplete B (φ a) (DerivedCategory.Q.obj T) hT
  simp [completedBaseChangeModelIso, Functor.map_comp]

end SerrePositivity.DerivedCompletion
