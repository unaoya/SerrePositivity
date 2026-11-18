module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.FreeProductAWRightAugmentation
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.ProductFrameCoaction
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.TensorFrameCoaction
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StandardParameterAugmentation

/-!
概要：指定パラメータ余作用と同じ増大写像の単位則。
方針：各余単体・各図式対象で、指定 AW と零次増大写像の成分を計算する。
規約：余作用・増大写像を取り替えず、恒等射との厳密な等式を目標とする。
使われ方：HA 1.2.4、IS-W2 §73 A05。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open AlgebraicTopology AlgebraicTopology.DoldKan HomologicalComplex
open _root_.SerrePositivity.ComplexLimits
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (A : Type u) [CommRing A] {J : Type v} [Category.{w} J]
variable (W : J ⥤ SSet.{u}) (φ : simplicialRingCoefficient.{u} →+* A)
local notation "P" => standardParameterForCoefficients A J
local notation "F" => freeProductFrame A W P

/-- 指定積余作用と指定増大写像の右単位則。 -/
theorem productFrameCoaction_counit :
    productFrameCoaction A W φ ≫ (𝟙 F ⊗ₘ standardParameterAugmentation A J) ≫
      (ρ_ F).hom = 𝟙 F := by
  apply NatTrans.ext
  funext n
  apply NatTrans.ext
  funext j
  change
    (freeNegativeChainsMap (A := A)
      (lift (𝟙 ((W.obj j) ⊗ ((P).obj n).obj j))
        (snd (W.obj j) (((P).obj n).obj j))) ≫
      freeProductAlexanderWhitney φ ((W.obj j) ⊗ ((P).obj n).obj j)
        (((P).obj n).obj j)) ≫
      (𝟙 _ ⊗ₘ (_root_.SerrePositivity.ComplexLimits.normalizedSimplexCochainContraction A n).hom) ≫
        (ρ_ _).hom = 𝟙 _

  simp only [Category.assoc]
  erw [freeProductAlexanderWhitney_right_augmentation A φ
    ((W.obj j) ⊗ ((P).obj n).obj j) n]
  simp only [freeNegativeChainsMap, ← extendMap_comp, ← Functor.map_comp,
    ← Functor.whiskerRight_comp]
  erw [lift_fst, Functor.whiskerRight_id', CategoryTheory.Functor.map_id, extendMap_id]

/-- 指定テンソル余作用と指定増大写像の右単位則。 -/
theorem tensorFrameCoaction_counit :
    tensorFrameCoaction A W φ ≫
      (𝟙 (freeTensorFrame A W P) ⊗ₘ standardParameterAugmentation A J) ≫
      (ρ_ (freeTensorFrame A W P)).hom = 𝟙 _ := by
  apply NatTrans.ext
  funext n
  apply NatTrans.ext
  funext j
  let Y := ((P).obj n).obj j
  let B := freeNegativeChains (A := A) (W.obj j)
  let C := freeNegativeChains (A := A) Y
  let ε : C ⟶ 𝟙_ (CochainComplex (ModuleCat A) ℤ) :=
    (_root_.SerrePositivity.ComplexLimits.normalizedSimplexCochainContraction A n).hom
  let δ : C ⟶ C ⊗ C := freeNegativeChainsMap (A := A) (lift (𝟙 Y) (𝟙 Y)) ≫
    freeProductAlexanderWhitney φ Y Y
  have hd : δ ≫ (𝟙 C ⊗ₘ ε) ≫ (ρ_ C).hom = 𝟙 C := by
    dsimp only [δ]
    simp only [Category.assoc]
    erw [freeProductAlexanderWhitney_right_augmentation A φ Y n]
    simp only [freeNegativeChainsMap, ← extendMap_comp, ← Functor.map_comp,
      ← Functor.whiskerRight_comp]
    erw [lift_fst, Functor.whiskerRight_id', CategoryTheory.Functor.map_id, extendMap_id]
  simp only [id_tensorHom] at hd
  change (B ◁ δ) ≫ (α_ B C C).inv ≫
    (𝟙 (B ⊗ C) ⊗ₘ ε) ≫ (ρ_ (B ⊗ C)).hom = 𝟙 _
  simp only [id_tensorHom, rightUnitor_tensor_hom]
  rw [← tensor_whiskerLeft_symm_assoc]
  rw [← whiskerLeft_comp, ← whiskerLeft_comp, hd, whiskerLeft_id]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
