module
public import SerrePositivity.DifferentialGraded.Resolution.Free.Composition
public import Mathlib.Data.ZMod.Basic

/-! # 自由dg圏構成に使う有限path・Hom直和・連結chain mapの監査 -/
@[expose] public section
noncomputable section
universe u v
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.FreeDGCategory
variable (A : Type u) [CommRing A] (D : Type v) [Small.{u} D]

example (K : ComplexQuiver A D) (hK : ∀ x y, complexKFlat A (K x y)) (x y : D) :
    complexKFlat A (homComplex A D K x y) := homComplex_kFlat A D K hK x y

example (K : ComplexQuiver A D) (x y : D) :
    (unitInclusion A D K x ▷ homComplex A D K x y) ≫ composition A D K x x y =
      (λ_ (homComplex A D K x y)).hom := composition_left_unit A D K x y

-- 二つの一辺pathは、接続頂点を内部に持つ二辺pathへ送られる。
example (K : ComplexQuiver A D) (x y z : D) :
    (edgeInclusion A D K x y ⊗ₘ edgeInclusion A D K y z) ≫ composition A D K x y z =
      pathInclusion A D K x z (.inr [y]) := by
  have h := composition_nonempty A D K x y z [] []
  exact h.trans (Category.id_comp _)

-- 恒等pathとxからxへの元の一辺pathは別添字である。
example (x : D) : (.inl ⟨rfl⟩ : PathIndex D x x) ≠ .inr [] := by
  intro h
  cases h

example (D : Type v) [Small.{0} D] (K : ComplexQuiver (ZMod 2) D)
    (hK : ∀ x y, complexKFlat (ZMod 2) (K x y)) (x y : D) :
    complexKFlat (ZMod 2) (homComplex (ZMod 2) D K x y) :=
  homComplex_kFlat (ZMod 2) D K hK x y

#print axioms SerrePositivity.DifferentialGraded.FreeDGCategory.ComplexQuiver
#print axioms SerrePositivity.DifferentialGraded.FreeDGCategory.wordTensor
#print axioms SerrePositivity.DifferentialGraded.FreeDGCategory.wordMap
#print axioms SerrePositivity.DifferentialGraded.FreeDGCategory.wordMap_id
#print axioms SerrePositivity.DifferentialGraded.FreeDGCategory.wordMap_comp
#print axioms SerrePositivity.DifferentialGraded.FreeDGCategory.wordTensor_kFlat
#print axioms SerrePositivity.DifferentialGraded.FreeDGCategory.concatenate
#print axioms SerrePositivity.DifferentialGraded.FreeDGCategory.wordConcatenationIso
#print axioms SerrePositivity.DifferentialGraded.FreeDGCategory.PathIndex
#print axioms SerrePositivity.DifferentialGraded.FreeDGCategory.pathTensor
#print axioms SerrePositivity.DifferentialGraded.FreeDGCategory.pathIndexSmall
#print axioms SerrePositivity.DifferentialGraded.FreeDGCategory.homComplex
#print axioms SerrePositivity.DifferentialGraded.FreeDGCategory.pathInclusion
#print axioms SerrePositivity.DifferentialGraded.FreeDGCategory.unitInclusion
#print axioms SerrePositivity.DifferentialGraded.FreeDGCategory.edgeInclusion
#print axioms SerrePositivity.DifferentialGraded.FreeDGCategory.homComplex_ext
#print axioms SerrePositivity.DifferentialGraded.FreeDGCategory.pathTensor_kFlat
#print axioms SerrePositivity.DifferentialGraded.FreeDGCategory.homComplex_kFlat
#print axioms SerrePositivity.DifferentialGraded.FreeDGCategory.pathMap
#print axioms SerrePositivity.DifferentialGraded.FreeDGCategory.homMap
#print axioms SerrePositivity.DifferentialGraded.FreeDGCategory.pathInclusion_homMap
#print axioms SerrePositivity.DifferentialGraded.FreeDGCategory.unitInclusion_homMap
#print axioms SerrePositivity.DifferentialGraded.FreeDGCategory.edgeInclusion_homMap
#print axioms SerrePositivity.DifferentialGraded.FreeDGCategory.pathMap_id
#print axioms SerrePositivity.DifferentialGraded.FreeDGCategory.pathMap_comp
#print axioms SerrePositivity.DifferentialGraded.FreeDGCategory.homMap_id
#print axioms SerrePositivity.DifferentialGraded.FreeDGCategory.homMap_comp
#print axioms SerrePositivity.DifferentialGraded.FreeDGCategory.pathComposition
#print axioms SerrePositivity.DifferentialGraded.FreeDGCategory.composition
#print axioms SerrePositivity.DifferentialGraded.FreeDGCategory.composition_pathInclusion
#print axioms SerrePositivity.DifferentialGraded.FreeDGCategory.composition_nonempty
#print axioms SerrePositivity.DifferentialGraded.FreeDGCategory.composition_unit_path
#print axioms SerrePositivity.DifferentialGraded.FreeDGCategory.composition_left_unit
