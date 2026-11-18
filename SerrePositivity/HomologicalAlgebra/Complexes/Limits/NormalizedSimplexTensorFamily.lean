module

public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedSimplexTensorAugmentation

/-!
# 元の正規化単体テンソルの全関手族

概要：X⊗N(Δ•) と同じ augmentation を X に自然な全関手族へまとめる。
方針：元の curried tensor と二つの単位子の自然性を使う。
規約：全複体射・全単体作用素に自然である。
使われ方：元の cofibrant probe と標準 frame の全比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

def normalizedSimplexTensorFamily : Complex A ⥤ (SimplexCategory ⥤ Complex A) :=
  curriedTensor (Complex A) ⋙ (Functor.whiskeringLeft _ _ _).obj
    (SSet.stdSimplex ⋙ _root_.SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A)

def normalizedSimplexTensorFamilyAugmentation :
    _root_.SerrePositivity.ComplexLimits.normalizedSimplexTensorFamily A ⟶ Functor.const SimplexCategory where
  app X := _root_.SerrePositivity.ComplexLimits.normalizedSimplexTensorAugmentation A X
  naturality {X Y} f := by
    apply NatTrans.ext
    funext n
    change (f ▷ (_root_.SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).obj (SSet.stdSimplex.obj n)) ≫
      ((𝟙 Y ⊗ₘ (_root_.SerrePositivity.ComplexLimits.normalizedSimplexCochainContraction A n).hom) ≫ (ρ_ Y).hom) =
        ((𝟙 X ⊗ₘ (_root_.SerrePositivity.ComplexLimits.normalizedSimplexCochainContraction A n).hom) ≫ (ρ_ X).hom) ≫ f
    rw [id_tensorHom, id_tensorHom, ← Category.assoc, ← whisker_exchange,
      Category.assoc, rightUnitor_naturality, Category.assoc]

end SerrePositivity.ComplexLimits
