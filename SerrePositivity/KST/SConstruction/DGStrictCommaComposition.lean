module
public import SerrePositivity.KST.SConstruction.DGStrictCommaUnit
public import SerrePositivity.KST.SConstruction.DGStrictCommaTensorZero

/-! # 閉比較族の実 comma Hom 作用の合成保存
概要：比較 cochain 零の実 Hom 作用が全次数の豊穣合成を厳密に保存する。
方針：両実射影では元の関手法則、比較では左右 tensor の零性を使う。
規約：全 Hom tensor からの鎖写像を判定。使われ方：標準 dg 対角関手の構成。
-/
@[expose] public section
noncomputable section
universe u v w t
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory CochainComplex HomComplex
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable {R : Type u} [CommRing R] {C : Type v} [DGCategory R C]
  {E : Type w} [DGCategory R E] {F : DGFunctor R C E}
  {P : Type t} [DGCategory R P]
namespace DGStrictCommaFamily
variable (d : DGStrictCommaFamily R C E F P)

/-- 同じ全 Hom tensor は、実合成の第一比較項を消す。 -/
lemma homMap_firstPrimitive (x y z : P) :
    (Cochain.ofHom (d.homMap x y ⊗ₘ d.homMap y z)).comp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaFirstCompositePrimitive R C E F (d.obj x) (d.obj y) (d.obj z))
      (zero_add (-1)) = 0 :=
  dgStrictCommaTensorRight_zero (-1) (d.homMap x y) (d.homMap y z)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R C E F (d.obj x) (d.obj y))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaFirstCompositionMap R C E F (d.obj x) (d.obj y) (d.obj z))
    (d.homMap_comparison x y)

/-- 同じ全 Hom tensor は、実合成の第二比較項も消す。 -/
lemma homMap_secondPrimitive (x y z : P) :
    (Cochain.ofHom (d.homMap x y ⊗ₘ d.homMap y z)).comp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSecondCompositePrimitive R C E F (d.obj x) (d.obj y) (d.obj z))
      (zero_add (-1)) = 0 :=
  dgStrictCommaTensorLeft_zero (-1) (d.homMap x y) (d.homMap y z)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R C E F (d.obj y) (d.obj z))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSecondCompositionMap R C E F (d.obj x) (d.obj y) (d.obj z))
    (d.homMap_comparison y z)

/-- 元の二関手の全次数合成を、同じ実 comma 合成へ厳密に送る。 -/
lemma homMap_comp (x y z : P) :
    eComp (Complex R) x y z ≫ d.homMap x z =
      (d.homMap x y ⊗ₘ d.homMap y z) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaComposition R C E F (d.obj x) (d.obj y) (d.obj z) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHom_ext R C E F (d.obj x) (d.obj z)
  · rw [Category.assoc, d.homMap_source, Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaComposition_source]
    dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSourceComposite]
    rw [← Category.assoc, tensorHom_comp_tensorHom, d.homMap_source, d.homMap_source]
    exact d.source.map_comp x y z
  · rw [Category.assoc, d.homMap_replacement, Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaComposition_replacement]
    dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacementComposite]
    rw [← Category.assoc, tensorHom_comp_tensorHom,
      d.homMap_replacement, d.homMap_replacement]
    exact d.replacement.map_comp x y z
  · rw [dgStrictCommaComparison_precompose, d.homMap_comparison, Cochain.comp_zero,
      dgStrictCommaComparison_precompose, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaComposition_comparison]
    dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaCompositePrimitive]
    rw [Cochain.comp_add, d.homMap_firstPrimitive, d.homMap_secondPrimitive, add_zero]

end DGStrictCommaFamily
end SerrePositivity.KST.SConstruction
