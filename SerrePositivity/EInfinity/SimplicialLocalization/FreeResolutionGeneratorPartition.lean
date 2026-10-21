module

public import SerrePositivity.EInfinity.SimplicialLocalization.FreeResolution
public import SerrePositivity.EInfinity.SimplicialLocalization.MarkedGeneratorCategory
public import SerrePositivity.EInfinity.SimplicialLocalization.GeneratorPartitionUniversal

/-!
# 元の自由解像の全次数の指定生成矢と自由積の普遍性

概要：指定生成矢の自由圏と二つの生成部分の普遍性を、元の自由解像の各次数へ代入する。
方針：最外層の自由相対圏の元の生成圏と W.paths をそのまま使う。
規約：零次と全単体次数を含み、恒等文字も保持する。高次比較の弱同値性は後続。
使われ方：Dwyer–Kan 比較補題2.3の各自由次数への適用。
-/

@[expose] public section
universe u u' v'
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.SimplicialLocalization
open CategoryTheory
open SerrePositivity.HomotopyFunctionComplex

def freeResolutionGeneratorBase (C : RelativeCategory.{u}) (n : SimplexCategoryᵒᵖ) :
    RelativeCategory.{u} := ComonadResolutionOperators.power freeRelativeComonad C n.unop.len

lemma freeResolution_eq_freeGeneratorBase (C : RelativeCategory.{u}) (n : SimplexCategoryᵒᵖ) :
    (freeResolution C).obj n = freeRelativeFunctor.obj (freeResolutionGeneratorBase C n) := rfl

def freeResolutionMarkedEquivalence (C : RelativeCategory.{u}) (n : SimplexCategoryᵒᵖ) :
    Paths (MarkedGenerators.quiver (freeResolutionGeneratorBase C n).weakEquivalences) ≌
      WideSubcategory ((freeResolution C).obj n).weakEquivalences :=
  MarkedGenerators.equivalence (freeResolutionGeneratorBase C n).weakEquivalences

lemma freeResolutionMarkedEquivalence_inclusion (C : RelativeCategory.{u})
    (n : SimplexCategoryᵒᵖ) :
    (freeResolutionMarkedEquivalence C n).functor ⋙
      wideSubcategoryInclusion ((freeResolution C).obj n).weakEquivalences =
        MarkedGenerators.inclusion (freeResolutionGeneratorBase C n).weakEquivalences := rfl

lemma freeResolution_existsUnique_extension (C : RelativeCategory.{u})
    (n : SimplexCategoryᵒᵖ) {D : Type u'} [Category.{v'} D]
    (F : Paths (MarkedGenerators.quiver (freeResolutionGeneratorBase C n).weakEquivalences) ⥤ D)
    (G : Paths (MarkedGenerators.quiver
      (GeneratorPartition.unmarked (freeResolutionGeneratorBase C n).weakEquivalences)) ⥤ D)
    (h : ∀ X : (freeResolutionGeneratorBase C n).category, F.obj X = G.obj X) :
    ∃! H : ((freeResolution C).obj n).category ⥤ D,
      MarkedGenerators.inclusion (freeResolutionGeneratorBase C n).weakEquivalences ⋙ H = F ∧
        MarkedGenerators.inclusion
          (GeneratorPartition.unmarked (freeResolutionGeneratorBase C n).weakEquivalences) ⋙ H =
            G :=
  GeneratorPartition.existsUnique_extension (freeResolutionGeneratorBase C n).weakEquivalences F G h

end SerrePositivity.EInfinity.SimplicialLocalization
