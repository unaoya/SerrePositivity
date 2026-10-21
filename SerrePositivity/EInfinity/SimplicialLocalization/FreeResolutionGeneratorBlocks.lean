module

public import SerrePositivity.EInfinity.SimplicialLocalization.FreeResolutionGeneratorPartition
public import SerrePositivity.EInfinity.SimplicialLocalization.GeneratorBlockCategory
public import SerrePositivity.EInfinity.SimplicialLocalization.GeneratorBlockParts

/-!
# 元の自由解像の全次数の交互標準形

概要：元の各自由次数の射と圏を、指定・非指定の生成矢の交互標準形へ同定する。
方針：元の最外層の生成圏に正規化の全単射と圏同値を代入する。
規約：元の全対象・射列・合成・恒等文字を保持する。hammock の弱比較は後続。
使われ方：元の自由解像の各 hammock の行の分解。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.SimplicialLocalization
open CategoryTheory

def freeResolutionBlockEquiv (C : RelativeCategory.{u}) (n : SimplexCategoryᵒᵖ)
    (X Y : ((freeResolution C).obj n).category) :
    (X ⟶ Y) ≃ GeneratorBlocks.Normal (freeResolutionGeneratorBase C n).weakEquivalences X Y :=
  GeneratorBlocks.equivalence (freeResolutionGeneratorBase C n).weakEquivalences X Y

def freeResolutionBlockCategoryEquivalence (C : RelativeCategory.{u}) (n : SimplexCategoryᵒᵖ) :
    GeneratorBlocks.BlockCategory (freeResolutionGeneratorBase C n).weakEquivalences ≌
      ((freeResolution C).obj n).category :=
  GeneratorBlocks.categoryEquivalence (freeResolutionGeneratorBase C n).weakEquivalences

lemma freeResolutionBlockEquiv_symm_apply (C : RelativeCategory.{u}) (n : SimplexCategoryᵒᵖ)
    (X Y : ((freeResolution C).obj n).category)
    (N : GeneratorBlocks.Normal (freeResolutionGeneratorBase C n).weakEquivalences X Y) :
    (freeResolutionBlockEquiv C n X Y).symm N =
      GeneratorBlocks.flattenNormal (freeResolutionGeneratorBase C n).weakEquivalences N := rfl

lemma freeResolutionBlockEquiv_id (C : RelativeCategory.{u}) (n : SimplexCategoryᵒᵖ)
    (X : ((freeResolution C).obj n).category) :
    freeResolutionBlockEquiv C n X X (𝟙 X) =
      GeneratorBlocks.empty (freeResolutionGeneratorBase C n).weakEquivalences X := rfl

lemma freeResolutionBlockEquiv_comp (C : RelativeCategory.{u}) (n : SimplexCategoryᵒᵖ)
    {X Y Z : ((freeResolution C).obj n).category} (f : X ⟶ Y) (g : Y ⟶ Z) :
    freeResolutionBlockEquiv C n X Z (f ≫ g) =
      GeneratorBlocks.comp (freeResolutionGeneratorBase C n).weakEquivalences
        (freeResolutionBlockEquiv C n X Y f) (freeResolutionBlockEquiv C n Y Z g) :=
  GeneratorBlocks.normalize_comp (freeResolutionGeneratorBase C n).weakEquivalences f g

end SerrePositivity.EInfinity.SimplicialLocalization
