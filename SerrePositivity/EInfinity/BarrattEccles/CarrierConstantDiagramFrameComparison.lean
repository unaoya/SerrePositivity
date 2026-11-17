module

public import SerrePositivity.EInfinity.BarrattEccles.CarrierConstantDiagramFrame

/-!
# 定値図式の標準 frame の元の図式への弱い augmentation

概要：BM 命題 4.1・Hovey §5.4 の図式 frame を元の定値図式へ全次元で比較する。
方針：標準単体の零単体への縮退、零次同型、定値図式置換の比較を合成する。
規約：比較は各次元で弱同値だが Reedy 自明 fibration とは主張しない。
使われ方：図式の選んだ resolution と構成した frame の比較。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles.CarrierDiagram

open CategoryTheory Limits _root_.HomotopicalAlgebra
open SerrePositivity.DifferentialGraded
open SerrePositivity.HomotopyFunctionComplex

variable (A : Type u) [CommRing A] (K : Type u) [SmallCategory K]

local instance : HasColimitsOfSize.{u, u} (Complex A) := ⟨fun _ _ => inferInstance⟩

local instance : HasColimitsOfSize.{0, u} (Complex A) :=
  hasColimitsOfSizeShrink.{0, u} _

/-- 概要：構成した図式 frame から元の定値図式への augmentation（Hovey §5.4）。
方針：零単体へ縮退してから、同じ置換図式の比較へ続ける。
規約：すべての単体作用素に厳密に自然。
使われ方：実際の図式 frame と元の定値図式の Hom 比較。 -/
def constantDiagramFrameComparison (Y : (Complex A)) :
    constantDiagramFrame A K Y ⟶
      (Functor.const SimplexCategory).obj ((Functor.const K).obj Y) where
  app n := (constantDiagramFrame A K Y).map (QuillenStandardFrame.collapse n) ≫
    (constantDiagramFrameZeroIso A K Y).hom ≫ (constantDiagramComparison A K).app Y
  naturality n m f := by
    have hc : f ≫ QuillenStandardFrame.collapse m = QuillenStandardFrame.collapse n :=
      SimplexCategory.isTerminalZero.hom_ext _ _
    change (constantDiagramFrame A K Y).map f ≫
        ((constantDiagramFrame A K Y).map (QuillenStandardFrame.collapse m) ≫ _) =
      _ ≫ 𝟙 _
    rw [Category.comp_id, ← Category.assoc, ← Functor.map_comp, hc]

/-- 概要：図式 frame の零次比較は既存の二つの比較の合成（Hovey §5.4）。
方針：零単体の自己縮退が恒等射であることを使う。
規約：零次同型と元の定値図式比較は選び直さない。
使われ方：π₀ 比較と元の図式射の類の計算。 -/
lemma constantDiagramFrameComparison_zero (Y : (Complex A)) :
    (constantDiagramFrameComparison A K Y).app (SimplexCategory.mk 0) =
      (constantDiagramFrameZeroIso A K Y).hom ≫ (constantDiagramComparison A K).app Y := by
  change (constantDiagramFrame A K Y).map _ ≫ _ = _
  rw [show QuillenStandardFrame.collapse (SimplexCategory.mk 0) = 𝟙 _ from
    Subsingleton.elim _ _, (constantDiagramFrame A K Y).map_id, Category.id_comp]

/-- 概要：図式 frame の augmentation は全次元で図式の弱同値（Hovey §5.4）。
方針：frame の homotopical constancy、零次同型、置換の弱同値を合成する。
規約：具体的な射影図式モデルを局所的に使う。
使われ方：元の定値図式の任意の選んだ resolution との比較。 -/
lemma constantDiagramFrameComparison_weakEquivalence (Y : (Complex A))
    (n : SimplexCategory) :
    let := projectiveModelCategory A K
    weakEquivalences (K ⥤ (Complex A)) ((constantDiagramFrameComparison A K Y).app n) := by
  let := projectiveModelCategory A K
  have hz : weakEquivalences (K ⥤ (Complex A))
      (constantDiagramFrameZeroIso A K Y).hom :=
    (weakEquivalences _).of_isIso (constantDiagramFrameZeroIso A K Y).hom
  exact (weakEquivalences _).comp_mem _ _
    (constantDiagramFrame_homotopicallyConstant A K Y (QuillenStandardFrame.collapse n))
    ((weakEquivalences _).comp_mem _ _ hz (constantDiagramComparison_weakEquivalence A K Y).mem)

/-- 概要：図式 frame の零次同型は始域複体の射に自然（Hovey §5.4）。
方針：零単体の重み同型に対する実現族の自然性を使う。
規約：構成済みの置換関手の同じ射を使う。
使われ方：図式 frame の augmentation を始域の族で束ねる。 -/
lemma constantDiagramFrameZeroIso_naturality {Y Z : (Complex A)} (f : Y ⟶ Z) :
    ((constantDiagramFrameFamily A K).map f).app (SimplexCategory.mk 0) ≫
        (constantDiagramFrameZeroIso A K Z).hom =
      (constantDiagramFrameZeroIso A K Y).hom ≫ (constantDiagramReplacement A K).map f := by
  let := SerrePositivity.EInfinity.projectiveModelCategory A
  let q := Reedy.cosimplicialResolutionFamily (carrierProbeFactorization A)
  apply NatTrans.ext
  funext k
  exact ((Realization.family.map (q.obj.map f)).naturality
    ((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.zeroTensorWeightIso K (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight K)).hom.app k)).symm

/-- 概要：元の定値図式への全次元の比較は始域複体にも自然（Hovey §5.4）。
方針：frame の縮退の自然性、零次同型の自然性、置換比較の自然性を合成する。
規約：元の複体・図式のすべての射に厳密に自然。
使われ方：任意の選んだ図式 resolution と frame を自然に比較する。 -/
def constantDiagramFrameAugmentation : constantDiagramFrameFamily A K ⟶
    (Functor.const K : (Complex A) ⥤ _) ⋙ Functor.const SimplexCategory where
  app := constantDiagramFrameComparison A K
  naturality Y Z f := by
    apply NatTrans.ext
    funext n
    change ((constantDiagramFrameFamily A K).map f).app n ≫
        ((constantDiagramFrame A K Z).map (QuillenStandardFrame.collapse n) ≫
          (constantDiagramFrameZeroIso A K Z).hom ≫ (constantDiagramComparison A K).app Z) =
      ((constantDiagramFrame A K Y).map (QuillenStandardFrame.collapse n) ≫
        (constantDiagramFrameZeroIso A K Y).hom ≫ (constantDiagramComparison A K).app Y) ≫
          (Functor.const K).map f
    have hn : ((constantDiagramFrameFamily A K).map f).app n ≫
        (constantDiagramFrame A K Z).map (QuillenStandardFrame.collapse n) =
      (constantDiagramFrame A K Y).map (QuillenStandardFrame.collapse n) ≫
        ((constantDiagramFrameFamily A K).map f).app (SimplexCategory.mk 0) :=
      (((constantDiagramFrameFamily A K).map f).naturality (QuillenStandardFrame.collapse n)).symm
    rw [← Category.assoc, ← Category.assoc, hn]
    simp only [Category.assoc]
    rw [← Category.assoc (((constantDiagramFrameFamily A K).map f).app (SimplexCategory.mk 0))
      (constantDiagramFrameZeroIso A K Z).hom ((constantDiagramComparison A K).app Z),
      constantDiagramFrameZeroIso_naturality]
    simp only [Category.assoc]
    rw [(constantDiagramComparison A K).naturality f]

end SerrePositivity.EInfinity.BarrattEccles.CarrierDiagram
