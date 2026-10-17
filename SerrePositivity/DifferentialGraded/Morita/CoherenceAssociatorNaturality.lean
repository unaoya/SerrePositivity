module
public import SerrePositivity.DifferentialGraded.Morita.CoherenceAssociatorPaths

/-! # kernel結合子と公開左経路の全導来射自然性

## 概要
最初の二kernelの射について、主導来kernel結合子と公開左経路の自然性を証明する。

## 方針
既存のcurried結合自然同型を評価し、合成比較の片側自然性を順に適用する。

## 規約と注意
射は主導来kernel圏の任意射。代表のK-flat性を仮定しない。

## 使われ方
U16aの結合coherenceをK-flat代表の同型に沿って任意kernelへ移す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z t
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory CategoryTheory.Functor BimoduleTensor
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
  (F : Type z) [DGCategory A F] [Small.{u} F]
  (G : Type t) [DGCategory A G] [Small.{u} G]
  (hD : localHomKFlat A D) (hE : localHomKFlat A E)

/-- 最初のkernelの任意導来射に関する主導来kernel結合子の自然性。 -/
lemma kernelAssociatorIso_first_naturality {P P' : Kernel A D E} (f : P ⟶ P')
    (Q : Kernel A E F) (R : Kernel A F G) :
    (((derivedBimoduleComposeFunctor A G E D hD).map f).app
        (kernelCompose A E F G hE Q R)) ≫
      (kernelAssociatorIso A D E F G hD hE P' Q R).hom =
    (kernelAssociatorIso A D E F G hD hE P Q R).hom ≫
      (((derivedBimoduleComposeFunctor A G F D hD).map
        (((derivedBimoduleComposeFunctor A F E D hD).map f).app Q)).app R) := by
  have h := NatTrans.congr_app (NatTrans.congr_app
    ((derivedBimoduleAssociatorIso A G F E D hE hD).hom.naturality f) Q) R
  exact h

/-- 二番目のkernelの任意導来射に関する主導来kernel結合子の自然性。 -/
lemma kernelAssociatorIso_second_naturality (P : Kernel A D E)
    {Q Q' : Kernel A E F} (g : Q ⟶ Q') (R : Kernel A F G) :
    ((derivedBimoduleComposeFunctor A G E D hD).obj P).map
        (((derivedBimoduleComposeFunctor A G F E hE).map g).app R) ≫
      (kernelAssociatorIso A D E F G hD hE P Q' R).hom =
    (kernelAssociatorIso A D E F G hD hE P Q R).hom ≫
      (((derivedBimoduleComposeFunctor A G F D hD).map
        (((derivedBimoduleComposeFunctor A F E D hD).obj P).map g)).app R) := by
  have h := NatTrans.congr_app
    (((derivedBimoduleAssociatorIso A G F E D hE hD).hom.app P).naturality g) R
  exact h

/-- 最初のkernelの射について公開左経路は自然。 -/
lemma kernelAssociatorLeftPath_first_naturality {P P' : Kernel A D E} (f : P ⟶ P')
    (Q : Kernel A E F) (R : Kernel A F G) :
    whiskerRight (whiskerRight ((kernelDerivedTensorFunctor A D E).map f)
        (kernelDerivedTensor A E F Q)) (kernelDerivedTensor A F G R) ≫
      kernelAssociatorLeftPath A D E F G hD P' Q R =
    kernelAssociatorLeftPath A D E F G hD P Q R ≫
      (kernelDerivedTensorFunctor A D G).map
        (((derivedBimoduleComposeFunctor A G F D hD).map
          (((derivedBimoduleComposeFunctor A F E D hD).map f).app Q)).app R) := by
  dsimp only [kernelAssociatorLeftPath]
  slice_lhs 1 2 => rw [← whiskerRight_comp, kernelCompositionIso_first_naturality]
  rw [whiskerRight_comp]
  simp only [Category.assoc]
  slice_lhs 2 3 => erw [kernelCompositionIso_first_naturality A D F G hD
    (((derivedBimoduleComposeFunctor A F E D hD).map f).app Q) R]
  rfl

/-- 二番目のkernelの射について公開左経路は自然。 -/
lemma kernelAssociatorLeftPath_second_naturality (P : Kernel A D E)
    {Q Q' : Kernel A E F} (g : Q ⟶ Q') (R : Kernel A F G) :
    whiskerRight (whiskerLeft (kernelDerivedTensor A D E P)
        ((kernelDerivedTensorFunctor A E F).map g)) (kernelDerivedTensor A F G R) ≫
      kernelAssociatorLeftPath A D E F G hD P Q' R =
    kernelAssociatorLeftPath A D E F G hD P Q R ≫
      (kernelDerivedTensorFunctor A D G).map
        (((derivedBimoduleComposeFunctor A G F D hD).map
          (((derivedBimoduleComposeFunctor A F E D hD).obj P).map g)).app R) := by
  dsimp only [kernelAssociatorLeftPath]
  slice_lhs 1 2 => rw [← whiskerRight_comp, kernelCompositionIso_second_naturality]
  rw [whiskerRight_comp]
  simp only [Category.assoc]
  slice_lhs 2 3 => erw [kernelCompositionIso_first_naturality A D F G hD
    (((derivedBimoduleComposeFunctor A F E D hD).obj P).map g) R]
  rfl

end SerrePositivity.DifferentialGraded.Morita
