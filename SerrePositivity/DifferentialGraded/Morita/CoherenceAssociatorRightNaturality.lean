module
public import SerrePositivity.DifferentialGraded.Morita.CoherenceAssociatorNaturality

/-! # 公開結合図式の右経路の全導来射自然性

## 概要
公開右経路が最初の二kernelの全導来射に自然であることを証明する。

## 方針
関手結合子の成分を計算し、後二作用の比較・前作用の比較・kernel結合子の三squareを貼る。

## 規約と注意
代表のK-flat性や同型性を要求せず、任意の導来射で成立する。

## 使われ方
U16aの結合二経路の等式を指定K-flat代表から任意kernelへ移送する。
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

/-- 最初のkernelの全導来射に関する公開右経路の自然性。 -/
lemma kernelAssociatorRightPath_first_naturality {P P' : Kernel A D E} (f : P ⟶ P')
    (Q : Kernel A E F) (R : Kernel A F G) :
    whiskerRight (whiskerRight ((kernelDerivedTensorFunctor A D E).map f)
        (kernelDerivedTensor A E F Q)) (kernelDerivedTensor A F G R) ≫
      kernelAssociatorRightPath A D E F G hD hE P' Q R =
    kernelAssociatorRightPath A D E F G hD hE P Q R ≫
      (kernelDerivedTensorFunctor A D G).map
        (((derivedBimoduleComposeFunctor A G F D hD).map
          (((derivedBimoduleComposeFunctor A F E D hD).map f).app Q)).app R) := by
  apply NatTrans.ext
  funext X
  have hc := (kernelCompositionIso A E F G hE Q R).hom.naturality
    (((kernelDerivedTensorFunctor A D E).map f).app X)
  simp only [Functor.comp_map] at hc
  have hp := NatTrans.congr_app (kernelCompositionIso_first_naturality A D E G hD f
    (kernelCompose A E F G hE Q R)) X
  simp only [NatTrans.comp_app, whiskerRight_app] at hp
  have ha := congrArg (kernelDerivedTensorFunctor A D G).map
    (kernelAssociatorIso_first_naturality A D E F G hD hE f Q R)
  simp only [Functor.map_comp] at ha
  have hax := NatTrans.congr_app ha X
  simp only [NatTrans.comp_app] at hax
  dsimp only [kernelAssociatorRightPath]
  simp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app,
    Functor.associator_hom_app, Category.assoc]
  erw [Category.id_comp, Category.id_comp]
  slice_lhs 1 2 => erw [hc]
  slice_lhs 2 3 => erw [hp]
  slice_lhs 3 4 => erw [hax]
  rfl

/-- 二番目のkernelの全導来射に関する公開右経路の自然性。 -/
lemma kernelAssociatorRightPath_second_naturality (P : Kernel A D E)
    {Q Q' : Kernel A E F} (g : Q ⟶ Q') (R : Kernel A F G) :
    whiskerRight (whiskerLeft (kernelDerivedTensor A D E P)
        ((kernelDerivedTensorFunctor A E F).map g)) (kernelDerivedTensor A F G R) ≫
      kernelAssociatorRightPath A D E F G hD hE P Q' R =
    kernelAssociatorRightPath A D E F G hD hE P Q R ≫
      (kernelDerivedTensorFunctor A D G).map
        (((derivedBimoduleComposeFunctor A G F D hD).map
          (((derivedBimoduleComposeFunctor A F E D hD).obj P).map g)).app R) := by
  apply NatTrans.ext
  funext X
  have hc := NatTrans.congr_app (kernelCompositionIso_first_naturality A E F G hE g R)
    ((kernelDerivedTensor A D E P).obj X)
  simp only [NatTrans.comp_app, whiskerRight_app] at hc
  have hp := NatTrans.congr_app (kernelCompositionIso_second_naturality A D E G hD P
    (((derivedBimoduleComposeFunctor A G F E hE).map g).app R)) X
  simp only [NatTrans.comp_app, whiskerLeft_app] at hp
  have ha := congrArg (kernelDerivedTensorFunctor A D G).map
    (kernelAssociatorIso_second_naturality A D E F G hD hE P g R)
  simp only [Functor.map_comp] at ha
  have hax := NatTrans.congr_app ha X
  simp only [NatTrans.comp_app] at hax
  dsimp only [kernelAssociatorRightPath]
  simp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app,
    Functor.associator_hom_app, Category.assoc]
  erw [Category.id_comp, Category.id_comp]
  slice_lhs 1 2 => erw [hc]
  slice_lhs 2 3 => erw [hp]
  slice_lhs 3 4 => erw [hax]
  rfl

end SerrePositivity.DifferentialGraded.Morita
