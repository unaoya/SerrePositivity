module
public import SerrePositivity.DifferentialGraded.Morita.CoherencePerfectUnit

/-! # 実際のPerf作用比較の結合coherence

## 概要
別担当の実際のPerf合成比較について、三kernelの結合図式を証明する。

## 方針
包含の忠実性で主導来射へ戻し、受入済みkernelCompositionIso_associatorを適用する。

## 規約と注意
合成kernelの列のperfect性は既存の定理から供給し、追加仮定として受け取らない。

## 使われ方
U16dのPerf作用coherenceへの接続。係数変更の残接続とは区別する。
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
  (P : Kernel A D E) (Q : Kernel A E F) (R : Kernel A F G)
  (hP : kernelColumnsPerfect A D E P) (hQ : kernelColumnsPerfect A E F Q)
  (hR : kernelColumnsPerfect A F G R)

/-- 既存の実際のPerf合成比較は、主導来kernel結合子と整合する。 -/
theorem perfectKernelCompositionIso_associator :
    let hPQ := kernelCompose_columnsPerfect_of_columns A D E F hD P Q hP hQ
    let hQR := kernelCompose_columnsPerfect_of_columns A E F G hE Q R hQ hR
    whiskerRight (perfectKernelCompositionIso A D E F hD P Q hP hQ).hom
        (perfectDerivedKernelAction A F G R hR) ≫
      (perfectKernelCompositionIso A D F G hD (kernelCompose A D E F hD P Q) R hPQ hR).hom =
    (Functor.associator (perfectDerivedKernelAction A D E P hP)
      (perfectDerivedKernelAction A E F Q hQ) (perfectDerivedKernelAction A F G R hR)).hom ≫
      whiskerLeft (perfectDerivedKernelAction A D E P hP)
        (perfectKernelCompositionIso A E F G hE Q R hQ hR).hom ≫
      (perfectKernelCompositionIso A D E G hD P (kernelCompose A E F G hE Q R) hP hQR).hom ≫
      perfectDerivedKernelMap A D G
        (kernelCompose_columnsPerfect_of_columns A D E G hD P (kernelCompose A E F G hE Q R) hP hQR)
        (kernelCompose_columnsPerfect_of_columns A D F G hD (kernelCompose A D E F hD P Q) R hPQ hR)
        (kernelAssociatorIso A D E F G hD hE P Q R).hom := by
  dsimp only
  apply NatTrans.ext
  funext X
  apply (modulePerfect A G).hom_ext
  have h := NatTrans.congr_app (kernelCompositionIso_associator A D E F G hD hE P Q R) X.obj
  dsimp only [kernelAssociatorLeftPath, kernelAssociatorRightPath] at h
  simp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app,
    Functor.associator_hom_app] at h
  erw [Category.id_comp] at h
  simp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app, Functor.associator_hom_app,
    perfectKernelCompositionIso, perfectDerivedKernelCompositionIso, perfectFunctorCompositionIso,
    perfectFunctorIso, Iso.trans_hom, NatIso.ofComponents, ObjectProperty.isoMk, Iso.refl_hom]
  change (kernelDerivedTensor A F G R).map
      (𝟙 _ ≫ (kernelCompositionIso A D E F hD P Q).hom.app X.obj) ≫
      (𝟙 _ ≫ (kernelCompositionIso A D F G hD
        (kernelCompose A D E F hD P Q) R).hom.app X.obj) =
    𝟙 _ ≫ (𝟙 _ ≫ (kernelCompositionIso A E F G hE Q R).hom.app
      ((kernelDerivedTensor A D E P).obj X.obj)) ≫
      (𝟙 _ ≫ (kernelCompositionIso A D E G hD P (kernelCompose A E F G hE Q R)).hom.app X.obj) ≫
      ((kernelDerivedTensorFunctor A D G).map
        (kernelAssociatorIso A D E F G hD hE P Q R).hom).app X.obj
  simpa only [Category.id_comp] using h

end SerrePositivity.DifferentialGraded.Morita
