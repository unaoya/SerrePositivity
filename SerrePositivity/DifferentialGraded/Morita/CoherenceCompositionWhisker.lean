module
public import SerrePositivity.DifferentialGraded.Morita.CoherenceComposition

/-! # 公開作用合成比較の片側自然性

## 概要
両kernelの全導来射に関する既存自然性を、片側のwhiskeringに読み替える。

## 方針
他方の射を恒等に特殊化し、主導来合成の同じ射を計算する。

## 規約と注意
既存の比較を変更しない。合成の始域の局所Hom K-flat性だけを保持する。

## 使われ方
U16aの結合図式でモデル計算の射を合成経路の末尾へ運ぶ。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory CategoryTheory.Functor BimoduleTensor
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
  (F : Type z) [DGCategory A F] [Small.{u} F]

/-- 最初のkernelの全導来射に関する作用合成比較のwhiskering自然性。 -/
lemma kernelCompositionIso_first_naturality (hD : localHomKFlat A D)
    {P P' : Kernel A D E} (f : P ⟶ P') (Q : Kernel A E F) :
    whiskerRight ((kernelDerivedTensorFunctor A D E).map f) (kernelDerivedTensor A E F Q) ≫
      (kernelCompositionIso A D E F hD P' Q).hom =
    (kernelCompositionIso A D E F hD P Q).hom ≫
      (kernelDerivedTensorFunctor A D F).map
        (((derivedBimoduleComposeFunctor A F E D hD).map f).app Q) := by
  have h := kernelCompositionIso_naturality A D E F hD f (𝟙 Q)
  simp only [kernelComposeMap, CategoryTheory.Functor.map_id] at h
  erw [Category.comp_id] at h
  apply NatTrans.ext
  funext X
  have hx := NatTrans.congr_app h X
  simp only [NatTrans.comp_app, NatTrans.hcomp_app, NatTrans.id_app, whiskerRight_app,
    Category.id_comp] at hx ⊢
  convert hx using 1
  rfl

/-- 後のkernelの全導来射に関する作用合成比較のwhiskering自然性。 -/
lemma kernelCompositionIso_second_naturality (hD : localHomKFlat A D)
    (P : Kernel A D E) {Q Q' : Kernel A E F} (g : Q ⟶ Q') :
    whiskerLeft (kernelDerivedTensor A D E P) ((kernelDerivedTensorFunctor A E F).map g) ≫
      (kernelCompositionIso A D E F hD P Q').hom =
    (kernelCompositionIso A D E F hD P Q).hom ≫
      (kernelDerivedTensorFunctor A D F).map
        (((derivedBimoduleComposeFunctor A F E D hD).obj P).map g) := by
  have h := kernelCompositionIso_naturality A D E F hD (𝟙 P) g
  simp only [kernelComposeMap, CategoryTheory.Functor.map_id, NatTrans.id_app] at h
  erw [Category.id_comp] at h
  apply NatTrans.ext
  funext X
  have hx := NatTrans.congr_app h X
  simp only [NatTrans.comp_app, NatTrans.hcomp_app, NatTrans.id_app, whiskerLeft_app,
    CategoryTheory.Functor.map_id, Category.comp_id] at hx ⊢
  convert hx using 1
  rfl

end SerrePositivity.DifferentialGraded.Morita
