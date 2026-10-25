module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraConvolutionPrecompose

/-!
概要：実余モノイドの前合成を dg 畳み込み代数の射へ持ち上げる。
方針：閉構造の転置・評価と元の対角保存を用いる。
規約：元の複体上の内部 Hom 射を保持する。
使われ方：E2 が供給する AW 単体射の乗法的実現。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R]

lemma convolutionAdjunction_homEquiv (H : Comon (Complex R))
    (X Y : Complex R) (t : (convolutionTensor R H).obj X ⟶ Y) :
    (convolutionAdjunction R H).homEquiv X Y t = MonoidalClosed.curry (A := H.X) t := by
  rw [convolutionAdjunction, Adjunction.homEquiv_ofNatIsoLeft_apply]
  change (ihom.adjunction H.X).homEquiv X Y ((𝟙 _) ≫ t) = _
  rw [Category.id_comp]
  rfl

lemma convolutionAdjunction_counit (H : Comon (Complex R)) (B : Complex R) :
    (convolutionAdjunction R H).counit.app B = (ihom.ev H.X).app B := by
  change (convolutionTensorIso R H).inv.app _ ≫ (ihom.adjunction H.X).counit.app B = _
  change (𝟙 _) ≫ (ihom.ev H.X).app B = _
  exact Category.id_comp _

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
