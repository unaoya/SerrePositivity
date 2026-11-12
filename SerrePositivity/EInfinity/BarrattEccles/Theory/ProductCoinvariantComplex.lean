module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.ProductCoinvariants
public import SerrePositivity.EInfinity.BarrattEccles.Theory.CoinvariantTensorComplex

/-!
# 独立な群作用の余不変と複体のテンソル

HA 3.2.4.7 の自由比較のテンソル側で、直積群による余不変の分離を
両方の微分を持つ非有界複体へ延ばす。全複体の符号は元の標準のものを使う。
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity
open CategoryTheory MonoidalCategory HomologicalComplex
variable {A G H : Type u} [CommRing A] [Group G] [Group H]
  {K L : CochainComplex (ModuleCat.{u} A) ℤ} (ρ : G →* End K) (σ : H →* End L)

/-- 一つの群作用を持つ複体の、指定された余不変の複体。 -/
abbrev actionCoinvariantComplex :=
  ((Rep.coinvariantsFunctor A G).mapHomologicalComplex (.up ℤ)).obj
    (representationCochainComplex ρ)

/-- 各双次数の分離は、両方の微分を保つ二重複体の同型である。 -/
def productCoinvariantBicomplexIso :
    (((Rep.coinvariantsTensor A (G × H)).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj
      (representationCochainComplex (ρ.comp (MonoidHom.fst G H)))).obj
        (representationCochainComplex (σ.comp (MonoidHom.snd G H))) ≅
    (((MonoidalCategory.curriedTensor (ModuleCat A)).mapBifunctorHomologicalComplex
      (.up ℤ) (.up ℤ)).obj (actionCoinvariantComplex ρ)).obj (actionCoinvariantComplex σ) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => HomologicalComplex.Hom.isoOfComponents
      (fun j => productCoinvariantsIso ((representationCochainComplex ρ).X i)
        ((representationCochainComplex σ).X j)) (by
      intro j k hjk
      apply ModuleCat.hom_ext
      apply Representation.Coinvariants.hom_ext
      apply TensorProduct.ext
      apply LinearMap.ext
      intro v
      apply LinearMap.ext
      intro w
      rfl)) (by
    intro i j hij
    apply HomologicalComplex.Hom.ext
    funext k
    apply ModuleCat.hom_ext
    apply Representation.Coinvariants.hom_ext
    apply TensorProduct.ext
    apply LinearMap.ext
    intro v
    apply LinearMap.ext
    intro w
    rfl)

/-- 直積群の余不変の分離を、直和全複体の同型へ移す。 -/
def productCoinvariantTotalIso :
    coinvariantTensorTotal (ρ.comp (MonoidHom.fst G H)) (σ.comp (MonoidHom.snd G H)) ≅
      actionCoinvariantComplex ρ ⊗ actionCoinvariantComplex σ :=
  HomologicalComplex₂.total.mapIso (productCoinvariantBicomplexIso ρ σ) (.up ℤ)

/-- 実際のテンソル複体の直積群の余不変は、左右の余不変の複体のテンソルである。 -/
def productCoinvariantComplexIso :
    tensorCoinvariantComplex (ρ.comp (MonoidHom.fst G H)) (σ.comp (MonoidHom.snd G H)) ≅
      actionCoinvariantComplex ρ ⊗ actionCoinvariantComplex σ :=
  (coinvariantTensorTotalIso (ρ.comp (MonoidHom.fst G H))
    (σ.comp (MonoidHom.snd G H))).symm ≪≫ productCoinvariantTotalIso ρ σ

end SerrePositivity.EInfinity
