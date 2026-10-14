module

public import SerrePositivity.Spectra.SymmetricSequence.FreeZeroConvolution

/-! # 生成次数零の単位対象の比較 -/

@[expose] public section

universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.SymmetricSequence

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C] [HasColimitsOfSize.{0, 0} C] [HasLimitsOfSize.{0, 0} C]

/-- 各段でテンソル単位を左にテンソルする関手の単位自然同型。 -/
def pointwiseTensorUnitNatIso : pointwiseTensorFunctor (𝟙_ C) ≅ 𝟭 (SymmetricSequence C) :=
  NatIso.ofComponents (fun F => NatIso.ofComponents (fun a => λ_ (F.obj a)) (by
    intro a b f
    exact leftUnitor_naturality (F.map f))) (by
    intro F G g
    apply NatTrans.ext
    funext a
    exact leftUnitor_naturality (g.app a))

omit [SymmetricCategory C] [MonoidalClosed C]
  [HasColimitsOfSize.{0, 0} C] [HasLimitsOfSize.{0, 0} C] in
/-- 各段の単位自然比較は通常の左単位同型。 -/
lemma pointwiseTensorUnitNatIso_app (F : SymmetricSequence C) (a : FiniteBijection) :
    ((pointwiseTensorUnitNatIso (C := C)).hom.app F).app a = (λ_ (F.obj a)).hom := rfl

/-- 第0段からテンソル単位を自由生成するとconvolutionの単位になる。 -/
def freeZeroUnitIso : (freeAt 0).obj (𝟙_ C) ≅ 𝟙_ (SymmetricSequence C) :=
  (ρ_ ((freeAt 0).obj (𝟙_ C))).symm ≪≫
    (freeZeroConvolutionNatIso (𝟙_ C)).app (𝟙_ (SymmetricSequence C)) ≪≫
      (pointwiseTensorUnitNatIso (C := C)).app (𝟙_ (SymmetricSequence C))

end SerrePositivity.SymmetricSequence
