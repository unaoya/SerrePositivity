module

public import SerrePositivity.Spectra.SymmetricSequence.FreeZeroUnitGenerators
public import SerrePositivity.CategoryTheory.Monoidal.FreeModuleMonoidal

/-! # 自由零生成の単位比較を係数加群へ移す -/

@[expose] public section

universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.SymmetricSequence

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped CategoryTheory.MonObj

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C] [HasColimitsOfSize.{0, 0} C] [HasLimitsOfSize.{0, 0} C]
  (M : SymmetricSequence C) [MonObj M]

/-- 第0段から単位を自由生成した係数加群と正則係数加群の比較。 -/
def freeZeroModuleUnitIso :
    MonoidalFreeModule.freeObj M ((freeAt 0).obj (𝟙_ C)) ≅ Mod.regular M :=
  (MonoidalFreeModule.freeFunctor M).mapIso (freeZeroUnitIso (C := C)) ≪≫
    MonoidalBalancedTensor.freeUnitIso M

/-- 加群の単位比較は、基礎対称列の生成元を係数の単位へ送る。 -/
@[reassoc]
lemma freeZeroModuleUnitIso_generator :
    MonoidalFreeModule.generator M ((freeAt 0).obj (𝟙_ C)) ≫
        (freeZeroModuleUnitIso M).hom.hom = (freeZeroUnitIso (C := C)).hom ≫ η[M] := by
  unfold freeZeroModuleUnitIso
  simp only [Iso.trans_hom, Mod.comp_hom']
  change MonoidalFreeModule.generator M ((freeAt 0).obj (𝟙_ C)) ≫
    (MonoidalFreeModule.freeMap M (freeZeroUnitIso (C := C)).hom).hom ≫
      (MonoidalBalancedTensor.freeUnitIso M).hom.hom = _
  rw [MonoidalBalancedTensor.generator_freeMap_assoc,
    MonoidalBalancedTensor.generator_freeUnit]

/-- 第0段の生成元を単位比較へ送ると、係数の単位の標準射になる。 -/
@[reassoc]
lemma freeZeroModuleUnitIso_generator_level :
    freeAtGenerator 0 (𝟙_ C) ≫
        (MonoidalFreeModule.generator M ((freeAt 0).obj (𝟙_ C))).app (FiniteBijection.of 0) ≫
          (freeZeroModuleUnitIso M).hom.hom.app (FiniteBijection.of 0) =
      convolutionUnitCan.app ⟨⟨⟩⟩ ≫ η[M].app (FiniteBijection.of 0) := by
  have h := congrArg (fun g => freeAtGenerator 0 (𝟙_ C) ≫ g.app (FiniteBijection.of 0))
    (freeZeroModuleUnitIso_generator M)
  change freeAtGenerator 0 (𝟙_ C) ≫
    (MonoidalFreeModule.generator M ((freeAt 0).obj (𝟙_ C))).app (FiniteBijection.of 0) ≫
      (freeZeroModuleUnitIso M).hom.hom.app (FiniteBijection.of 0) =
    freeAtGenerator 0 (𝟙_ C) ≫ (freeZeroUnitIso (C := C)).hom.app (FiniteBijection.of 0) ≫
      η[M].app (FiniteBijection.of 0) at h
  have hu := congrArg (fun g => g ≫ η[M].app (FiniteBijection.of 0))
    (freeZeroUnitIso_generator_hom (C := C))
  simp only [Category.assoc] at hu
  exact h.trans hu

/-- 与えた第0段の生成射を単位比較へ送ると係数の単位になるという法則。 -/
def freeZeroModuleUnitGeneratorLaw
    (i : 𝟙_ C ⟶ (MonoidalFreeModule.freeObj M ((freeAt 0).obj (𝟙_ C))).X.obj
      (FiniteBijection.of 0)) : Prop :=
  i ≫ (freeZeroModuleUnitIso M).hom.hom.app (FiniteBijection.of 0) =
    convolutionUnitCan.app ⟨⟨⟩⟩ ≫ η[M].app (FiniteBijection.of 0)

/-- 自由加群の二段の生成元の公式から、単位比較の生成元の法則を得る。 -/
lemma freeZeroModuleUnitGenerator_law
    (i : 𝟙_ C ⟶ (MonoidalFreeModule.freeObj M ((freeAt 0).obj (𝟙_ C))).X.obj
      (FiniteBijection.of 0))
    (hi : i = freeAtGenerator 0 (𝟙_ C) ≫
      (MonoidalFreeModule.generator M ((freeAt 0).obj (𝟙_ C))).app (FiniteBijection.of 0)) :
    freeZeroModuleUnitGeneratorLaw M i := by
  unfold freeZeroModuleUnitGeneratorLaw
  rw [hi, Category.assoc]
  exact freeZeroModuleUnitIso_generator_level M

end SerrePositivity.SymmetricSequence
