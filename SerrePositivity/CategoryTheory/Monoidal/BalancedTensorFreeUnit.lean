module

public import SerrePositivity.CategoryTheory.Monoidal.FreeModuleMonoidal
public import SerrePositivity.CategoryTheory.Monoidal.BalancedTensorFreeLeft

/-! # 単位と同型な対象からの自由加群の左テンソルの比較 -/

@[expose] public section

universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.MonoidalBalancedTensor

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped CategoryTheory.MonObj

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] (M : C) [MonObj M]

/-- 単位と同型な対象から生成した自由加群を正則加群へ比較する。 -/
def freeUnitFromIso {S : C} (e : S ≅ 𝟙_ C) :
    MonoidalFreeModule.freeObj M S ≅ Mod.regular M :=
  (MonoidalFreeModule.freeFunctor M).mapIso e ≪≫ freeUnitIso M

/-- この比較は生成元を単位への比較と係数の単位の合成へ送る。 -/
@[reassoc]
lemma generator_freeUnitFromIso {S : C} (e : S ≅ 𝟙_ C) :
    MonoidalFreeModule.generator M S ≫ (freeUnitFromIso M e).hom.hom = e.hom ≫ η[M] := by
  unfold freeUnitFromIso
  simp only [Iso.trans_hom, Mod.comp_hom']
  change MonoidalFreeModule.generator M S ≫ (MonoidalFreeModule.freeMap M e.hom).hom ≫
    (freeUnitIso M).hom.hom = _
  rw [generator_freeMap_assoc, generator_freeUnit]

variable [SymmetricCategory C] [IsCommMonObj M] [HasCoequalizers C]
  [∀ X : C, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfShape WalkingParallelPair (tensorRight X)]

/-- 左自由因子の逆比較と単位比較を合成すると通常の左単位子になる。 -/
lemma freeLeft_unit_comparison {S : C} (e : S ≅ 𝟙_ C) (A : Mod C M) :
    (freeLeftIso M S A).inv.hom ≫
        (((freeUnitFromIso M e).hom ▷ A) ≫ (λ_ A).hom).hom =
      e.hom ▷ A.X ≫ (λ_ A.X).hom := by
  rw [freeLeftIso_inv]
  change (MonoidalFreeModule.generator M S ▷ A.X ≫
    projection M (MonoidalFreeModule.freeObj M S) A) ≫
      map M (freeUnitFromIso M e).hom (𝟙 A) ≫ leftUnitHom M A = _
  rw [Category.assoc, projection_map_assoc, Mod.id_hom', tensorHom_id,
    projection_leftUnitHom]
  rw [← comp_whiskerRight_assoc, generator_freeUnitFromIso, comp_whiskerRight,
    Category.assoc, ModObj.one_smul_self]

end SerrePositivity.MonoidalBalancedTensor
