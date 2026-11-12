module

public import SerrePositivity.KST.Spectra.FreeActionFunctionIso
public import SerrePositivity.KST.Spectra.FreeUniversalCover

/-!
概要：群作用の非斉次座標の関数複体による実際の余単体 cochain 図式。
方針：自由軌道の射の前合成の恒等・合成法則を end との比較から示す。
規約：各次数は Fin n → G で添字付けられた係数の関数複体。
使われ方：Goerss–Jardine VIII §2。群 cochain の π_* と代数的 cochain の比較。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory SSet


namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FreeActionFamily

variable {G : Type u} [Group G]

lemma functionPre_id (S : Type u) (B : Action SSet.{u} G) :
    functionPre (𝟙 (Action.leftRegular G ⊗ Action.trivial G S)) B =
      𝟙 (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialFunctionComplex.obj S B.V) := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro x
  change (fun s ↦ (B.ρ 1).asHom.app n (x s)) = x
  rw [map_one]
  rfl

lemma functionPre_comp {S T U : Type u}
    (θ : (Action.leftRegular G ⊗ Action.trivial G T) ⟶
      (Action.leftRegular G ⊗ Action.trivial G S))
    (η : (Action.leftRegular G ⊗ Action.trivial G U) ⟶
      (Action.leftRegular G ⊗ Action.trivial G T)) (B : Action SSet.{u} G) :
    functionPre (η ≫ θ) B = functionPre θ B ≫ functionPre η B := by
  apply (cancel_epi (functionIso S B).hom).mp
  calc
    (functionIso S B).hom ≫ functionPre (η ≫ θ) B =
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsPre ((GroupActionCochains.actionWeightFunctor G).map (η ≫ θ))
          (coefficients B) ≫ (functionIso U B).hom := (functionIso_pre _ _).symm
    _ = (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsPre ((GroupActionCochains.actionWeightFunctor G).map θ) (coefficients B) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsPre ((GroupActionCochains.actionWeightFunctor G).map η) (coefficients B)) ≫
          (functionIso U B).hom := by
      rw [CategoryTheory.Functor.map_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsPre_comp]
    _ = (functionIso S B).hom ≫ (functionPre θ B ≫ functionPre η B) := by
      rw [Category.assoc, functionIso_pre η B, ← Category.assoc,
        functionIso_pre θ B, Category.assoc]

end FreeActionFamily

namespace GroupActionCochains

/-- 概要：非斉次座標の関数複体による群作用の余単体図式。
方針：自由軌道の単体的図式の各射に反変な関数の前合成を適用する。
規約：係数には単体集合の群作用を入力する。
使われ方：Goerss–Jardine VIII §2。cochain の顔・退化を座標で記述する図式。 -/
def functionCochains {G : Type u} [Group G] (B : Action SSet.{u} G) :
    CosimplicialObject SSet.{u} where
  obj n := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialFunctionComplex.obj (Fin n.len → G) B.V
  map f := FreeActionFamily.functionPre ((freeUniversalCover G).map f.op) B
  map_id n := by
    rw [op_id, CategoryTheory.Functor.map_id]
    change FreeActionFamily.functionPre
      (𝟙 (Action.leftRegular G ⊗ Action.trivial G (Fin n.len → G))) B = 𝟙 _
    exact FreeActionFamily.functionPre_id (Fin n.len → G) B
  map_comp f g := by
    rw [op_comp, CategoryTheory.Functor.map_comp, FreeActionFamily.functionPre_comp]

end GroupActionCochains

end

end SerrePositivity.KST.Spectra
