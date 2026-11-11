module
public import SerrePositivity.DifferentialGraded.Module.Hom.HomotopyAndOperations
public import SerrePositivity.DifferentialGraded.Module.Hom.ConeComparison
/-!
概要：閉零始域からの実加群 cone の右包含を、同じ右包含を順射とする実同型にする。
方針：元 cone 延長を逆に選び、全評価・全次数の cone 分解で往復則を確認する。
規約：ホモトピー同値へ弱めない。使われ方：恒等 Hom gluing の実右軸上の cone 回収。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits HomologicalComplex CochainComplex HomComplex DifferentialGraded
variable (R : Type u) [CommRing R] (E : Type v) [DGCategory R E] [Small.{u} E]

def zeroSourceModuleConeIso {M N : ModuleCategory R E} (f : M ⟶ N) (hM : IsZero M) :
    N ≅ moduleCone R E f where
  hom := moduleConeInr R E f
  inv := moduleConeDesc R E f (𝟙 N) (hM.eq_of_src _ _)
  hom_inv_id := moduleConeDesc_inr R E f (𝟙 N) _
  inv_hom_id := by
    apply moduleMorphism_ext
    intro x
    apply HomologicalComplex.Hom.ext
    funext n
    apply mappingCone.ext_to ((moduleEvaluation R E x).map f) n (n + 1) rfl
    · exact ((HomologicalComplex.eval (ModuleCat R) (.up ℤ) (n + 1)).map_isZero
        ((moduleEvaluation R E x).map_isZero hM)).eq_of_tgt _ _
    · simp only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id,
        HomologicalComplex.comp_f, HomologicalComplex.id_f, moduleConeDesc_eval,
        complexConeDesc_f, moduleConeInr_eval, Category.assoc, mappingCone.inr_f_snd_v,
        Category.id_comp, Category.comp_id]


end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
