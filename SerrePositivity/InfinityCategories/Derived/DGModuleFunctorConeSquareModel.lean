module
public import SerrePositivity.InfinityCategories.Derived.DGModuleConeSquareData
public import SerrePositivity.InfinityCategories.Derived.DGModuleSquareFunctor
public import SerrePositivity.InfinityCategories.Derived.DGModuleSquarePostcomposeIso
public import SerrePositivity.InfinityCategories.Derived.DGModuleFunctorConeComponents
public import SerrePositivity.InfinityCategories.Derived.DGModuleConePushout

/-! # cone の実同型による関手像の四角形模型

概要：写した射の標準 cofiber 四角形を cone 同型で後合成し、実押し出し模型を得る。
方針：四角形全体の関手同型で普遍性を運び、下側の実二単体を関手像と照合する。
規約：零角の変更は別途必要。使われ方：dg 加群関手の cofiber 保存。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
variable (F : DGFunctor A (RightModule A D) (RightModule A E))
variable {M N : ModuleCategory A D}

/-- 元の cone の実像を終点に持つ標準 cofiber 四角形模型。 -/
def dgModuleFunctorConeSquareModel (f : M ⟶ N) :
    DGModuleSquareData A E (F.onClosed.obj M) (F.onClosed.obj N)
      (moduleZero A E) (F.onClosed.obj (moduleCone A D f)) :=
  (dgModuleConeSquareData A E (F.onClosed.map f)).postcompose
    (dgModuleFunctorConeComparison A D E F f)

/-- 模型は標準 cone 四角形全体との実関手同型を持つ。 -/
def dgModuleFunctorConeSquareModelFunctorIso (f : M ⟶ N) :
    FunctorIso (dgModuleConeSquare A E (F.onClosed.map f))
      (dgModuleFunctorConeSquareModel A D E F f).square := by
  rw [← dgModuleConeSquareData_square]
  exact (dgModuleConeSquareData A E (F.onClosed.map f)).postcomposeFunctorIso _

/-- 実関手同型で運んだ模型は実押し出し四角形である。 -/
lemma dgModuleFunctorConeSquareModel_isPushout (f : M ⟶ N) :
    IsPushoutSquare (dgModuleFunctorConeSquareModel A D E F f).square :=
  (dgModuleConeSquare_isPushout A E (F.onClosed.map f)).of_functorIso
    (dgModuleFunctorConeSquareModelFunctorIso A D E F f)

/-- 模型の下側の実二単体は元の標準四角形の関手像と等しい。 -/
lemma dgModuleFunctorConeSquareModel_lower (f : M ⟶ N) :
    (dgModuleFunctorConeSquareModel A D E F f).lowerTriangle =
      ((dgModuleConeSquareData A D f).map F).lowerTriangle := by
  apply dgSimplex2_ext
  · rfl
  · rfl
  · apply heq_of_eq
    exact congrArg (fun g => (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) g)).val)
      (dgModuleFunctorConeComparison_inr A D E F f)
  · apply heq_of_eq
    change (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A)
      ((0 : F.onClosed.obj M ⟶ moduleCone A E (F.onClosed.map f)) ≫
        dgModuleFunctorConeComparison A D E F f))).val =
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A)
        (F.onClosed.map (0 : M ⟶ moduleCone A D f)))).val
    rw [zero_comp, Functor.map_zero]
  · exact heq_of_eq (dgModuleFunctorConeComparison_inl A D E F f)

end SerrePositivity.InfinityCategories
