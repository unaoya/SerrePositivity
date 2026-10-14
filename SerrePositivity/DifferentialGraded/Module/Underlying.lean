module
public import SerrePositivity.DifferentialGraded.Module.Category
public import Mathlib.CategoryTheory.Discrete.Basic

/-! # dg 加群の underlying family

忘却先は対象の離散族。全次数の作用と自然性を捨てる忘却関手であり、
dg 加群そのものを通常の Dᵒᵖ の関手圏と同一視しない。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 閉零加群の射は全対象の chain map 成分で判定できる。 -/
lemma moduleMorphism_ext {M N : ModuleCategory A D} {f g : M ⟶ N}
    (h : ∀ x : D, (moduleEvaluation A D x).map f = (moduleEvaluation A D x).map g) :
    f = g := by
  change ForgetEnrichment.homTo (Complex A) f = ForgetEnrichment.homTo (Complex A) g
  apply moduleHom_ext
  intro x
  exact (complexClosedHomEquiv A _ _).injective (h x)

/-- 右 dg 加群を対象の離散族に忘却する関手。 -/
def moduleUnderlying : ModuleCategory A D ⥤ (Discrete D ⥤ Complex A) where
  obj M := Discrete.functor (fun x => (moduleEvaluation A D x).obj M)
  map f := Discrete.natTrans (fun x => (moduleEvaluation A D x.as).map f)
  map_id M := by
    apply NatTrans.ext
    funext x
    exact (moduleEvaluation A D x.as).map_id M
  map_comp f g := by
    apply NatTrans.ext
    funext x
    exact (moduleEvaluation A D x.as).map_comp f g

/-- underlying family への忘却は忠実。 -/
instance moduleUnderlying_faithful : (moduleUnderlying A D).Faithful where
  map_injective := by
    intro M N f g h
    apply moduleMorphism_ext
    intro x
    exact congrArg (fun t => t.app (Discrete.mk x)) h
end SerrePositivity.DifferentialGraded
