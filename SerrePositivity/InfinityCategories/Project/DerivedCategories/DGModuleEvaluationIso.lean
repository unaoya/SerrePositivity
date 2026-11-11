module
public import SerrePositivity.DifferentialGraded.Module.Graded

/-! # 実加群同型の評価による判定

概要：閉零加群射の全評価が複体同型なら、その実射自身は加群同型。
方針：同じ射の評価成分を同型族とし、全 dg 自然な逆を組み立てる。
規約：次数零の通常の自然変換だけに制限しない。使われ方：実 cone 比較と tensor。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 全評価で同型となる実加群射の同じ成分を持つ加群同型。 -/
def dgModuleIsoOfEvaluation {M N : ModuleCategory A D} (f : M ⟶ N)
    (h : ∀ x : D, IsIso ((moduleEvaluation A D x).map f)) : M ≅ N := by
  letI (x : D) := h x
  exact moduleIsoMk A D (fun x => asIso ((moduleEvaluation A D x.unop).map f))
    (fun x y => (moduleMapFamilyEquiv A D M N f).property x y)

/-- 評価から組み立てた同型の順射は元の実加群射。 -/
lemma dgModuleIsoOfEvaluation_hom {M N : ModuleCategory A D} (f : M ⟶ N) (h) :
    (dgModuleIsoOfEvaluation A D f h).hom = f := by
  apply moduleMorphism_ext
  intro x
  rw [dgModuleIsoOfEvaluation, moduleIsoMk_hom_eval]
  rfl

/-- 全ての実評価で同型となる加群射は同型。 -/
lemma dgModule_isIso_of_evaluation {M N : ModuleCategory A D} (f : M ⟶ N)
    (h : ∀ x : D, IsIso ((moduleEvaluation A D x).map f)) : IsIso f := by
  rw [← dgModuleIsoOfEvaluation_hom A D f h]
  infer_instance

end SerrePositivity.InfinityCategories.Project.DerivedCategories
