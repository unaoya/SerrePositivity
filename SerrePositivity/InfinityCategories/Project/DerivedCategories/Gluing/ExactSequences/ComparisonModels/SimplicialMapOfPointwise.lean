module
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorHomotopy

/-! 各次数の具体的な値を同じ既知の自然族へ照合して、値を保持した単体的写像を構成する。 -/
@[expose] public section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory
variable {K X : SSet.{u}} (P : K ⟶ X) (φ : ∀ d, K.obj d → X.obj d)
  (hφ : ∀ d z, φ d z = P.app d z)

def dgGluingSimplicialMapOfPointwise : K ⟶ X where
  app d := ↾(φ d)
  naturality := by
    intro d e α
    apply ConcreteCategory.hom_ext
    intro z
    change φ e (K.map α z) = X.map α (φ d z)
    rw [hφ, hφ]
    exact ConcreteCategory.congr_hom (C := Type u) (P.naturality α) z

lemma dgGluingSimplicialMapOfPointwise_eq : dgGluingSimplicialMapOfPointwise P φ hφ = P := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro z
  exact hφ d z

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
