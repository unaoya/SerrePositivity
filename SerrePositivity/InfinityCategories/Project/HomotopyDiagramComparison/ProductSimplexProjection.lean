module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.PrismLastContraction
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.WeakReverseHomotopy

/-!
# 元の M×Δ[n] の第一射影の弱同値性

概要：任意の M の積から第一成分への元の射影に、実際の収縮を構成する。
方針：M を固定して標準単体だけを最後の頂点へ収縮し、同じ射影の逆データを得る。
規約：M の Kan 性・quasicategory 性・非空性・モデル構造を要求しない。
使われ方：元の積単体の要素圏から既存の高次比較への弱な第一射影。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ProductSimplexProjection
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open _root_.SerrePositivity.InfinityCategories
open scoped _root_.Simplicial
variable (M : SSet.{u}) (n : ℕ)

abbrev projection : M ⊗ (Δ[n] : SSet.{u}) ⟶ M := fst _ _

def sectionMap : M ⟶ M ⊗ (Δ[n] : SSet.{u}) :=
  lift (𝟙 M) (SSet.const (stdSimplex.obj₀Equiv.symm (Fin.last n)))

lemma sectionMap_projection : sectionMap M n ≫ projection M n = 𝟙 M := lift_fst _ _

def contractionMap : (M ⊗ (Δ[n] : SSet.{u})) ⊗ Δ[1] ⟶ M ⊗ Δ[n] where
  app d := ↾fun s => (s.1.1, (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.prismLastContraction n).app d (s.2, s.1.2))
  naturality _ _ θ := by
    apply ConcreteCategory.hom_ext
    intro s
    exact Prod.ext rfl (congrArg (fun f => f (s.2, s.1.2))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.prismLastContraction n).naturality θ))

def contraction : SSet.Homotopy (𝟙 (M ⊗ (Δ[n] : SSet.{u})))
    (projection M n ≫ sectionMap M n) where
  h := contractionMap M n
  h₀ := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro s
    exact Prod.ext rfl (congrArg (fun f => f.app d s.2) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.prismLastContraction_zero n))
  h₁ := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro s
    exact Prod.ext rfl (congrArg (fun f => f.app d s.2) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.prismLastContraction_one n))
  rel := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro s
    exact False.elim s.1.property

lemma projection_weak : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (projection M n) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.isWeakHomotopyEquivalence_of_reverseHomotopyInverse
    (projection M n) (sectionMap M n) (contraction M n)
  rw [sectionMap_projection]
  exact SSet.RelativeMorphism.Homotopy.refl (SSet.RelativeMorphism.botEquiv.symm (𝟙 M))

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ProductSimplexProjection
