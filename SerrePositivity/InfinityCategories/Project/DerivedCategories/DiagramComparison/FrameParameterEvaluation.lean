module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StandardSimplexParameter
/-!
概要：指定余作用と区間評価を単体パラメータで合成する。
方針：余作用・区間評価の自然性とテンソルの交換則を使う。
規約：A07の証明分割。新しい余作用や区間は選ばない。
使われ方：HA 1.2.4、全単体Hom上の指定ホモトピー。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable {F G P : SimplexCategory ⥤ C}
/-- 同じ余作用から、指定された区間単体によるframe評価を得る。 -/
def frameParameterEvaluation (δ : F ⟶ F ⊗ P)
    (k : F ⊗ (Functor.const SimplexCategory).obj (P.obj ⦋1⦌) ⟶ G)
    (n : SimplexCategory) (t : n ⟶ ⦋1⦌) : F.obj n ⟶ G.obj n :=
  δ.app n ≫ (F.obj n ◁ P.map t) ≫ k.app n
/-- 同じframe評価は単体パラメータの前合成と可換。 -/
theorem frameParameterEvaluation_naturality (δ : F ⟶ F ⊗ P)
    (k : F ⊗ (Functor.const SimplexCategory).obj (P.obj ⦋1⦌) ⟶ G)
    {m n : SimplexCategory} (s : m ⟶ n) (t : n ⟶ ⦋1⦌) :
    F.map s ≫ frameParameterEvaluation δ k n t =
      frameParameterEvaluation δ k m (s ≫ t) ≫ G.map s := by
  have hk := k.naturality s
  change (F.map s ⊗ₘ 𝟙 (P.obj ⦋1⦌)) ≫ k.app n = k.app m ≫ G.map s at hk
  rw [tensorHom_id] at hk
  dsimp only [frameParameterEvaluation]
  rw [← Category.assoc, δ.naturality s]
  change (δ.app m ≫ (F.map s ⊗ₘ P.map s)) ≫ (F.obj n ◁ P.map t) ≫ k.app n = _
  simp only [Category.assoc, tensorHom_def]
  rw [← whiskerLeft_comp_assoc, ← CategoryTheory.Functor.map_comp]
  rw [← whisker_exchange_assoc, hk]
end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
