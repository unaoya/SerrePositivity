module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.FrameParameterEvaluation
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.ResolutionHom
public import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy
/-!
概要：指定余作用と区間評価から全単体Homの区間射を作る。
方針：n単体を同じ余作用・単体パラメータ・区間評価の合成へ送る。
規約：A07の証明分割。単体作用素の可換性をNatTransとして保持する。
使われ方：HA 1.2.4、元の指定二射を結ぶ単体的ホモトピー。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory
open SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable {F G P : SimplexCategory ⥤ C}
/-- 同じ余作用と区間評価による全単体Homの区間射。 -/
def frameHomotopyUnderlyingMap (δ : F ⟶ F ⊗ P)
    (k : F ⊗ (Functor.const SimplexCategory).obj (P.obj ⦋1⦌) ⟶ G) (Q : C) :
    (cosimplicialHom G).obj Q ⊗ (SSet.stdSimplex.{v}.obj ⦋1⦌) ⟶ (cosimplicialHom F).obj Q where
  app n := ↾fun x => frameParameterEvaluation δ k n.unop (SSet.stdSimplex.objEquiv x.2) ≫ x.1
  naturality n m s := by
    ext x
    change frameParameterEvaluation δ k m.unop
      (SSet.stdSimplex.objEquiv ((SSet.stdSimplex.obj ⦋1⦌).map s x.2)) ≫
        (G.map s.unop ≫ x.1) =
      F.map s.unop ≫ (frameParameterEvaluation δ k n.unop (SSet.stdSimplex.objEquiv x.2) ≫ x.1)
    rw [SSet.stdSimplex.map_apply, Equiv.apply_symm_apply]
    rw [← Category.assoc, ← frameParameterEvaluation_naturality, Category.assoc]
end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
