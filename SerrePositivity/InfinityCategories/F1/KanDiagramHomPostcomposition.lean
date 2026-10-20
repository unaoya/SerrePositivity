module

public import SerrePositivity.InfinityCategories.F1.StrictDiagramOppositeHom
public import SerrePositivity.InfinityCategories.F1.KanDiagramUniversalEnriched
public import SerrePositivity.InfinityCategories.HomotopyLimits.RepresentableComparison

/-!
概要：元の strict Kan 変換の全単体を、表現可能 Hom 図式の後合成へ移す。
方針：各成分で豊穣合成を curry し、元の変換の厳密な自然性を使う。
規約：元の全 Hom の Kan 性は要求しない。
使われ方：左切断 prism の終点を、実際の weighted Hom 作用と同定する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
open HomotopyLimits

/-- 各対象の変換を、同じ対象での表現可能 Hom の後合成へ写す。 -/
def kanDiagramHomPostcompositionComponent {I : Type u} [SmallCategory I]
    (F G : KanDiagramObject I) (x : KanObject.{u}) (i : I) :
    SimplicialCategory.sHom (F.val.obj i) (G.val.obj i) ⟶
      (ihom (SimplicialCategory.sHom x (F.val.obj i))).obj
        (SimplicialCategory.sHom x (G.val.obj i)) :=
  curry (eComp SSet x (F.val.obj i) (G.val.obj i))

private lemma kanHomPostcomposition_condition {I : Type u} [SmallCategory I]
    (F G : KanDiagramObject I) (x : KanObject.{u}) {d : SimplexCategoryᵒᵖ}
    (θ : (strictDiagramMappingSpace
      (F.val ⋙ kanObjectForget) (G.val ⋙ kanObjectForget)).obj d) {i j : I} (f : i ⟶ j)
    (k : SimplexCategoryᵒᵖ) (α : d ⟶ k) (a : (SimplicialCategory.sHom x (F.val.obj i)).obj k) :
    ((simplicialHomDiagram G.val x).map f).app k
      (((kanDiagramHomPostcompositionComponent F G x i).app d (θ.val i)).app k α a) =
    ((kanDiagramHomPostcompositionComponent F G x j).app d (θ.val j)).app k α
      (((simplicialHomDiagram F.val x).map f).app k a) := by
  apply CategoryTheory.Functor.functorHom_ext
  intro l β
  apply ConcreteCategory.hom_ext
  intro z
  change (kanObjectForget.map (G.val.map f)).app l
      ((θ.val i).app l _ (a.app l _ z)) =
    (θ.val j).app l _ ((kanObjectForget.map (F.val.map f)).app l (a.app l _ z))
  simpa using θ.property f l (α ≫ β) (a.app l β z)

/-- 元の strict な変換の各単体は、表現可能 Hom 図式間の同じ次数の変換を与える。 -/
def kanDiagramHomPostcompositionSimplex {I : Type u} [SmallCategory I]
    (F G : KanDiagramObject I) (x : KanObject.{u}) {d : SimplexCategoryᵒᵖ}
    (θ : (strictDiagramMappingSpace
      (F.val ⋙ kanObjectForget) (G.val ⋙ kanObjectForget)).obj d) :
    strictDiagramMappingSimplex (simplicialHomDiagram F.val x)
      (simplicialHomDiagram G.val x) d :=
  ⟨fun i => (kanDiagramHomPostcompositionComponent F G x i).app d (θ.val i),
    fun f k α a => by exact kanHomPostcomposition_condition F G x θ f k α a⟩

/-- 全 Hom の後合成を、表現可能 Hom 図式の変換空間への単体集合の射へ束ねる。 -/
def kanDiagramHomPostcomposition {I : Type u} [SmallCategory I]
    (F G : KanDiagramObject I) (x : KanObject.{u}) :
    strictDiagramMappingSpace (F.val ⋙ kanObjectForget) (G.val ⋙ kanObjectForget) ⟶
      strictDiagramMappingSpace (simplicialHomDiagram F.val x) (simplicialHomDiagram G.val x) where
  app d := ↾fun θ => ⟨fun i =>
    (kanDiagramHomPostcompositionComponent F G x i).app d (θ.val i),
    fun f k α a => by exact kanHomPostcomposition_condition F G x θ f k α a⟩
  naturality {d e} α := by
    apply ConcreteCategory.hom_ext
    intro θ
    apply Subtype.ext
    funext i
    exact congrArg (fun f => f (θ.val i))
      ((kanDiagramHomPostcompositionComponent F G x i).naturality α)

end SerrePositivity.InfinityCategories
