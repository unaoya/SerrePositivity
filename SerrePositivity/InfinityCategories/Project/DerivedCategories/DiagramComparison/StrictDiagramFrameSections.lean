module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictDiagramRightFrameComparison

/-!
概要：strict図式の実right frame Homを、各頂点の射と全ての自然性の式で表示する。
方針：各単体の自然変換を成分の族として読み、同じframe作用素で単体作用を作る。
規約：単なる頂点ごとの積ではなく、全ての添字射の自然性を保持する。
使われ方：HTT 4.2.4.4の写像空間比較におけるstrict側のendの表示。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory HomotopicalAlgebra SSet
open SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (A : Type u) [CommRing A] (d : StrictDiagramDirection)
local instance : ModelCategory (StrictComplexDiagram A d) := strictDiagramReedyModelCategory A d

/-- 同じright frameの各単体を、元のstrict図式として読む。 -/
abbrev strictDiagramFrame (Y : StrictComplexDiagram A d) :
    SimplexCategoryᵒᵖ ⥤ StrictComplexDiagram A d :=
  (rightFrameDiagram (strictDiagramRightFrameFamily A d)).obj Y

/-- frameの固定単体への全成分と、全ての添字射についての自然性。 -/
def StrictDiagramFrameSection (X Y : StrictComplexDiagram A d) (n : SimplexCategoryᵒᵖ) :=
  { f : ∀ j, X.obj j ⟶ ((strictDiagramFrame A d Y).obj n).obj j //
    ∀ (i j : strictDiagramIndex d) (a : i ⟶ j),
      X.map a ≫ f j = f i ≫ ((strictDiagramFrame A d Y).obj n).map a }

/-- 同じframeの作用素は、全成分の自然性を保つ。 -/
def strictDiagramFrameSectionMap (X Y : StrictComplexDiagram A d)
    {m n : SimplexCategoryᵒᵖ} (θ : m ⟶ n) :
    StrictDiagramFrameSection A d X Y m → StrictDiagramFrameSection A d X Y n := by
  intro f
  refine ⟨fun j => f.val j ≫ ((strictDiagramFrame A d Y).map θ).app j, ?_⟩
  intro i j a
  rw [← Category.assoc, f.property i j a, Category.assoc,
    ((strictDiagramFrame A d Y).map θ).naturality a, ← Category.assoc]

/-- 全ての自然性を保持した成分族の単体集合。 -/
def strictDiagramFrameSections (X Y : StrictComplexDiagram A d) : SSet.{u} where
  obj n := StrictDiagramFrameSection A d X Y n
  map θ := ↾(strictDiagramFrameSectionMap A d X Y θ)
  map_id n := by
    apply ConcreteCategory.hom_ext
    intro f
    apply Subtype.ext
    funext j
    change f.val j ≫ ((strictDiagramFrame A d Y).map (𝟙 n)).app j = f.val j
    rw [CategoryTheory.Functor.map_id]
    simp
  map_comp θ φ := by
    apply ConcreteCategory.hom_ext
    intro f
    apply Subtype.ext
    funext j
    change f.val j ≫ ((strictDiagramFrame A d Y).map (θ ≫ φ)).app j =
      (f.val j ≫ ((strictDiagramFrame A d Y).map θ).app j) ≫
        ((strictDiagramFrame A d Y).map φ).app j
    rw [CategoryTheory.Functor.map_comp]
    exact (Category.assoc _ _ _).symm

/-- 実frame Homの全単体と、自然性を課した同じ全成分族との単体的同型。 -/
def strictDiagramFrameSectionsIso (X Y : StrictComplexDiagram A d) :
    (strictDiagramRightFrameMapping A d X).obj Y ≅ strictDiagramFrameSections A d X Y where
  hom :=
    { app := fun _ => ↾fun f => ⟨f.app, fun _ _ a => f.naturality a⟩
      naturality := by intros; rfl }
  inv :=
    { app := fun _ => ↾fun f => { app := f.val, naturality := fun _ _ a => f.property _ _ a }
      naturality := by intros; rfl }
  hom_inv_id := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro f
    apply NatTrans.ext
    rfl
  inv_hom_id := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro f
    apply Subtype.ext
    rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
