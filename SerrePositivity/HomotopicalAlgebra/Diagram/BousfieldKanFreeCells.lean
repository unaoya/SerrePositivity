module
public import SerrePositivity.HomotopicalAlgebra.Diagram.BousfieldKanDegenerate
public import Mathlib.Logic.Equiv.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
概要：BK重みの各次数の非退化単体は、元の非退化射列上の自由図式。
方針：全単体の分解を非退化部分に制限し、最後の射への後合成で自然性を示す。
規約：IS-W2 R03aの細胞表示の証明分割。元の圏に余分な仮定を付けない。
使われ方：自由境界によるBK重みの骨格の付着。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DiagramModel.BousfieldKanCells
open CategoryTheory Limits SSet
open scoped Simplicial
variable (I : Type u) [SmallCategory I]

/-- 非退化な自由細胞の表示。最後の射は任意の元の射。 -/
abbrev NondegenerateData (n : ℕ) (i : I) :=
  Σ c : (nerve I).nonDegenerate n, (c.val.obj (Fin.last n) ⟶ i)

/-- 非退化なBK単体と、非退化な台の射列の自由な表示の全単射。 -/
def nondegenerateEquiv (n : ℕ) (i : I) :
    (nerve (Over i)).nonDegenerate n ≃ NondegenerateData I n i :=
  ((simplexEquiv I n i).subtypeEquiv
    (p := fun s => s ∈ (nerve (Over i)).nonDegenerate n)
    (q := fun (s : SimplexData I n i) => s.1 ∈ (nerve I).nonDegenerate n)
    (fun s => nondegenerate_iff_base I s)).trans
      (Equiv.subtypeSigmaEquiv (fun c : ComposableArrows I n => c.obj (Fin.last n) ⟶ i)
        (fun c => c ∈ (nerve I).nonDegenerate n))

/-- 同じ非退化射列で添字付けた自由な型値図式。 -/
def freeCellDiagram (n : ℕ) : I ⥤ Type u where
  obj i := NondegenerateData I n i
  map f := ↾fun s => ⟨s.1, s.2 ≫ f⟩
  map_id i := by
    apply ConcreteCategory.hom_ext
    rintro ⟨c, g⟩
    simp
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    rintro ⟨c, h⟩
    change (⟨c, h ≫ (f ≫ g)⟩ : NondegenerateData I n _) = ⟨c, (h ≫ f) ≫ g⟩
    simp only [Category.assoc]

/-- 元のBKの非退化単体を評価先の全射で運ぶ図式。 -/
def nondegenerateDiagram (n : ℕ) : I ⥤ Type u where
  obj i := (nerve (Over i)).nonDegenerate n
  map f := ↾fun s => ⟨s.val ⋙ Over.map f, by
    apply (nondegenerate_iff_base I _).mpr
    exact (nondegenerate_iff_base I s.val).mp s.property⟩
  map_id i := by
    apply ConcreteCategory.hom_ext
    intro s
    apply Subtype.ext
    change s.val ⋙ Over.map (𝟙 i) = s.val
    rw [Over.mapId_eq, CategoryTheory.Functor.comp_id]
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro s
    apply Subtype.ext
    change s.val ⋙ Over.map (f ≫ g) = (s.val ⋙ Over.map f) ⋙ Over.map g
    rw [Over.mapComp_eq]
    rfl

/-- BKの非退化部分と自由図式の同定は、元の全評価先の射で自然。 -/
def nondegenerateDiagramIso (n : ℕ) :
    nondegenerateDiagram I n ≅ freeCellDiagram I n :=
  NatIso.ofComponents (fun i => (nondegenerateEquiv I n i).toIso) (by
    intro i j f
    apply ConcreteCategory.hom_ext
    intro s
    rfl)

end SerrePositivity.DiagramModel.BousfieldKanCells
