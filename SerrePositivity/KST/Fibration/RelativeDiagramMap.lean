module
public import SerrePositivity.KST.Fibration.RelativeDiagram

/-! # 相対図式の再添字

評価と厳密に可換な射は、全成分の W 条件を保つ。
再添字写像の恒等・合成と、周囲への包含・商の core 評価との可換性を保持する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w z
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration

/-- 評価の再添字と可換な射を相対部分複体へ制限する。 -/
def relativeDiagramMap {B C X Y : SSet.{u}} {J : Type v} {K : Type w}
    (q : B ⟶ C) (evX : J → (X ⟶ B)) (evY : K → (Y ⟶ B))
    (f : X ⟶ Y) (r : K → J) (hf : ∀ k, f ≫ evY k = evX (r k)) :
    (relativeDiagram q evX : SSet.{u}) ⟶ (relativeDiagram q evY : SSet.{u}) :=
  Subcomplex.lift ((relativeDiagram q evX).ι ≫ f) (by
    rintro n _ ⟨s, rfl⟩ k
    have he := ConcreteCategory.congr_hom (NatTrans.congr_app (hf k) n) s.val
    change q.app n ((evY k).app n (f.app n s.val)) ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore C).obj n
    change (evY k).app n (f.app n s.val) = (evX (r k)).app n s.val at he
    rw [he]
    exact s.property (r k))

/-- 制限した射の包含後は、元の実射に厳密に一致する。 -/
lemma relativeDiagramMap_ι {B C X Y : SSet.{u}} {J : Type v} {K : Type w}
    (q : B ⟶ C) (evX : J → (X ⟶ B)) (evY : K → (Y ⟶ B))
    (f : X ⟶ Y) (r : K → J) (hf : ∀ k, f ≫ evY k = evX (r k)) :
    relativeDiagramMap q evX evY f r hf ≫ (relativeDiagram q evY).ι =
      (relativeDiagram q evX).ι ≫ f := rfl

/-- 再添字は商の core への各評価とも厳密に可換。 -/
lemma relativeDiagramMap_evaluation {B C X Y : SSet.{u}} {J : Type v} {K : Type w}
    (q : B ⟶ C) (evX : J → (X ⟶ B)) (evY : K → (Y ⟶ B))
    (f : X ⟶ Y) (r : K → J) (hf : ∀ k, f ≫ evY k = evX (r k)) (k : K) :
    relativeDiagramMap q evX evY f r hf ≫ relativeDiagramEvaluation q evY k =
      relativeDiagramEvaluation q evX (r k) := by
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore C).ι).1
  simp only [Category.assoc, relativeDiagramEvaluation_ι]
  rw [← Category.assoc, ← Category.assoc, relativeDiagramMap_ι]
  simp only [Category.assoc]
  rw [← Category.assoc f (evY k) q, hf k]

/-- 恒等射の制限は恒等射。 -/
lemma relativeDiagramMap_id {B C X : SSet.{u}} {J : Type v}
    (q : B ⟶ C) (ev : J → (X ⟶ B)) :
    relativeDiagramMap q ev ev (𝟙 X) id (fun _ => Category.id_comp _) =
      𝟙 (relativeDiagram q ev : SSet.{u}) := by
  apply (cancel_mono (relativeDiagram q ev).ι).1
  simp only [relativeDiagramMap_ι, Category.comp_id, Category.id_comp]

/-- 再添字写像を含めて実合成を保持する。 -/
lemma relativeDiagramMap_comp {B C X Y Z : SSet.{u}}
    {J : Type v} {K : Type w} {L : Type z}
    (q : B ⟶ C) (evX : J → (X ⟶ B)) (evY : K → (Y ⟶ B))
    (evZ : L → (Z ⟶ B)) (f : X ⟶ Y) (g : Y ⟶ Z)
    (r : K → J) (s : L → K)
    (hf : ∀ k, f ≫ evY k = evX (r k)) (hg : ∀ l, g ≫ evZ l = evY (s l)) :
    relativeDiagramMap q evX evY f r hf ≫ relativeDiagramMap q evY evZ g s hg =
      relativeDiagramMap q evX evZ (f ≫ g) (r ∘ s)
        (fun l => by rw [Category.assoc, hg l, hf (s l)]; rfl) := by
  apply (cancel_mono (relativeDiagram q evZ).ι).1
  rw [Category.assoc, relativeDiagramMap_ι, ← Category.assoc,
    relativeDiagramMap_ι, relativeDiagramMap_ι, Category.assoc]

end SerrePositivity.KST.Fibration
