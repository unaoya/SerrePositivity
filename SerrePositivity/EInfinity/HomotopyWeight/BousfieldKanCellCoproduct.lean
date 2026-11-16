module
public import SerrePositivity.EInfinity.HomotopyWeight.BousfieldKanCellTensor

/-!
概要：BK自由細胞の各評価は、元の非退化単体の自由表示で添字付けた余積。
方針：同じ成分への包含と全成分からの降下射を単体ごとに記述する。
規約：IS-W2 R03aの骨格押し出しの証明分割。
使われ方：既存の単体集合の骨格の押し出しとの厳密な照合。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.HomotopyWeight
open CategoryTheory Limits Opposite SSet
open SerrePositivity.DiagramModel.BousfieldKanCells
open scoped Simplicial
variable (I : Type u) [SmallCategory I]

/-- 指定した同じ自由細胞の成分の包含。 -/
def bkCellComponentInclusion {n : ℕ} {i : I} (s : NondegenerateData I n i)
    (X : SSet.{u}) : X ⟶ ((bkCellTensor I n).obj X).obj i where
  app _ := ↾fun x => (x, s)
  naturality _ _ _ := rfl

/-- 全自由細胞の各評価の同じ余積余錐。 -/
def bkCellComponentCofan (n : ℕ) (i : I) (X : SSet.{u}) :
    Cofan (fun _ : NondegenerateData I n i => X) :=
  Cofan.mk (((bkCellTensor I n).obj X).obj i)
    (fun s => bkCellComponentInclusion I s X)

/-- 各自由細胞の射を同じ評価の余積から降下する。 -/
def bkCellComponentDesc {n : ℕ} {i : I} (X Z : SSet.{u})
    (f : NondegenerateData I n i → (X ⟶ Z)) :
    ((bkCellTensor I n).obj X).obj i ⟶ Z where
  app d := ↾fun s => (f s.2).app d s.1
  naturality d e α := by
    apply ConcreteCategory.hom_ext
    rintro ⟨x, s⟩
    exact NatTrans.naturality_apply (f s) α x

/-- 同じ余積の降下射は元のすべての包含に一致する。 -/
@[reassoc] theorem bkCellComponentInclusion_desc {n : ℕ} {i : I} (X Z : SSet.{u})
    (f : NondegenerateData I n i → (X ⟶ Z)) (s : NondegenerateData I n i) :
    bkCellComponentInclusion I s X ≫ bkCellComponentDesc I X Z f = f s := rfl

/-- 各評価の自由細胞の余錐は、元の全成分について余積。 -/
def bkCellComponentCofanIsColimit (n : ℕ) (i : I) (X : SSet.{u}) :
    IsColimit (bkCellComponentCofan I n i X) := by
  refine Cofan.IsColimit.mk _
    (fun s => bkCellComponentDesc I X s.pt (fun a => s.inj a)) ?_ ?_
  · intro s a
    rfl
  · intro s m hm
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    rintro ⟨x, a⟩
    exact ConcreteCategory.congr_hom (NatTrans.congr_app (hm a) d) x

/-- 各評価の自由細胞の射は、同じすべての余積成分で決まる。 -/
theorem bkCellComponentHom_ext {n : ℕ} {i : I} {X Z : SSet.{u}}
    {f g : ((bkCellTensor I n).obj X).obj i ⟶ Z}
    (h : ∀ s : NondegenerateData I n i,
      bkCellComponentInclusion I s X ≫ f = bkCellComponentInclusion I s X ≫ g) : f = g := by
  apply (bkCellComponentCofanIsColimit I n i X).hom_ext
  rintro ⟨a⟩
  exact h a

end SerrePositivity.EInfinity.HomotopyWeight
