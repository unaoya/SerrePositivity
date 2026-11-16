module
public import SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.BousfieldKanCellCoproduct
public import SerrePositivity.HomotopicalAlgebra.Diagram.SimplicialCellSkeleton

/-!
概要：空の部分複体の相対細胞とBK自由細胞の添字を厳密に照合する。
方針：既存の相対細胞の非退化単体を自由表示に写し、余積の一意性で同型を作る。
規約：IS-W2 R03aの押し出しの証明分割。新たな重みは選ばない。
使われ方：Mathlibの同じ骨格の押し出しを自由図式の押し出しに移す。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite _root_.SSet
open _root_.SerrePositivity.DiagramModel.BousfieldKanCells
open scoped _root_.Simplicial
variable (I : Type u) [SmallCategory I]

/-- 元の空の部分複体に対する相対細胞は、同じBK自由細胞の添字。 -/
def bkInitialCellEquiv (n : ℕ) (i : I) :
    relativeCellComplexOfMono.Cell ((⊥ : (nerve (Over i)).Subcomplex).ι) n ≃
      NondegenerateData I n i :=
  (show relativeCellComplexOfMono.Cell ((⊥ : (nerve (Over i)).Subcomplex).ι) n ≃
      (nerve (Over i)).nonDegenerate n from
    { toFun c := ⟨c.simplex, c.nonDegenerate⟩
      invFun c :=
        { simplex := c.val
          nonDegenerate := c.property
          notMem := by rintro ⟨x, hx⟩; exact x.property }
      left_inv c := by cases c; rfl
      right_inv c := rfl }).trans (nondegenerateEquiv I n i)

/-- 添字を往復しても、元の相対細胞の単体そのもの。 -/
theorem bkInitialCellEquiv_simplex (n : ℕ) (i : I)
    (c : relativeCellComplexOfMono.Cell ((⊥ : (nerve (Over i)).Subcomplex).ι) n) :
    ((nondegenerateEquiv I n i).symm (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkInitialCellEquiv I n i c)).val = c.simplex := by
  change ((nondegenerateEquiv I n i).symm
    ((nondegenerateEquiv I n i) ⟨c.simplex, c.nonDegenerate⟩)).val = _
  rw [Equiv.symm_apply_apply]

/-- 既存の相対細胞で添字を付け直しても、同じ各評価の余積。 -/
def bkCellReindexIsColimit {n : ℕ} {i : I} {α : Type u}
    (e : α ≃ NondegenerateData I n i) (X : SSet.{u}) :
    IsColimit (Cofan.mk (((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkCellTensor I n).obj X).obj i)
      (fun a : α => _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkCellComponentInclusion I (e a) X)) := by
  refine Cofan.IsColimit.mk _
    (fun s => _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkCellComponentDesc I X s.pt (fun a => s.inj (e.symm a))) ?_ ?_
  · intro s a
    change _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkCellComponentInclusion I (e a) X ≫
      _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkCellComponentDesc I X s.pt (fun b => s.inj (e.symm b)) = s.inj a
    simpa only [_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkCellComponentInclusion_desc, Equiv.symm_apply_apply]
  · intro s m hm
    apply _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkCellComponentHom_ext I
    intro a
    have h := hm (e.symm a)
    change _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkCellComponentInclusion I (e (e.symm a)) X ≫ m = s.inj (e.symm a) at h
    simpa only [_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkCellComponentInclusion_desc, Equiv.apply_symm_apply] using h

/-- 余積の添字を付け直す、同じ自由細胞への指定同型。 -/
def bkCellReindexIso {n : ℕ} {i : I} {α : Type u}
    (e : α ≃ NondegenerateData I n i) (X : SSet.{u}) :
    (∐ fun _ : α => X) ≅ ((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkCellTensor I n).obj X).obj i :=
  (coproductIsCoproduct (fun _ : α => X)).coconePointUniqueUpToIso
    (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkCellReindexIsColimit I e X)

/-- 付け直しの同型は、同じ各成分の包含そのものを運ぶ。 -/
@[reassoc] theorem bkCellReindexIso_ι {n : ℕ} {i : I} {α : Type u}
    (e : α ≃ NondegenerateData I n i) (X : SSet.{u}) (a : α) :
    Sigma.ι (fun _ : α => X) a ≫ (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkCellReindexIso I e X).hom =
      _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkCellComponentInclusion I (e a) X := by
  exact IsColimit.comp_coconePointUniqueUpToIso_hom _ _ (Discrete.mk a)

end SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight
