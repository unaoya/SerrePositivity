module

public import SerrePositivity.InfinityCategories.F1B.KanRelativeInitialFiberTransfer

/-!
概要：底上の射の全空間での相対始点境界充填は底の fiber でも成立する。
方針：全空間で充填し、射影の可換性で充填が同じ fiber に留まることを確認する。
規約：充填性・quasicategory 性の追加仮定は不要。
使われ方：coherent な余錐の族から各 fiber の余極限性を回収する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：全空間の相対始点境界充填は底の fiber に制限できる。
方針：全空間の持ち上げを得て、その射影を指定した標的の射影で計算する。
規約：射影と比較射は厳密に可換する。
使われ方：普遍余錐の充填条件の fiber ごとの必要条件。 -/
lemma kanInitialBoundaryLifting_fiber_of_total {E F B : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ B) (f : E ⟶ F) (hf : f ≫ q = p)
    (b : B _⦋0⦌) (x : (vertexFiber p b) _⦋0⦌) (hx : InitialBoundaryLifting f x.val) :
    InitialBoundaryLifting (vertexFiberMap p q f hf b) x := by
  intro n a d hfirst sq
  have hfirst' : boundaryVertex n 0 ≫ (a ≫ vertexFiberι p b) =
      SSet.yonedaEquiv.symm x.val := by
    rw [← Category.assoc, hfirst, SSet.yonedaEquiv_symm_comp]
    rfl
  have sq' : CommSq (a ≫ vertexFiberι p b) (boundary (n + 1)).ι f
      (d ≫ vertexFiberι q b) := by
    constructor
    rw [Category.assoc, ← vertexFiberMap_ι p q f hf b, ← Category.assoc,
      ← Category.assoc, sq.w, Category.assoc]
  obtain ⟨l, hl, hld⟩ := hx n _ _ hfirst' sq'
  have hlp : l ≫ p = SSet.const b := by
    rw [← hf, ← Category.assoc, hld, Category.assoc, vertexFiberι_comp, SSet.comp_const]
  refine ⟨vertexFiberLift p b l hlp, ?_, ?_⟩
  · apply vertexFiber_hom_ext p b
    rw [Category.assoc, vertexFiberLift_ι]
    exact hl
  · apply vertexFiber_hom_ext q b
    rw [Category.assoc, vertexFiberMap_ι, ← Category.assoc, vertexFiberLift_ι]
    exact hld

end SerrePositivity.InfinityCategories.F1B
