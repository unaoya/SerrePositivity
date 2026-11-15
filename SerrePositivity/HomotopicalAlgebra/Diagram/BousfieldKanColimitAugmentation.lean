module

public import SerrePositivity.HomotopicalAlgebra.Diagram.BousfieldKanTerminalRealization
public import SerrePositivity.HomotopicalAlgebra.Diagram.ConstantWeightNaturality

/-!
概要：指定BK増大射を零重みの実現と元の余錐の射に分解する。
方針：同じ実現随伴と余米田同型の評価式で照合する。
使われ方：HTT 4.2.4.4、RR02(a)の終対象での増大射の弱同値性。
規約：余錐の脚を取り替えず、元の増大射を用いる。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe w u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.Reedy
namespace SerrePositivity.DiagramModel.FrameWeightRealization
variable {K : Type w} [SmallCategory K]
  {C : Type u} [Category.{w} C] [HasColimitsOfSize.{w, w} C]
  (A : K ⥤ SimplexCategory ⥤ C)
  (c : Cocone (ConstantWeightHom.degree K A (SimplexCategory.mk 0)))

/-- 元の次数零余錐に対応する、零重みの実現からの射。 -/
def zeroWeightCoconeMap :
    (functor K A).obj (ConstantWeightHom.weight K (SimplexCategory.mk 0)) ⟶ c.pt :=
  ((adjunction K A).homEquiv _ _).symm
    ((ConstantWeightHom.homEquiv K A (SimplexCategory.mk 0) c.pt).symm c.ι)

lemma zeroWeightCoconeMap_eq : zeroWeightCoconeMap A c =
    (ConstantWeightRealization.iso K A (SimplexCategory.mk 0)).hom ≫ colimit.desc _ c := by
  apply (cancel_epi (ConstantWeightRealization.iso K A (SimplexCategory.mk 0)).inv).mp
  rw [ConstantWeightRealization.iso_inv_comp]
  simp only [Iso.inv_hom_id_assoc]
  dsimp only [ConstantWeightRealization.homEquiv, zeroWeightCoconeMap, Equiv.trans_apply]
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  simp only [colimConstAdj, Adjunction.mk'_homEquiv]
  rfl

lemma bousfieldKanAugmentation_factor :
    bousfieldKanAugmentation A c =
      (functor K A).map (bousfieldKanZeroWeight K) ≫ zeroWeightCoconeMap A c := by
  apply ((adjunction K A).homEquiv _ _).injective
  rw [bousfieldKanAugmentation_homEquiv, Adjunction.homEquiv_naturality_left]
  rw [zeroWeightCoconeMap, Equiv.apply_symm_apply]

lemma zeroWeightCoconeMap_isIso (hc : IsColimit c) : IsIso (zeroWeightCoconeMap A c) := by
  rw [zeroWeightCoconeMap_eq]
  letI : IsIso (colimit.desc _ c) := by
    change IsIso (colimit.isoColimitCocone ⟨c, hc⟩).hom
    infer_instance
  infer_instance

variable [ModelCategory C]
  (hA : ∀ k, reedyLeft simplex (cofibrations C) (initial.to (A.obj k)))
  (hconst : ∀ k, ∀ {n m : SimplexCategory} (f : n ⟶ m),
    weakEquivalences C ((A.obj k).map f))

include hA hconst in
/-- 終対象のある添字で、指定余極限余錐への元のBK増大射は弱同値。 -/
lemma bousfieldKanAugmentation_weakEquivalence_of_terminal
    {t : K} (ht : IsTerminal t) (hc : IsColimit c) :
    weakEquivalences C (bousfieldKanAugmentation A c) := by
  rw [bousfieldKanAugmentation_factor]
  letI := zeroWeightCoconeMap_isIso A c hc
  exact (weakEquivalences C).comp_mem _ _
    (bousfieldKanZeroWeight_realization_weakEquivalence K A hA hconst ht)
    ((weakEquivalences C).of_isIso _)

end SerrePositivity.DiagramModel.FrameWeightRealization
