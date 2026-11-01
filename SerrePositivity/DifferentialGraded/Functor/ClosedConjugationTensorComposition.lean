module
public import SerrePositivity.DifferentialGraded.Functor.DGClosedIsoConjugationLaws
/-!
概要：全次数の二項合成を保存する鎖写像族は、閉同型で共役した後も合成を保つ。
方針：抽象対象の上で tensor 合成と共役の交換則を一度適用する。
規約：ラベル族の評価や実加群延長を展開しない。
使われ方：大きい提示式の kernel 検査を避ける、豊穣作用の合成法則。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory SerrePositivity.KST.SConstruction
variable (R : Type u) [CommRing R] {C : Type v}
  [Category C] [EnrichedOrdinaryCategory (Complex R) C]

lemma enrichedClosedIsoConjugation_preserves_tensor_composition
    {X Y Z X' Y' Z' : C} (eX : X ≅ X') (eY : Y ≅ Y') (eZ : Z ≅ Z')
    {K L M : Complex R} (c : K ⊗ L ⟶ M)
    (a : K ⟶ X ⟶[Complex R] Y) (b : L ⟶ Y ⟶[Complex R] Z)
    (h : M ⟶ X ⟶[Complex R] Z)
    (hc : c ≫ h = (a ⊗ₘ b) ≫ eComp (Complex R) X Y Z) :
    c ≫ (h ≫ enrichedClosedIsoConjugation (Complex R) eX eZ) =
      ((a ≫ enrichedClosedIsoConjugation (Complex R) eX eY) ⊗ₘ
        (b ≫ enrichedClosedIsoConjugation (Complex R) eY eZ)) ≫
          eComp (Complex R) X' Y' Z' := by
  rw [← Category.assoc, hc, Category.assoc,
    ← enrichedClosedIsoConjugation_comp, tensorHom_comp_tensorHom_assoc]

end SerrePositivity.DifferentialGraded
