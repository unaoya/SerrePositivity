module
public import SerrePositivity.HomologicalAlgebra.NormalizedMooreMap
/-!
概要：既存Moore比較の加法関手間の自然変換に関する自然性。
方針：同じMoore包含で相殺し、元の自然変換の自然性に戻す。
規約：IS-W2 A12の前提計算1/3。指定された比較の順射を保持する。
使われ方：HA 1.2.4、図式評価と正規化の指定比較の自然性。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomologicalComplex AlgebraicTopology AlgebraicTopology.DoldKan
namespace SerrePositivity.HomologicalAlgebra
variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
/-- 既存Moore比較は加法関手間の全自然変換に自然。 -/
theorem normalizedMooreMapHom_functor_naturality {F G : C ⥤ D} [F.Additive] [G.Additive]
    (α : F ⟶ G) (X : SimplicialObject C) :
    (NatTrans.mapHomologicalComplex α (.down ℕ)).app ((normalizedMooreComplex C).obj X) ≫
      normalizedMooreMapHom G X =
    normalizedMooreMapHom F X ≫ (normalizedMooreComplex D).map (Functor.whiskerLeft X α) := by
  apply (cancel_mono (inclusionOfMooreComplexMap (X ⋙ G))).mp
  rw [Category.assoc, normalizedMooreMapHom_inclusion]
  simp only [Category.assoc]
  erw [(inclusionOfMooreComplex D).naturality (Functor.whiskerLeft X α)]
  erw [normalizedMooreMapHom_inclusion_assoc]
  apply HomologicalComplex.Hom.ext
  funext n
  change α.app (((normalizedMooreComplex C).obj X).X n) ≫
      G.map ((inclusionOfMooreComplexMap X).f n) ≫ 𝟙 _ =
    F.map ((inclusionOfMooreComplexMap X).f n) ≫ 𝟙 _ ≫ α.app (X.obj (Opposite.op (SimplexCategory.mk n)))
  simp only [Category.comp_id, Category.id_comp]
  exact (α.naturality ((inclusionOfMooreComplexMap X).f n)).symm
end SerrePositivity.HomologicalAlgebra
