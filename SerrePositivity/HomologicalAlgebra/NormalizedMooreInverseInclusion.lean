module
public import SerrePositivity.HomologicalAlgebra.NormalizedMooreMap

/-!
概要：指定Moore係数比較の逆射も、同じ包含と交代面複体比較を保つ。
方針：前向き比較の包含則と両逆則から合成を消去する。
規約：IS-W2 C01の既存構成の単位・係数移送則。加法性以外の仮定なし。
使われ方：HA 1.2.4、零次生成元の点ごとの係数輸送。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.HomologicalAlgebra
open CategoryTheory AlgebraicTopology
variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
variable (F : C ⥤ D) [F.Additive] (X : SimplicialObject C)

/-- 指定Moore比較の逆射は、元の包含を交代面比較の逆射へ送る。 -/
theorem normalizedMooreMapInv_inclusion :
    normalizedMooreMapInv F X ≫
      (F.mapHomologicalComplex (.down ℕ)).map (inclusionOfMooreComplexMap X) =
    inclusionOfMooreComplexMap (X ⋙ F) ≫
      (alternatingFaceMapComplexCompMapHomologicalComplexIso F).inv.app X := by
  apply (cancel_mono ((alternatingFaceMapComplexCompMapHomologicalComplexIso F).hom.app X)).mp
  simp only [Category.assoc, Iso.inv_hom_id_app]
  rw [← normalizedMooreMapHom_inclusion]
  change (normalizedMooreMapIso F X).inv ≫ (normalizedMooreMapIso F X).hom ≫
    inclusionOfMooreComplexMap (X ⋙ F) = _
  rw [Iso.inv_hom_id_assoc]
  exact (Category.comp_id _).symm

end SerrePositivity.HomologicalAlgebra
