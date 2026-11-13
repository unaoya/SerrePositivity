module
public import SerrePositivity.HomologicalAlgebra.NormalizedMooreMap
/-!
概要：加法関手とMoore正規化の指定比較は、元の射影を保つ。
方針：分裂の合成と正規化冪等射の保存を使う。
規約：指定された包含・射影・比較を保持する。IS-W2 A05aの証明の分割。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology AlgebraicTopology.DoldKan
namespace SerrePositivity.HomologicalAlgebra
variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
variable (F : C ⥤ D) [F.Additive] (X : SimplicialObject C)
/-- 指定Moore比較は、交代面複体からの指定射影と可換。 -/
@[reassoc]
theorem normalizedMooreMapHom_projection :
    (F.mapHomologicalComplex (.down ℕ)).map (PInftyToNormalizedMooreComplex X) ≫
      normalizedMooreMapHom F X =
    (alternatingFaceMapComplexCompMapHomologicalComplexIso F).hom.app X ≫
      PInftyToNormalizedMooreComplex (X ⋙ F) := by
  dsimp only [normalizedMooreMapHom]
  simp only [← Category.assoc, ← Functor.map_comp]
  rw [PInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap]
  simp only [Category.assoc]
  rw [alternatingMapIso_PInfty_assoc, PInfty_comp_PInftyToNormalizedMooreComplex]
end SerrePositivity.HomologicalAlgebra
