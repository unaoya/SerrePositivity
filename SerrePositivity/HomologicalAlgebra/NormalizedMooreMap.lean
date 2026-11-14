module
public import Mathlib.AlgebraicTopology.DoldKan.Normalized

/-!
概要：加法関手と Moore 正規化の交換を指定された分裂から構成する。
方針：交代面複体の比較と PInfty の保存で、包含・射影を左右に合成する。
規約：核の保存や平坦性を仮定しない。指定された比較の射を保持する。
使われ方：HA 1.2.4、G10 の EZ ホモトピーの係数変更。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology AlgebraicTopology.DoldKan
namespace SerrePositivity.HomologicalAlgebra
variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
variable (F : C ⥤ D) [F.Additive] (X : SimplicialObject C)

/-- 交代面複体の指定比較は正規化冪等射を保つ。 -/
@[reassoc]
theorem alternatingMapIso_PInfty :
    (F.mapHomologicalComplex (.down ℕ)).map (PInfty (X := X)) ≫
        (alternatingFaceMapComplexCompMapHomologicalComplexIso F).hom.app X =
      (alternatingFaceMapComplexCompMapHomologicalComplexIso F).hom.app X ≫
        PInfty (X := X ⋙ F) := by
  apply HomologicalComplex.hom_ext
  intro n
  simp

/-- 移した Moore 分裂から元の指定 Moore 分裂への比較。 -/
def normalizedMooreMapHom :
    (F.mapHomologicalComplex (.down ℕ)).obj ((normalizedMooreComplex C).obj X) ⟶
      (normalizedMooreComplex D).obj (X ⋙ F) :=
  (F.mapHomologicalComplex (.down ℕ)).map (inclusionOfMooreComplexMap X) ≫
    (alternatingFaceMapComplexCompMapHomologicalComplexIso F).hom.app X ≫
      PInftyToNormalizedMooreComplex (X ⋙ F)

/-- 指定 Moore 比較の逆向きの射。 -/
def normalizedMooreMapInv :
    (normalizedMooreComplex D).obj (X ⋙ F) ⟶
      (F.mapHomologicalComplex (.down ℕ)).obj ((normalizedMooreComplex C).obj X) :=
  inclusionOfMooreComplexMap (X ⋙ F) ≫
    (alternatingFaceMapComplexCompMapHomologicalComplexIso F).inv.app X ≫
      (F.mapHomologicalComplex (.down ℕ)).map (PInftyToNormalizedMooreComplex X)

/-- 指定分裂の比較は同型であり、加法性以外の完全性を要求しない。 -/
def normalizedMooreMapIso :
    (F.mapHomologicalComplex (.down ℕ)).obj ((normalizedMooreComplex C).obj X) ≅
      (normalizedMooreComplex D).obj (X ⋙ F) where
  hom := normalizedMooreMapHom F X
  inv := normalizedMooreMapInv F X
  hom_inv_id := by
    dsimp only [normalizedMooreMapHom, normalizedMooreMapInv]
    simp only [Category.assoc, PInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap_assoc]
    rw [← alternatingMapIso_PInfty_assoc]
    erw [((alternatingFaceMapComplexCompMapHomologicalComplexIso F).app X).hom_inv_id_assoc]
    rw [← Functor.map_comp_assoc, inclusionOfMooreComplexMap_comp_PInfty,
      ← Functor.map_comp]
    erw [(splitMonoInclusionOfMooreComplexMap X).id]
    exact (F.mapHomologicalComplex (.down ℕ)).map_id _
  inv_hom_id := by
    dsimp only [normalizedMooreMapHom, normalizedMooreMapInv]
    simp only [Category.assoc]
    rw [← Functor.map_comp_assoc,
      PInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap,
      alternatingMapIso_PInfty_assoc]
    erw [((alternatingFaceMapComplexCompMapHomologicalComplexIso F).app X).inv_hom_id_assoc]
    rw [inclusionOfMooreComplexMap_comp_PInfty_assoc]
    exact (splitMonoInclusionOfMooreComplexMap (X ⋙ F)).id

/-- 指定同型の前向き射は移した Moore 包含を保つ。 -/
@[reassoc]
theorem normalizedMooreMapHom_inclusion :
    normalizedMooreMapHom F X ≫ inclusionOfMooreComplexMap (X ⋙ F) =
      (F.mapHomologicalComplex (.down ℕ)).map (inclusionOfMooreComplexMap X) ≫
        (alternatingFaceMapComplexCompMapHomologicalComplexIso F).hom.app X := by
  dsimp only [normalizedMooreMapHom]
  simp only [Category.assoc, PInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap]
  rw [← alternatingMapIso_PInfty, ← Functor.map_comp_assoc,
    inclusionOfMooreComplexMap_comp_PInfty]

/-- Moore 比較はすべての単体的対象の射について自然。 -/
theorem normalizedMooreMapHom_naturality {X Y : SimplicialObject C} (f : X ⟶ Y) :
    (F.mapHomologicalComplex (.down ℕ)).map ((normalizedMooreComplex C).map f) ≫
        normalizedMooreMapHom F Y =
      normalizedMooreMapHom F X ≫
        (normalizedMooreComplex D).map (Functor.whiskerRight f F) := by
  apply (cancel_mono (inclusionOfMooreComplexMap (Y ⋙ F))).1
  rw [Category.assoc, normalizedMooreMapHom_inclusion]
  simp only [Category.assoc]
  erw [(inclusionOfMooreComplex D).naturality (Functor.whiskerRight f F)]
  erw [normalizedMooreMapHom_inclusion_assoc]
  simp only [← Category.assoc]
  rw [← Functor.map_comp]
  erw [(inclusionOfMooreComplex C).naturality f]
  rw [Functor.map_comp, Category.assoc]
  erw [(alternatingFaceMapComplexCompMapHomologicalComplexIso F).hom.naturality f]
  simp only [Category.assoc]
  rfl

/-- 加法関手と Moore 正規化の交換を全関手の自然同型にまとめる。 -/
def normalizedMooreMapNatIso :
    normalizedMooreComplex C ⋙ F.mapHomologicalComplex (.down ℕ) ≅
      (SimplicialObject.whiskering C D).obj F ⋙ normalizedMooreComplex D :=
  NatIso.ofComponents (normalizedMooreMapIso F)
    (fun f => normalizedMooreMapHom_naturality F f)

end SerrePositivity.HomologicalAlgebra
