module
public import SerrePositivity.KST.SConstruction.SerreCubeGeneratorRightFaceChain
public import SerrePositivity.KST.SConstruction.SerreCubeChainCompositionComparison

/-! # 元の右側自由座標付き標準面と実分割合成
概要：左生成元の元の標準面を右側に延長して合成すると、左 Hom 鎖射への前合成に戻る。
方針：元の Serre tensor 分割との厳密な自然性と、元の tensor 射の合成則を使う。
規約：元の射と因子順を保持。使われ方：全生成元の一端点追加の帰納。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

private lemma monoidalSplit_precomp {V : Type*} [Category V] [MonoidalCategory V]
    {X X' P P' Q Y Z W : V} (r : X' ⟶ X) (s : X ⟶ P ⊗ Q)
    (s' : X' ⟶ P' ⊗ Q) (a : P' ⟶ P) (f : P ⟶ Y) (g : Q ⟶ Z)
    (c : Y ⊗ Z ⟶ W) (h : r ≫ s = s' ≫ (a ⊗ₘ 𝟙 Q)) :
    r ≫ (s ≫ (f ⊗ₘ g) ≫ c) = s' ≫ ((a ≫ f) ⊗ₘ g) ≫ c := by
  rw [← Category.assoc r s, h]
  simp only [Category.assoc, tensorHom_comp_tensorHom_assoc, Category.id_comp]

/-- 元の右側自由座標付き標準面は、元の分割合成の左 Hom 鎖射への前合成を回収する。 -/
lemma serreCubeGeneratorRightFace_composition {D : Type v} [DGCategory A D]
    {x y z : D} (n : ℕ) (i : SerreCubeGeneratorIndex n) (t : ℕ)
    (f : serreCubeComplex A n ⟶ homObject A D x y)
    (g : serreCubeComplex A t ⟶ homObject A D y z) :
    (serreCubeGeneratorRightFace A n i t).hom ≫ serreCubeChainComposition A n t f g =
      serreCubeChainComposition A (serreCubeGeneratorFreeDimension n i) t
        ((serreCubeFaceNormal A (serreCubeGeneratorFaceNormal n i)).hom ≫ f) g := by
  have hc := congrArg (fun h => h.hom) (serreCubeRightExtension_tensor A
    (serreCubeFaceNormal A (serreCubeGeneratorFaceNormal n i)) t)
  have ht : (serreCubeGeneratorRightFace A n i t).hom ≫ (serreCubeTensorIso A n t).hom.hom =
      (serreCubeTensorIso A (serreCubeGeneratorFreeDimension n i) t).hom.hom ≫
        ((serreCubeFaceNormal A (serreCubeGeneratorFaceNormal n i)).hom ⊗ₘ
          𝟙 (serreCubeComplex A t)) := hc
  exact monoidalSplit_precomp
    (serreCubeGeneratorRightFace A n i t).hom
    (serreCubeTensorIso A n t).hom.hom
    (serreCubeTensorIso A (serreCubeGeneratorFreeDimension n i) t).hom.hom
    (serreCubeFaceNormal A (serreCubeGeneratorFaceNormal n i)).hom f g
    (eComp (Complex A) x y z) ht

end SerrePositivity.KST.SConstruction
