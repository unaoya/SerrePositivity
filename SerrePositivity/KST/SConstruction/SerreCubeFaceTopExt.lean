module
public import SerrePositivity.KST.SConstruction.SerreCubeGeneratorExt
public import SerrePositivity.KST.SConstruction.SerreCubeGeneratorFaceEvaluation
public import SerrePositivity.KST.SConstruction.SerreCubeTopCellImage

/-! # 元の全標準面の最高生成元像による鎖射の判定
概要：元の全端点・辺 tensor 生成元を標準面の最高生成元へ戻し、元の鎖射を判定する。
方針：元の生成元判定・標準面評価・HA 向きの整数単元の消去を使う。
規約：元の鎖射と標準面像を保持。使われ方：元の Serre Hom 逆構成の一意性と逆律。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の鎖射の二つの値は、同じ元の次数移送後の値が一致すれば一致する。 -/
lemma complexHom_value_of_degree_cast {P Q : Complex A} {p q : ℤ} (hp : p = q)
    (f g : P ⟶ Q) (w : P.X p)
    (h : f.f q (eqToHom (congrArg P.X hp) w) = g.f q (eqToHom (congrArg P.X hp) w)) :
    f.f p w = g.f p w := by
  cases hp
  exact h

/-- 元の全標準面の最高生成元像で一致する元の鎖射は等しい。 -/
lemma serreCube_face_top_hom_ext (n : ℕ) {K : Complex A}
    {f g : serreCubeComplex A n ⟶ K}
    (h : ∀ (d : ℕ) (v : CubeFaceNormal d n),
      f.f (-(d : ℤ)) ((serreCubeFaceNormal A v).hom.f (-(d : ℤ)) (serreCubeTopCell A d)) =
      g.f (-(d : ℤ)) ((serreCubeFaceNormal A v).hom.f (-(d : ℤ)) (serreCubeTopCell A d))) :
    f = g := by
  apply serreCube_generator_hom_ext A n
  intro i
  have he := serreCubeGenerator_face_top A n i
  have hc := (congrArg (fun w => f.f (-(serreCubeGeneratorFreeDimension n i : ℤ)) w) he).symm.trans
    ((h _ (serreCubeGeneratorFaceNormal n i)).trans
      (congrArg (fun w => g.f (-(serreCubeGeneratorFreeDimension n i : ℤ)) w) he))
  exact complexHom_value_of_degree_cast A (serreCubeGeneratorDegree_freeDimension n i)
    f g (serreCubeGenerator A n i) hc

/-- 元の全標準面の HA 向き最高生成元像で一致する元の鎖射は等しい。 -/
lemma serreCube_face_top_image_hom_ext (n : ℕ) {K : Complex A}
    {f g : serreCubeComplex A n ⟶ K}
    (h : ∀ (d : ℕ) (v : CubeFaceNormal d n),
      serreCubeTopCellImage A K d ((serreCubeFaceNormal A v).hom ≫ f) =
        serreCubeTopCellImage A K d ((serreCubeFaceNormal A v).hom ≫ g)) : f = g := by
  apply serreCube_face_top_hom_ext A n
  intro d v
  have hv := h d v
  change f.f (-(d : ℤ)) ((serreCubeFaceNormal A v).hom.f (-(d : ℤ))
      (serreCubeOrientationSign d • serreCubeTopCell A d)) =
    g.f (-(d : ℤ)) ((serreCubeFaceNormal A v).hom.f (-(d : ℤ))
      (serreCubeOrientationSign d • serreCubeTopCell A d)) at hv
  simp only [Units.smul_def, map_zsmul] at hv
  exact smul_left_cancel (serreCubeOrientationSign d) hv

end SerrePositivity.KST.SConstruction
