module

public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
概要：実際の代数の tensor 模型を、同じ構造射による Spec のファイバー積へ移す。
方針：Spec の同型、pullbackSpecIso とファイバー積の対称性を合成する。
規約：元の R-代数構造を保ち、二つの射影との可換式を明示する。
使われ方：Noether 係数模型の底変換を幾何の図式へ渡す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
universe u
variable {A R S B : Type u} [CommRing A] [CommRing R] [CommRing S] [CommRing B]
  [Algebra A R] [Algebra A S] [Algebra R B]

/-- 実際の tensor 模型による、同じ係数射のファイバー積との同型。 -/
def affineTensorModelIso (e : R ⊗[A] S ≃ₐ[R] B) :
    Spec (CommRingCat.of B) ≅
      pullback (Spec.map (CommRingCat.ofHom (algebraMap A S)))
        (Spec.map (CommRingCat.ofHom (algebraMap A R))) :=
  Scheme.Spec.mapIso e.toRingEquiv.toCommRingCatIso.op ≪≫
    (pullbackSpecIso A R S).symm ≪≫
    pullbackSymmetry (Spec.map (CommRingCat.ofHom (algebraMap A R)))
      (Spec.map (CommRingCat.ofHom (algebraMap A S)))

set_option backward.isDefEq.respectTransparency false in
/-- 模型の第一射影は、右挿入と実際の代数同型の合成の Spec。 -/
theorem affineTensorModelIso_hom_fst (e : R ⊗[A] S ≃ₐ[R] B) :
    (affineTensorModelIso e).hom ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (e.toRingHom.comp
        (Algebra.TensorProduct.includeRight : S →ₐ[A] R ⊗[A] S).toRingHom)) := by
  simp only [affineTensorModelIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    pullbackSymmetry_hom_comp_fst]
  rw [pullbackSpecIso_inv_snd]
  change Spec.map (CommRingCat.ofHom e.toRingHom) ≫
    Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : S →ₐ[A] R ⊗[A] S).toRingHom) = _
  rw [← Spec.map_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- 模型の第二射影は、元の R-代数構造射の Spec。 -/
theorem affineTensorModelIso_hom_snd (e : R ⊗[A] S ≃ₐ[R] B) :
    (affineTensorModelIso e).hom ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (algebraMap R B)) := by
  simp only [affineTensorModelIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    pullbackSymmetry_hom_comp_snd]
  rw [pullbackSpecIso_inv_fst']
  change Spec.map (CommRingCat.ofHom e.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap R (R ⊗[A] S))) = _
  rw [← Spec.map_comp]
  congr 1
  ext r
  exact e.commutes r

/-- tensor 模型の二つの実際の構造射は、Spec 上の pullback square を与える。 -/
theorem isPullback_affineTensorModel (e : R ⊗[A] S ≃ₐ[R] B) :
    IsPullback
      (Spec.map (CommRingCat.ofHom (e.toRingHom.comp
        (Algebra.TensorProduct.includeRight : S →ₐ[A] R ⊗[A] S).toRingHom)))
      (Spec.map (CommRingCat.ofHom (algebraMap R B)))
      (Spec.map (CommRingCat.ofHom (algebraMap A S)))
      (Spec.map (CommRingCat.ofHom (algebraMap A R))) := by
  apply IsPullback.of_iso_pullback _ (affineTensorModelIso e)
    (affineTensorModelIso_hom_fst e) (affineTensorModelIso_hom_snd e)
  constructor
  rw [← affineTensorModelIso_hom_fst e, ← affineTensorModelIso_hom_snd e,
    Category.assoc, Category.assoc, pullback.condition]

end SerrePositivity.AlgebraicGeometry
