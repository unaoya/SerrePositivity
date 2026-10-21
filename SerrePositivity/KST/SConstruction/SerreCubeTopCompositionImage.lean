module
public import SerrePositivity.KST.SConstruction.SerreCubeTopTensor
public import SerrePositivity.KST.SConstruction.SerreCubeTopCellImage
public import SerrePositivity.KST.SConstruction.SerreCubeOrientedComposition

/-! # 元の Serre tensor 分割の像と native dg 合成
概要：元の分割・二つの Hom 射・豊穣合成の実合成は、向き補正後に通常順合成を回収する。
方針：元の最高生成元の tensor 分割と元の二つの chain map の評価を照合する。
規約：同じ実射と同じ Hom 複体。使われ方：HA の分割合成項の実回収。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- 元の tensor 分割と Hom 射・豊穣合成の像は、同じ元の最高生成元上で豊穣順合成。 -/
lemma serreCubeTopCell_composition_image {x y z : D} (p q : ℕ)
    (f : serreCubeComplex A p ⟶ homObject A D x y)
    (g : serreCubeComplex A q ⟶ homObject A D y z) :
    ((serreCubeTensorIso A p q).hom.hom ≫ (f ⊗ₘ g) ≫ eComp (Complex A) x y z).f
        (-((p + q : ℕ) : ℤ)) (serreCubeTopCell A (p + q)) =
      forward A (f.f (-(p : ℤ)) (serreCubeTopCell A p))
        (g.f (-(q : ℤ)) (serreCubeTopCell A q)) (by omega) := by
  have h := congrArg (fun w =>
    (eComp (Complex A) x y z).f (-((p + q : ℕ) : ℤ))
      ((f ⊗ₘ g).f (-((p + q : ℕ) : ℤ)) w)) (serreCubeTopCell_tensor A p q)
  exact h.trans (congrArg (fun w =>
    (eComp (Complex A) x y z).f (-((p + q : ℕ) : ℤ)) w)
    (tensorMap_apply f g (-(p : ℤ)) (-(q : ℤ)) (-((p + q : ℕ) : ℤ)) (by omega)
      (serreCubeTopCell A p) (serreCubeTopCell A q)))

/-- 元の実 tensor 分割・Hom 射・合成は、向き補正後に同じ native 通常順合成を回収する。 -/
lemma serreCubeTopCellImage_composition {x y z : D} (p q : ℕ)
    (f : serreCubeComplex A p ⟶ homObject A D x y)
    (g : serreCubeComplex A q ⟶ homObject A D y z) :
    serreCubeTopCellImage A (homObject A D x z) (p + q)
        ((serreCubeTensorIso A p q).hom.hom ≫ (f ⊗ₘ g) ≫ eComp (Complex A) x y z) =
      compose A (serreCubeTopCellImage A (homObject A D y z) q g)
        (serreCubeTopCellImage A (homObject A D x y) p f) (by omega) := by
  have hm (V W : ModuleCat.{u} A) (h : V ⟶ W) (s : ℤˣ) (w : V) :
      h (s • w) = s • h w := by
    simp only [Units.smul_def, map_zsmul]
  have hf := hm _ _ (f.f (-(p : ℤ))) (serreCubeOrientationSign p) (serreCubeTopCell A p)
  have hg := hm _ _ (g.f (-(q : ℤ))) (serreCubeOrientationSign q) (serreCubeTopCell A q)
  exact (hm _ _
    (((serreCubeTensorIso A p q).hom.hom ≫ (f ⊗ₘ g) ≫ eComp (Complex A) x y z).f
      (-((p + q : ℕ) : ℤ))) (serreCubeOrientationSign (p + q))
        (serreCubeTopCell A (p + q))).trans
    ((congrArg (fun w => serreCubeOrientationSign (p + q) • w)
      (serreCubeTopCell_composition_image A p q f g)).trans
      ((serreCubeOriented_compose A p q (-((p + q : ℕ) : ℤ)) (by omega)
        (f.f (-(p : ℤ)) (serreCubeTopCell A p))
        (g.f (-(q : ℤ)) (serreCubeTopCell A q))).symm.trans
          (congrArg₂ (fun w t => compose A w t (show -(p : ℤ) + -(q : ℤ) =
            -((p + q : ℕ) : ℤ) by omega)) hg.symm hf.symm)))

end SerrePositivity.KST.SConstruction
