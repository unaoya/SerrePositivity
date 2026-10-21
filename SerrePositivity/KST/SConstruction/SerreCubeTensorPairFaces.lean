module
public import SerrePositivity.KST.SConstruction.SerreCubeTensorPair
public import SerrePositivity.KST.SConstruction.SerreCubeRightExtensionTensor
public import SerrePositivity.KST.SConstruction.SerreCubeRightExtensionFace

/-! # 元の左右 tensor 元と内部端点面の実作用
概要：元の左右合成元への内部端点面の作用を、左元への端点追加として回収する。
方針：元の実 tensor 比較の逆律と、右側延長の tensor 表示を評価する。
規約：元の右側全座標と両元を保持。使われ方：内部一面の左右線形復元の制限。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の実 tensor 合成元を分割し直すと、元の左右の同じ tensor を回収する。 -/
lemma serreCubeTensorPair_hom (n m : ℕ) (p q k : ℤ) (hk : p + q = k)
    (x : (serreCubeComplex A n).X p) (y : (serreCubeComplex A m).X q) :
    (serreCubeTensorIso A n m).hom.hom.f k (serreCubeTensorPair A n m p q k hk x y) =
      ιTensorObj (serreCubeComplex A n) (serreCubeComplex A m) p q k hk (x ⊗ₜ[A] y) := by
  have hid : (serreCubeTensorIso A n m).inv.hom ≫ (serreCubeTensorIso A n m).hom.hom =
      𝟙 (serreCubeComplex A n ⊗ serreCubeComplex A m) :=
    congrArg (fun f => f.hom) (serreCubeTensorIso A n m).inv_hom_id
  exact ConcreteCategory.congr_hom (congrArg (fun f => f.f k) hid)
    (ιTensorObj (serreCubeComplex A n) (serreCubeComplex A m) p q k hk (x ⊗ₜ[A] y))

/-- 元の右側延長の左右合成元への作用は、元の左元への同じ実射の作用。 -/
lemma serreCubeTensorPair_rightExtension {n l : ℕ}
    (f : serreCubeComonoid A n ⟶ serreCubeComonoid A l) (m : ℕ)
    (p q k : ℤ) (hk : p + q = k)
    (x : (serreCubeComplex A n).X p) (y : (serreCubeComplex A m).X q) :
    (serreCubeRightExtension A f m).hom.f k (serreCubeTensorPair A n m p q k hk x y) =
      serreCubeTensorPair A l m p q k hk (f.hom.f p x) y := by
  have hc := congrArg (fun g => g.f k (serreCubeTensorPair A n m p q k hk x y))
    (serreCubeRightExtension_tensor_chain A f m)
  have ht := congrArg (fun z => (serreCubeTensorIso A l m).inv.hom.f k
    ((f.hom ⊗ₘ 𝟙 (serreCubeComplex A m)).f k z)) (serreCubeTensorPair_hom A n m p q k hk x y)
  have hm := congrArg (fun z => (serreCubeTensorIso A l m).inv.hom.f k z)
    (tensorMap_apply f.hom (𝟙 (serreCubeComplex A m)) p q k hk x y)
  exact hc.trans (ht.trans hm)

/-- 元の内部端点面は、同じ左右合成元の左元へ同じ端点を追加する。 -/
lemma serreCubeRightFace_tensorPair (b : Bool) (n m : ℕ) (p q k : ℤ) (hk : p + q = k)
    (x : (serreCubeComplex A n).X p) (y : (serreCubeComplex A m).X q) :
    (serreCubeRightFace A b n m).hom.f k (serreCubeTensorPair A n m p q k hk x y) =
      serreCubeTensorPair A (n + 1) m p q k hk ((serreCubeFace A b n 0).hom.f p x) y := by
  have h := congrArg (fun f => f.hom.f k (serreCubeTensorPair A n m p q k hk x y))
    (serreCubeRightExtension_face_zero A b n m)
  exact h.symm.trans (serreCubeTensorPair_rightExtension A (serreCubeFace A b n 0) m p q k hk x y)

end SerrePositivity.KST.SConstruction
