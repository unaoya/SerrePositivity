module
public import SerrePositivity.KST.SConstruction.SerreCubeGeneratorTensorValues
public import SerrePositivity.KST.SConstruction.SerreCubeBoundaryTensor

/-! # 元の左右生成元の実鎖立方体内での tensor 合成
概要：元の左右の斉次元を、元の実 tensor 比較の逆で同じ鎖立方体内に合成する。
方針：元の同型の逆律と実 tensor 微分の Leibniz 則を保持する。
規約：元の両複体の微分と次数符号を保持。使われ方：内部一面の実 source 微分比較。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の左右の斉次元を、同じ元の左右連結 cube へ実 tensor 同型の逆で送る。 -/
def serreCubeTensorPair (n m : ℕ) (p q k : ℤ) (hk : p + q = k)
    (x : (serreCubeComplex A n).X p) (y : (serreCubeComplex A m).X q) :
    (serreCubeComplex A (n + m)).X k :=
  (serreCubeTensorIso A n m).inv.hom.f k
    (ιTensorObj (serreCubeComplex A n) (serreCubeComplex A m) p q k hk (x ⊗ₜ[A] y))

/-- 元の左右生成元の実 tensor 合成は、同じ連結生成元の指定次数移送。 -/
lemma serreCubeTensorPair_generator (n : ℕ) (i : SerreCubeGeneratorIndex n)
    (m : ℕ) (j : SerreCubeGeneratorIndex m) (k : ℤ)
    (hk : serreCubeGeneratorDegree n i + serreCubeGeneratorDegree m j = k) :
    serreCubeTensorPair A n m (serreCubeGeneratorDegree n i) (serreCubeGeneratorDegree m j)
      k hk (serreCubeGenerator A n i) (serreCubeGenerator A m j) =
      eqToHom (congrArg (fun d => (serreCubeComplex A (n + m)).X d)
        ((serreCubeGeneratorConcat_degree n i m j).trans hk))
        (serreCubeGenerator A (n + m) (serreCubeGeneratorConcat n i m j)) := by
  have h := congrArg (fun x => (serreCubeTensorIso A n m).inv.hom.f k x)
    (serreCubeGeneratorConcat_tensor A n i m j k hk)
  have hid : (serreCubeTensorIso A n m).hom.hom ≫
      (serreCubeTensorIso A n m).inv.hom = 𝟙 (serreCubeComplex A (n + m)) :=
    congrArg (fun f => f.hom) (serreCubeTensorIso A n m).hom_inv_id
  have ht := ConcreteCategory.congr_hom (congrArg (fun f => f.f k) hid)
    (eqToHom (congrArg (fun d => (serreCubeComplex A (n + m)).X d)
      ((serreCubeGeneratorConcat_degree n i m j).trans hk))
      (serreCubeGenerator A (n + m) (serreCubeGeneratorConcat n i m j)))
  exact h.symm.trans ht

private lemma map_add_zsmul (V W : ModuleCat.{u} A) (f : V ⟶ W) (a : ℤ) (x y : V) :
    f (x + a • y) = f x + a • f y := by
  change f.hom (x + a • y) = f.hom x + a • f.hom y
  rw [map_add, map_zsmul]

/-- 元の左右合成の実微分は、両 source 微分と左次数の符号を持つ Leibniz 和。 -/
lemma serreCubeTensorPair_d (n m : ℕ) (p q k : ℤ) (hk : p + q = k)
    (x : (serreCubeComplex A n).X p) (y : (serreCubeComplex A m).X q) :
    (serreCubeComplex A (n + m)).d k (k + 1) (serreCubeTensorPair A n m p q k hk x y) =
      serreCubeTensorPair A n m (p + 1) q (k + 1) (by omega)
        ((serreCubeComplex A n).d p (p + 1) x) y +
      p.negOnePow • serreCubeTensorPair A n m p (q + 1) (k + 1) (by omega)
        x ((serreCubeComplex A m).d q (q + 1) y) := by
  have h := ConcreteCategory.congr_hom ((serreCubeTensorIso A n m).inv.hom.comm k (k + 1))
    (ιTensorObj (serreCubeComplex A n) (serreCubeComplex A m) p q k hk (x ⊗ₜ[A] y))
  have ht := congrArg (fun z => (serreCubeTensorIso A n m).inv.hom.f (k + 1) z)
    (serreTensorDifferential_apply A (serreCubeComplex A n) (serreCubeComplex A m)
      p (p + 1) q (q + 1) k (k + 1) rfl rfl hk rfl x y)
  exact h.trans (ht.trans (map_add_zsmul A _ _ _ _ _ _))

end SerrePositivity.KST.SConstruction
