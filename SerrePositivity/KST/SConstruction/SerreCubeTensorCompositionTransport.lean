module
public import SerrePositivity.KST.SConstruction.SerreCubeTensorComposition

/-! # 元の実 tensor 合成の次元と対象の移送
概要：元の左右実鎖射を異なる表示へ移しても、同じ実 tensor 合成を保つ。
方針：元の次元・対象・両鎖射の等号を消去する。
規約：元の因子順と実豊穣合成を保持。使われ方：区間切断列の実合成への照合。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- 元の次元・三対象・両鎖射の表示変更は、元の実 tensor 合成を異種等号で保つ。 -/
lemma serreCubeTensorComposition_heq {n m n' m' : ℕ} (hn : n = n') (hm : m = m')
    {x y z x' y' z' : D} (hx : x = x') (hy : y = y') (hz : z = z')
    (F : serreCubeComplex A n ⟶ homObject A D x y)
    (G : serreCubeComplex A m ⟶ homObject A D y z)
    (F' : serreCubeComplex A n' ⟶ homObject A D x' y')
    (G' : serreCubeComplex A m' ⟶ homObject A D y' z') (hF : HEq F F') (hG : HEq G G') :
    HEq (serreCubeTensorComposition A n m F G) (serreCubeTensorComposition A n' m' F' G') := by
  cases hn
  cases hm
  cases hx
  cases hy
  cases hz
  cases hF
  cases hG
  rfl

/-- 元の左右 cube の次元移送を前合成すると、和次元の同じ移送を回収する。 -/
lemma serreCubeTensorComposition_dimension {n m n' m' : ℕ} (hn : n = n') (hm : m = m')
    {x y z : D} (F : serreCubeComplex A n' ⟶ homObject A D x y)
    (G : serreCubeComplex A m' ⟶ homObject A D y z) :
    serreCubeTensorComposition A n m
        (eqToHom (congrArg (serreCubeComplex A) hn) ≫ F)
        (eqToHom (congrArg (serreCubeComplex A) hm) ≫ G) =
      eqToHom (congrArg (serreCubeComplex A) (congrArg₂ Nat.add hn hm)) ≫
        serreCubeTensorComposition A n' m' F G := by
  cases hn
  cases hm
  simp only [eqToHom_refl, Category.id_comp]

end SerrePositivity.KST.SConstruction
