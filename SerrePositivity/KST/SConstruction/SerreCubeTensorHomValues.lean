module
public import SerrePositivity.KST.SConstruction.SerreCubeTensorHom

/-! # 元の連結比較の一段の射の評価
概要：元の連結同型の射を、全 tensor 対象を固定した式で回収する。
方針：同型の元の再帰式を、対象を推測せず定義的に展開する。
規約：元の括弧と因子順を保つ。使われ方：右ブロックの型照合。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の連結比較の一段の射を、四対象を固定して回収する。 -/
lemma serreCubeTensorIso_succ_hom (n m : ℕ) :
    (serreCubeTensorIso A n (m + 1)).hom =
      @tensorHom (Comon (Complex A)) _ _ (serreCubeComonoid A (n + m))
        (serreCubeComonoid A n ⊗ serreCubeComonoid A m)
        (serreIntervalComonoid A) (serreIntervalComonoid A)
        (serreCubeTensorIso A n m).hom (𝟙 (serreIntervalComonoid A)) ≫
        (α_ (serreCubeComonoid A n) (serreCubeComonoid A m) (serreIntervalComonoid A)).hom := rfl

end SerrePositivity.KST.SConstruction
