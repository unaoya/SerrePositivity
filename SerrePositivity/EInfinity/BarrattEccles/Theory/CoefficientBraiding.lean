module

public import SerrePositivity.DifferentialGraded.Tensor.ScalarExtension.CategoriesAndModules

/-!
# 係数制限と対称モノイダル構造

## 概要
Berger–Moerdijk §1 の代数を係数制限する際に使う Koszul 交換の比較。

## 方針
純粋な斉次テンソル上で、係数制限の tensorator と交換を評価する。

## 規約
任意の可換環準同型を扱い、既存の lax monoidal 構造を使う。

## 使われ方
Barratt–Eccles 代数の入力置換と部分合成の係数制限。
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity

open CategoryTheory MonoidalCategory HomologicalComplex DifferentialGraded
open scoped TensorProduct

variable {S T : Type u} [CommRing S] [CommRing T] (f : S →+* T)

/-- 項別係数制限の既存の tensorator は Koszul 交換と可換。 -/
@[instance_reducible]
def scalarRestrictionLaxBraided : (ScalarExtension.restriction f).LaxBraided where
  toLaxMonoidal := inferInstance
  braided X Y := by
    let F := ScalarExtension.restriction f
    let μXY := Functor.LaxMonoidal.μ F X Y
    let μYX := Functor.LaxMonoidal.μ F Y X
    apply HomologicalComplex.hom_ext
    intro t
    apply mapBifunctor.hom_ext
    intro r s hrs
    change r + s = t at hrs
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    change (SerrePositivity.cochainTensorSymmetry X Y).hom.f t
        (μXY.f t (ιTensorObj (F.obj X) (F.obj Y) r s t hrs (x ⊗ₜ[S] y))) =
      μYX.f t ((SerrePositivity.cochainTensorSymmetry (F.obj X) (F.obj Y)).hom.f t
        (ιTensorObj (F.obj X) (F.obj Y) r s t hrs (x ⊗ₜ[S] y)))
    rw [ScalarExtension.restriction_μ_apply f X Y r s t hrs x y,
      SerrePositivity.cochainTensorSymmetry_hom_apply_ι,
      SerrePositivity.cochainTensorSymmetry_hom_apply_ι]
    simp only [Units.smul_def, map_zsmul]
    exact congrArg (((r * s).negOnePow : ℤ) • ·)
      (ScalarExtension.restriction_μ_apply f Y X s r t (by omega) y x).symm

end SerrePositivity.EInfinity
