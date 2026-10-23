module

public import SerrePositivity.InfinityCategories.F1.SimplexNerveNaturality
public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeNativeProjection

/-!
概要：標準単体の制限と有限鎖の関手の合成を、同じ底上の正方形で結ぶ。
方針：元の標準単体・nerve 同型の両辺を計算する。
規約：元の標準単体の射を保持する。
使われ方：全局所 Hom 比較の共有面への自然性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
variable {C : Type u} [Category.{u} C] {m n : ℕ}
  (f : (Δ[m] : SSet.{u}) ⟶ Δ[n]) (σ : (Δ[n] : SSet.{u}) ⟶ nerve C)

/-- 同じ制限単体を、有限鎖の合成関手の nerve で表示する。 -/
def simplexNerveRestrictionOverIso :
    Over.mk (f ≫ σ) ≅ Over.mk
      (nerveMap (simplexNerveMapFunctor f ⋙ simplexNerveBaseFunctor σ)) :=
  Over.isoMk (stdSimplex.isoNerve m) (by
    change (stdSimplex.isoNerve m).hom ≫ nerveMap _ = f ≫ σ
    rw [← simplexNerveBaseFunctor_comp, simplexNerveBaseFunctor_nerveMap,
      Iso.hom_inv_id_assoc])

/-- 表示正方形は、同じ元の底上の射と厳密に可換。 -/
lemma simplexNerveRestrictionOverIso_comm :
    (simplexNerveRestrictionOverIso f σ).hom ≫
      cocartesianBaseChangeOverMap (simplexNerveMapFunctor f) (simplexNerveBaseFunctor σ) =
    (Over.homMk f rfl : Over.mk (f ≫ σ) ⟶ Over.mk σ) ≫ (simplexNerveOverIso σ).hom := by
  apply Over.OverMorphism.ext
  change (stdSimplex.isoNerve m).hom ≫ nerveMap (simplexNerveMapFunctor f) =
    f ≫ (stdSimplex.isoNerve n).hom
  rw [simplexNerveMapFunctor_nerveMap, Iso.hom_inv_id_assoc]

end SerrePositivity.InfinityCategories
