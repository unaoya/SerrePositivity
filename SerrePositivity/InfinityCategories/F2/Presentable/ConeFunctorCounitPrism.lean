module

public import SerrePositivity.InfinityCategories.F1.Joins.ConeCylinderMap
public import SerrePositivity.InfinityCategories.F2.Presentable.CoconeFunctorUnitPrism

/-!
概要：全錐族から定値頂点と元の図式を結ぶ全余単位の円柱を作る。
方針：元の錐の円柱比較を前合成し、図式変数を curry する。
規約：頂点族と図式族を全次数で保持する。
使われ方：極限関手と任意の普遍錐族の全自然な比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：全錐族を定値頂点から元の図式への全円柱にする。
方針：錐の円柱と全錐評価を合成し、図式変数を curry する。
規約：元のパラメータの全単体を同時に扱う。
使われ方：極限関手への随伴による比較。 -/
def coneFunctorCounitPrism {K A X : SSet.{u}}
    (s : A ⟶ (ihom (join Δ[0] K)).obj X) :
    A ⊗ (Δ[1] : SSet.{u}) ⟶ (ihom K).obj X :=
  curry (coconeUnitReorder K A ≫ (coneCylinderMap K ▷ A) ≫ uncurry s)

/-- 概要：全錐の円柱の始端は元の頂点族の定値図式。
方針：uncurry して標準錐円柱の始端公式を用いる。
規約：全関手そのものの厳密な等式。
使われ方：余単位の始端認証。 -/
lemma coneFunctorCounitPrism_zero {K A X : SSet.{u}}
    (s : A ⟶ (ihom (join Δ[0] K)).obj X) :
    SSet.ι₀ ≫ coneFunctorCounitPrism s =
      s ≫ evaluateFunctorAt (SSet.yonedaEquiv (joinInl (Δ[0] : SSet.{u}) K)) ≫
        constantFunctorMap K X := by
  rw [evaluateFunctorAt_constantFunctorMap]
  apply uncurry_injective
  rw [uncurry_natural_left, coneFunctorCounitPrism, uncurry_curry, uncurry_pre_app]
  have h : (K ◁ SSet.ι₀ (X := A)) ≫ coconeUnitReorder K A = SSet.ι₀ ▷ A := rfl
  rw [← Category.assoc, ← Category.assoc, h, ← comp_whiskerRight, coneCylinderMap_zero]
  rw [SSet.const_comp]
  have hp : stdSimplex.obj₀Equiv.symm (0 : Fin 1) =
      SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u})) := by
    apply stdSimplex.obj₀Equiv.injective
    apply Fin.ext
    omega
  rw [hp, ← SSet.yonedaEquiv_comp, Category.id_comp]

/-- 概要：全錐の円柱の終端は元の図式族。
方針：uncurry して標準錐円柱の終端公式を用いる。
規約：図式族を選び直さない。
使われ方：余単位の終端認証。 -/
lemma coneFunctorCounitPrism_one {K A X : SSet.{u}}
    (s : A ⟶ (ihom (join Δ[0] K)).obj X) :
    SSet.ι₁ ≫ coneFunctorCounitPrism s = s ≫ (pre (joinInr Δ[0] K)).app X := by
  apply uncurry_injective
  rw [uncurry_natural_left, coneFunctorCounitPrism, uncurry_curry, uncurry_pre_app]
  have h : (K ◁ SSet.ι₁ (X := A)) ≫ coconeUnitReorder K A = SSet.ι₁ ▷ A := rfl
  rw [← Category.assoc, ← Category.assoc, h, ← comp_whiskerRight, coneCylinderMap_one]

end SerrePositivity.InfinityCategories.F2.Presentable
