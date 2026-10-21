module

public import SerrePositivity.EInfinity.Hammock.LeftRoofPrecomposeObjects

/-!
# 始域比較の上行の全図式

概要：元の二つの frame の比較と中間射を全四列の関手へ束ねる。
方針：元の全縦射と各自然性の正方形を使う。
規約：元の全対象・全射・弱同値を保持する。
使われ方：source frame の始域比較の全単体ホモトピー。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v uI vI
namespace SerrePositivity.EInfinity.Hammock.LeftRoof.Precompose
open CategoryTheory
variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) [W.IsMultiplicative]
  {I : Type uI} [Category.{vI} I] {X' Y : C}
  (U' U : I ⥤ C) (p' : U' ⟶ (Functor.const I).obj X') (hp' : ∀ i, W (p'.app i))
  (α : U' ⟶ U) (σ : U ⟶ (Functor.const I).obj Y)
  (hU' : ∀ {i j} (a : i ⟶ j), W (U'.map a))
  (hU : ∀ {i j} (a : i ⟶ j), W (U.map a))

def upperDiagram : I ⥤ Zigzag W word X' Y where
  obj i := upper W (p'.app i) (hp' i) (α.app i) (σ.app i)
  map {i j} a :=
    { app := Fin.cases (𝟙 X') (Fin.cases (U'.map a) (Fin.cases (U.map a)
        (Fin.cases (U.map a) (Fin.cases (𝟙 Y) (fun k => Fin.elim0 k)))))
      app_mem k := by
        fin_cases k
        · exact W.id_mem X'
        · exact hU' a
        · exact hU a
        · exact hU a
        · exact W.id_mem Y
      first := rfl
      last := rfl
      comm k := by
        fin_cases k
        · exact (p'.naturality a).symm
        · exact (α.naturality a).symm
        · exact (Category.id_comp _).trans (Category.comp_id _).symm
        · exact (σ.naturality a).symm }
  map_id i := Zigzag.hom_ext _ _ (by
    intro k
    fin_cases k
    · rfl
    · exact U'.map_id i
    · exact U.map_id i
    · exact U.map_id i
    · rfl)
  map_comp a b := Zigzag.hom_ext _ _ (by
    intro k
    fin_cases k
    · exact (Category.id_comp _).symm
    · exact U'.map_comp a b
    · exact U.map_comp a b
    · exact U.map_comp a b
    · exact (Category.id_comp _).symm)

end SerrePositivity.EInfinity.Hammock.LeftRoof.Precompose
