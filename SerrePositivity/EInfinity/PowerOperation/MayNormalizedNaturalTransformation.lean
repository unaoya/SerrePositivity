module

public import SerrePositivity.EInfinity.PowerOperation.MayNormalizedClasses

/-!
# 同じ係数で規格化した May 演算の厳密自然変換

May, Proposition 2.3(i)(ii)。持ち上げた F_p に使うため、
指定係数 c と同じ D_i から得た加法的演算を全厳密代数射で束ねる。
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory HomologicalComplex
open SerrePositivity.EInfinity.BarrattEccles

abbrev mayNormalizedStrictHomology (k : Type u) [CommRing k] (n : ℤ) :=
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget (operad k) ⋙
    homologyFunctor (ModuleCat k) (.up ℤ) (-n) ⋙ forget₂ (ModuleCat k) AddCommGrpCat

variable {k : Type u} [CommRing k] (p : ℕ) [Fact p.Prime] [CharP k p]

/-- 同じ規格化係数を使う May の演算は全厳密 BE 代数に自然。 -/
def mayNormalizedStrictPowerZero (n : ℤ) (c : k) :
    mayNormalizedStrictHomology k n ⟶ mayNormalizedStrictHomology k n where
  app X := AddCommGrpCat.ofHom (mayNormalizedAddHom p X n c)
  naturality X Y f := by
    ext x
    exact (mayNormalizedHomology_naturality p X n c f x).symm

end SerrePositivity.EInfinity.PowerOperation
