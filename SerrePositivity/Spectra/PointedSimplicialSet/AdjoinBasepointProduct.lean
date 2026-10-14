module

public import SerrePositivity.Spectra.Pointed.AdjoinBasepointProduct
public import SerrePositivity.Spectra.PointedSimplicialSet.AdjoinBasepoint

/-! # 自由基点追加の直積とsmashの比較 -/

@[expose] public section

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.PointedSimplicialSet

open CategoryTheory CategoryTheory.MonoidalCategory

/-- 二つの自由基点付き単体的集合のsmashを、直積への基点追加と比較する。 -/
def adjoinBasepointProductIso (K L : SSet.{u}) :
    adjoinBasepoint K ⊗ adjoinBasepoint L ≅ adjoinBasepoint (K ⊗ L) :=
  PointedObject.adjoinSmashIso K L

/-- 直積との比較の順射は、両変数に関して自然。 -/
@[reassoc] lemma adjoinBasepointProductIso_hom_naturality {K L K' L' : SSet.{u}}
    (f : K ⟶ K') (g : L ⟶ L') :
    (adjoinBasepointFunctor.map f ⊗ₘ adjoinBasepointFunctor.map g) ≫
      (adjoinBasepointProductIso K' L').hom =
    (adjoinBasepointProductIso K L).hom ≫ adjoinBasepointFunctor.map (f ⊗ₘ g) :=
  PointedObject.adjoinSmashHom_naturality f g

/-- 直積との比較の逆射も、両変数に関して自然。 -/
@[reassoc] lemma adjoinBasepointProductIso_inv_naturality {K L K' L' : SSet.{u}}
    (f : K ⟶ K') (g : L ⟶ L') :
    adjoinBasepointFunctor.map (f ⊗ₘ g) ≫ (adjoinBasepointProductIso K' L').inv =
    (adjoinBasepointProductIso K L).inv ≫
      (adjoinBasepointFunctor.map f ⊗ₘ adjoinBasepointFunctor.map g) :=
  PointedObject.adjoinSmashInv_naturality f g

end SerrePositivity.PointedSimplicialSet
