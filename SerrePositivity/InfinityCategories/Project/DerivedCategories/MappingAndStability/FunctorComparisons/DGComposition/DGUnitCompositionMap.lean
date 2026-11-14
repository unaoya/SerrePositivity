module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans
/-!
概要：単位からの実射と全 Hom の自然性を、同じ厳密 dg 比較へ接続する。
方針：元の斉次合成と実分解の三成分の等式を使う。
規約：出力の射影性と入力の Small 性は不要。使われ方：模型変更の全自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded MonoidalCategory
variable {R : Type u} [CommRing R] {D : Type v} [DGCategory R D]
def dgUnitPostcompMap {x y z : D}
    (i : 𝟙_ (Complex R) ⟶ homObject R D y z) :
    homObject R D x y ⟶ homObject R D x z :=
  ((ρ_ _).inv ≫ _ ◁ i) ≫ eComp (Complex R) x y z
def dgUnitPrecompMap {x y z : D}
    (i : 𝟙_ (Complex R) ⟶ homObject R D x y) :
    homObject R D y z ⟶ homObject R D x z :=
  ((λ_ _).inv ≫ i ▷ _) ≫ eComp (Complex R) x y z
end SerrePositivity.InfinityCategories.Project.DerivedCategories
