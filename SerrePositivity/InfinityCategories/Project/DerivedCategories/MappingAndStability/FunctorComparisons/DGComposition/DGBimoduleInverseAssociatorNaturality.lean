module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor.DGBimoduleIsoNerveAlgebra
public import SerrePositivity.DifferentialGraded.Tensor.Associator.Pentagon
/-!
概要：双加群射の実作用と逆結合子の自然性を、同じ全関手射で照合する。
方針：元の閉零成分・全 Hom 自然な厳密変換・同じ実 nerve を使う。
規約：原 Hom の平坦性と入力圏の Small 性を追加しない。
使われ方：元の通常合成比較 α の自然性と左単位三角式。
-/
@[expose] public section
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet DifferentialGraded
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
private lemma inv_naturality {C : Type*} [Category C] {A B X Y : C}
    (a : A ≅ B) (b : X ≅ Y) (l : A ⟶ X) (r : B ⟶ Y)
    (h : l ≫ b.hom = a.hom ≫ r) : a.inv ≫ l = r ≫ b.inv := by
  apply (cancel_mono b.hom).mp
  rw [Category.assoc, h, ← Category.assoc, Iso.inv_hom_id, Category.id_comp,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]
variable (R : Type u) [CommRing R] (B C E : Type v) (F : Type (max (u + 1) v))
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R B] [Small.{u} B] [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C]
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E] [_root_.SerrePositivity.DifferentialGraded.DGCategory R F]
variable {P P' : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R B C} {Q Q' : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R C E}
  {T T' : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R E F}
local notation "P₀" => _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R B C P
local notation "P₁" => _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R B C P'
local notation "Q₀" => _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R C E Q
local notation "Q₁" => _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R C E Q'
local notation "T₀" => _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R E F T
local notation "T₁" => _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R E F T'
/-- 同じ三つの閉零双加群射に関する逆結合子の自然性。 -/
lemma dgBimoduleAssociator_inv_naturality (f : P ⟶ P') (g : Q ⟶ Q') (h : T ⟶ T') :
    (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.associatorIso R B C E F P₀ Q₀ T₀).inv ≫
      _root_.SerrePositivity.DifferentialGraded.BimoduleTensor.composeMap R B E F (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.composeMap R B C E f g) h =
    _root_.SerrePositivity.DifferentialGraded.BimoduleTensor.composeMap R B C F f (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.composeMap R C E F g h) ≫
      (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.associatorIso R B C E F P₁ Q₁ T₁).inv := by
  exact inv_naturality (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.associatorIso R B C E F P₀ Q₀ T₀)
    (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.associatorIso R B C E F P₁ Q₁ T₁) _ _
    (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.associatorIso_naturality R B C E F f g h)
/-- 同じ逆結合子の自然性は、元の全関手射の実 nerve 像でも成立。 -/
lemma dgBimoduleNerve_inverse_associator_naturality
    (f : P ⟶ P') (g : Q ⟶ Q') (h : T ⟶ T') :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBimoduleFunctorHomFunctor R B F).map
      (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.associatorIso R B C E F P₀ Q₀ T₀).inv ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBimoduleFunctorHomFunctor R B F).map
        (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.composeMap R B E F (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.composeMap R B C E f g) h) =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBimoduleFunctorHomFunctor R B F).map
      (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.composeMap R B C F f (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.composeMap R C E F g h)) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBimoduleFunctorHomFunctor R B F).map
        (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.associatorIso R B C E F P₁ Q₁ T₁).inv := by
  simpa only [CategoryTheory.Functor.map_comp] using! congrArg
    (fun m => (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBimoduleFunctorHomFunctor R B F).map m)
    (dgBimoduleAssociator_inv_naturality R B C E F f g h)
end
end SerrePositivity.InfinityCategories.Project.DerivedCategories
