module

public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorCurryHom
public import SerrePositivity.InfinityCategories.F1.Scaffold.UniversalScaffoldEvaluation

/-!
概要：積に関して定値な底上の相対関手空間の指数則を厳密な同型にする。
方針：相対評価と内部 Hom の評価を結合子で並べ替え、両逆関係を各次数で検査する。
規約：充填性や底の quasicategory 性は不要。
使われ方：定値始域からの coherent 変換と、全切断への写像の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories

/-- 内部 Hom の相対関手の族を、積上の元の相対関手の族へ展開する。 -/
def relativeFunctorUncurryHom {A E B : SSet.{u}} (p : E ⟶ B) (a : A ⟶ B) (L : SSet.{u}) :
    (ihom L).obj (relativeFunctorSpace p a) ⟶ relativeFunctorSpace p (fst A L ≫ a) :=
  relativeFunctorCurry
    ((α_ A L ((ihom L).obj (relativeFunctorSpace p a))).hom ≫
      relativeFunctorUncurry (uncurry (𝟙 ((ihom L).obj (relativeFunctorSpace p a))))) (by
    rw [Category.assoc, relativeFunctorUncurry_projection]
    simp only [associator_hom_fst_assoc])

/-- 定値な底上の積を始域とする相対関手空間は、元の相対関手空間への内部 Hom と同型。 -/
def relativeFunctorExponentialIso {A E B : SSet.{u}} (p : E ⟶ B) (a : A ⟶ B) (L : SSet.{u}) :
    relativeFunctorSpace p (fst A L ≫ a) ≅ (ihom L).obj (relativeFunctorSpace p a) where
  hom := relativeFunctorCurryHom p a L
  inv := relativeFunctorUncurryHom p a L
  hom_inv_id := by
    apply relativeFunctorUncurry_injective p (fst A L ≫ a)
    rw [relativeFunctorUncurry_parameter, relativeFunctorUncurryHom,
      relativeFunctorUncurry_curry, ← Category.assoc, associator_naturality_right,
      Category.assoc, ← relativeFunctorUncurry_parameter, ← uncurry_natural_left,
      Category.comp_id, relativeFunctorCurryHom, uncurry_curry,
      relativeFunctorUncurry_curry, Iso.hom_inv_id_assoc]
  inv_hom_id := by
    apply uncurry_injective
    rw [uncurry_natural_left, relativeFunctorCurryHom, uncurry_curry]
    apply relativeFunctorUncurry_injective p a
    rw [relativeFunctorUncurry_parameter, relativeFunctorUncurry_curry,
      ← Category.assoc, associator_inv_naturality_right, Category.assoc,
      ← relativeFunctorUncurry_parameter, relativeFunctorUncurryHom,
      Category.comp_id, relativeFunctorUncurry_curry, Iso.inv_hom_id_assoc]

end SerrePositivity.InfinityCategories
