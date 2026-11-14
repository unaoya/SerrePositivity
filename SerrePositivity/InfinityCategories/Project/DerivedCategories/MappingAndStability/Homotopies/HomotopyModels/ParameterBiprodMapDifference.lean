module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Resolutions.DGModuleFunctorResolutionCompositionMaps
/-!
概要：全パラメータ上の直和差と、同じ直和鎖写像の前合成を照合する。
方針：同じ全 Hom・実二射影・比較 cochain の等式を保持して構成する。
規約：元の出力の射影性と入力の小ささは不要。使われ方：二変数 Hom の固定入力制限の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded MonoidalCategory
open CochainComplex HomComplex SSet
/-- 同じ直和差と、両成分を保持する実直和射との前合成。 -/
lemma parameterBiprod_map_difference {V : Type u} [Category.{v} V] [Preadditive V]
    {P Q P' Q' T : V} [HasBinaryBiproduct P Q] [HasBinaryBiproduct P' Q']
    (a : P ⟶ P') (b : Q ⟶ Q') (p : P' ⟶ T) (q : Q' ⟶ T) :
    biprod.map a b ≫ (biprod.fst ≫ p - biprod.snd ≫ q) =
      biprod.fst ≫ a ≫ p - biprod.snd ≫ b ≫ q := by
  simp only [Preadditive.comp_sub, ← Category.assoc, biprod.map_fst, biprod.map_snd]
end SerrePositivity.InfinityCategories.Project.DerivedCategories
