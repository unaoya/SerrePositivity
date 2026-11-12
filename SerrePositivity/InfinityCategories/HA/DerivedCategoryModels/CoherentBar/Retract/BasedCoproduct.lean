module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.BasedOperators
/-!
概要：単体次数ごとの未シフト係数直和に、始点を保つ単体写像の作用を置く。
方針：各始点加群の厳密な等号から直和射を作り、包含への制限で関手則を検証する。
規約：元の bar の係数族を使う補助直和であり、実 bar の微分は変更しない。
使われ方：ラベルの Dold–Kan 作用を同じ係数加群へ移す正規化計算。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract
open CategoryTheory Limits DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))

abbrev dgCoherentBarBasedFamily (n : ℕ) (s : I _⦋n⦌) : ModuleCategory R D :=
  ForgetEnrichment.of (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F ⟨n, s⟩)

abbrev dgCoherentBarBasedCoproduct (n : ℕ) : ModuleCategory R D :=
  ∐ dgCoherentBarBasedFamily R D F n

def dgCoherentBarBasedMap {m n : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌)
    (hf : f.toOrderHom 0 = 0) :
    dgCoherentBarBasedCoproduct R D F n ⟶ dgCoherentBarBasedCoproduct R D F m :=
  Sigma.desc (fun s =>
    eqToHom (congrArg (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R))
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarSource_based_map R D F f hf s)).symm ≫
      Sigma.ι (dgCoherentBarBasedFamily R D F m) (I.map f.op s))

@[reassoc]
lemma dgCoherentBarBasedMap_ι {m n : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌)
    (hf : f.toOrderHom 0 = 0) (s : I _⦋n⦌) :
    Sigma.ι (dgCoherentBarBasedFamily R D F n) s ≫ dgCoherentBarBasedMap R D F f hf =
      eqToHom (congrArg (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R))
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarSource_based_map R D F f hf s)).symm ≫
        Sigma.ι (dgCoherentBarBasedFamily R D F m) (I.map f.op s) := by
  simp only [dgCoherentBarBasedMap, Sigma.ι_comp_desc]

private lemma basedInclusion_paths {n : ℕ} {s t : I _⦋n⦌} (h : s = t)
    (M : _root_.SerrePositivity.DifferentialGraded.ModuleCategory R D) (hs : M = dgCoherentBarBasedFamily R D F n s)
    (ht : M = dgCoherentBarBasedFamily R D F n t) :
    eqToHom hs ≫ Sigma.ι (dgCoherentBarBasedFamily R D F n) s =
      eqToHom ht ≫ Sigma.ι (dgCoherentBarBasedFamily R D F n) t := by
  cases h
  rfl

lemma dgCoherentBarBasedMap_id (n : ℕ) :
    dgCoherentBarBasedMap R D F (𝟙 ⦋n⦌) rfl = 𝟙 _ := by
  apply Sigma.hom_ext
  intro s
  rw [dgCoherentBarBasedMap_ι, Category.comp_id]
  have hi : I.map (𝟙 ⦋n⦌).op s = s := by
    change I.map (𝟙 (Opposite.op ⦋n⦌)) s = s
    exact ConcreteCategory.congr_hom (I.map_id _) s
  exact (basedInclusion_paths R D F hi _ _ rfl).trans (Category.id_comp _)

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract
