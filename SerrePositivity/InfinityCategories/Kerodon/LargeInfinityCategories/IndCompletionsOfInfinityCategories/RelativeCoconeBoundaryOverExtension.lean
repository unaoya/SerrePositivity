module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.EquivalenceFamilyRelativeExtension
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.EquivalenceCylinderFunctorIso
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.RelativeEquivalenceCylinder
/-!
概要：全固定境界と標的への元の像を同時に保つ可逆修正の延長。
方針：変更側の可逆円柱と固定側の定値円柱を貼り、相対内部 Hom で持ち上げる。
規約：元の標的全図式と全固定境界を厳密に保持する。
使われ方：指定始点評価を保つ join 円柱の構成。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
/-- 概要：可逆境界修正を、別の全境界と標的全図式を固定して延長する。
方針：固定境界の定値族を貼り相対延長を使う。規約：全射を保持。使われ方：相対反映。 -/
lemma exists_extension_of_equivalenceFamily_fixed_boundary_over
    {A B C D Q X Y : SSet.{u}} (p : X ⟶ Y) (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting p)
    {i : A ⟶ B} {j : A ⟶ C} {r : B ⟶ D} {s : C ⟶ D}
    (hP : IsPushout i j r s) (t : D ⟶ Q) [Mono t] (u : Q ⟶ X) (v : B ⟶ X)
    (hv : i ≫ v = j ≫ s ≫ t ≫ u)
    (V : B ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceInterval ⟶ X)
    (h₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceCylinderEndpoint B false ≫ V = r ≫ t ≫ u)
    (h₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceCylinderEndpoint B true ≫ V = v)
    (hV : (i ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceInterval) ≫ V = fst A _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceInterval ≫ j ≫ s ≫ t ≫ u)
    (hVp : V ≫ p = fst B _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceInterval ≫ r ≫ t ≫ u ≫ p) :
    ∃ F : Q ⟶ X, r ≫ t ≫ F = v ∧ s ≫ t ≫ F = s ≫ t ≫ u ∧ F ≫ p = u ≫ p := by
  let w := hP.desc v (s ≫ t ≫ u) hv
  let R := fst C _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceInterval ≫ s ≫ t ≫ u
  have hc : (i ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceInterval) ≫ V = (j ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceInterval) ≫ R := by
    rw [hV]
    dsimp only [R]
    rw [← Category.assoc (j ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceInterval), whiskerRight_fst, Category.assoc]
  let W := (hP.map (tensorRight _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceInterval)).desc V R hc
  have W₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceCylinderEndpoint D false ≫ W = t ≫ u := by
    apply hP.hom_ext
    · rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.equivalenceCylinderEndpoint_naturality, Category.assoc,
        IsPushout.inl_desc, h₀]
    · rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.equivalenceCylinderEndpoint_naturality, Category.assoc,
        IsPushout.inr_desc]
      dsimp only [R]
      rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceCylinderEndpoint_fst, Category.id_comp]
  have W₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceCylinderEndpoint D true ≫ W = w := by
    apply hP.hom_ext
    · rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.equivalenceCylinderEndpoint_naturality, Category.assoc,
        IsPushout.inl_desc, h₁]
      exact (hP.inl_desc _ _ _).symm
    · rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.equivalenceCylinderEndpoint_naturality, Category.assoc,
        IsPushout.inr_desc]
      dsimp only [R]
      rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceCylinderEndpoint_fst, Category.id_comp]
      exact (hP.inr_desc _ _ _).symm
  have Wp : W ≫ p = fst D _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceInterval ≫ t ≫ u ≫ p := by
    apply (hP.map (tensorRight _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceInterval)).hom_ext
    · rw [← Category.assoc, IsPushout.inl_desc, hVp]
      change fst B _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceInterval ≫ r ≫ t ≫ u ≫ p =
        (r ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceInterval) ≫ fst D _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceInterval ≫ t ≫ u ≫ p
      rw [← Category.assoc (r ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceInterval) (fst D _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceInterval),
        whiskerRight_fst, Category.assoc]
    · rw [← Category.assoc, IsPushout.inr_desc]
      dsimp only [R]
      simp only [Category.assoc]
      change fst C _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceInterval ≫ s ≫ t ≫ u ≫ p =
        (s ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceInterval) ≫ fst D _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceInterval ≫ t ≫ u ≫ p
      rw [← Category.assoc (s ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceInterval) (fst D _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceInterval),
        whiskerRight_fst, Category.assoc]
  obtain ⟨F, hF, hFp⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.exists_extension_of_equivalenceFamily_over p hp t u w W W₀ W₁ Wp
  refine ⟨F, ?_, ?_, hFp⟩
  · rw [hF]
    exact hP.inl_desc _ _ _
  · rw [hF]
    exact hP.inr_desc _ _ _
end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
