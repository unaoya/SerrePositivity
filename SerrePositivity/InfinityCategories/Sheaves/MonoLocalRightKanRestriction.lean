module

public import SerrePositivity.InfinityCategories.Sheaves.MonoLocalRightKan
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.RightKanLimitRestriction
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.NatTransHomotopyNaturality

/-!
概要：局所単射の指定恒等余単位から、同じ層の係数の全錐の制限の極限性を得る。
方針：既存の恒等変換の円柱の法則と、指定右 Kan 条件による極限比較を合成する。
規約：HTT 6.2.2.6、Kerodon §7.3（Tag 02Y1）の既存構成の法則。
使われ方：S8 の元の sectionsOf_map の可逆性の単射の場合。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type u} [SmallCategory C] {P Q : Cᵒᵖ ⥤ Type u}
variable {E : SSet.{u + 1}} [Quasicategory E]

/-- 元の集合重みの射影を、係数と同じ宇宙の通常の nerve で表示する。 -/
abbrev asSmallSectionsDiagram (P : Cᵒᵖ ⥤ Type u) (O : Presheaf C E) :=
  nerveMap (asSmallLocalFunctor (Functor.Elements.π P)) ≫ (nerveAsSmallIso Cᵒᵖ).inv ≫ O

/-- 元の指定余単位を同じ係数へ送った円柱。 -/
abbrev monoLocalRightKanCounit (φ : P ⟶ Q) (O : Presheaf C E) :=
  kanRightCounitPostcomp
    (δ := nerveMap (asSmallLocalFunctor φ.mapElements))
    (F := nerveMap (asSmallLocalFunctor (Functor.Elements.π Q)))
    (F₀ := nerveMap (asSmallLocalFunctor (Functor.Elements.π P)))
    (nerveNatTransHomotopy (asSmallRightCounit φ.mapElements φ.mapElementsCompπIso.hom))
    ((nerveAsSmallIso Cᵒᵖ).inv ≫ O)

/-- 指定した恒等余単位の円柱全体は時間に定値。 -/
lemma monoLocalRightKanCounit_h (φ : P ⟶ Q) (O : Presheaf C E) :
    (monoLocalRightKanCounit φ O).h =
      fst _ _ ≫ (asSmallSectionsDiagram P O) := by
  change (nerveNatTransHomotopy (𝟙 (asSmallLocalFunctor (Functor.Elements.π P)))).h ≫
    ((nerveAsSmallIso Cᵒᵖ).inv ≫ O) = _
  rw [nerveNatTransHomotopy_id, Category.assoc]

/-- 局所全射な単射に沿う同じ全錐の制限は、層の係数で極限錐を与える。 -/
lemma monoLocal_restrict_isLimit (J : GrothendieckTopology C) (φ : P ⟶ Q)
    [Mono φ] [CategoryTheory.Presheaf.IsLocallySurjective J φ]
    (O : Presheaf C E) (hO : IsSheaf J O)
    (c : JoinCone (asSmallSectionsDiagram Q O)) (hc : IsLimitCone c) :
    IsLimitCone (restrictJoinCone c (nerveMap (asSmallLocalFunctor φ.mapElements))) := by
  let δ := nerveMap (asSmallLocalFunctor φ.mapElements)
  let p := asSmallSectionsDiagram Q O
  let α : SSet.Homotopy (δ ≫ p) (δ ≫ p) := monoLocalRightKanCounit φ O
  have ha : α = SSet.RelativeMorphism.Homotopy.refl
      (SSet.RelativeMorphism.botEquiv.symm (δ ≫ p)) := by
    apply SSet.RelativeMorphism.Homotopy.ext
    exact monoLocalRightKanCounit_h φ O
  have hk : IsRightKanExtension δ (δ ≫ p) p α :=
    monoLocal_isRightKanExtension J φ O hO
  rw [ha] at hk
  exact (isLimitCone_iff_restrict_of_rightKan_refl δ p hk c).mp hc

end SerrePositivity.InfinityCategories.Sheaves
