module

public import SerrePositivity.InfinityCategories.Sheaves.SheafLimitClosure
public import SerrePositivity.InfinityCategories.Sheaves.SheafGlobalSectionsFamily
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.FunctorStability
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ReflectionSmallLimits
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.EmptyCone
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.EquivalenceTerminal
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.FullSubcomplexInitialReflection

/-!
概要：安定な presentable 係数の層圏に、有限極限と零対象を元の前層圏から持ち上げる。
方針：層の極限閉性を用い、同じ頂点の極限錐と零対象性を全部分複体へ戻す。
使われ方：HA §1.1.3、HTT 6.2.2.7、Kerodon §7.1（Tag 02H1）の極限と始終対象。
規約：周囲で選んだ零頂点をそのまま使う。層化の左完全性はまだ結論しない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
open SerrePositivity.InfinityCategories.HA.StableInfinityCategories
open SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type u} [SmallCategory C] {E : SSet.{u + 1}} [Quasicategory E]

/-- 前層圏の任意の終頂点は、空図式の極限閉性により層である。 -/
lemma sheafProperty_of_isTerminalVertex (J : GrothendieckTopology C)
    (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E)
    (x : (PresheafCat C E) _⦋0⦌) (hx : IsTerminalVertex x) : sheafProperty J x := by
  have h := sheafProperty_limitCone J hE (emptyCone x)
    ((isLimitCone_emptyCone_iff x).mpr hx) (by
      intro k
      exact False.elim k.property)
  simpa only [emptyCone_vertex] using h

/-- 安定係数の層圏の有限極限は、元の前層圏の極限錐を持ち上げて作る。 -/
theorem sheaf_hasFiniteLimits [IsStable E] (J : GrothendieckTopology C)
    (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E) :
    HasFiniteLimits (SheafCat J E) := by
  letI : IsStable (PresheafCat C E) := isStable_functorCategory _ E
  letI : HasFiniteLimits (PresheafCat C E) := hasFiniteLimits_of_isStable _
  constructor
  intro K _ D
  obtain ⟨c, hc⟩ := HasFiniteLimits.hasLimit (D ≫ sheafInclusion J)
  apply fullSubcomplex_hasLimit_of_apex (sheafProperty J) D c hc
  exact sheafProperty_limitCone J hE c hc
    (fun k ↦ fullSubcomplexOnVertices_vertex (D.app _ k))

/-- 前層圏の零頂点を同じ頂点のまま層圏へ戻す。 -/
theorem sheaf_hasZeroVertex [IsStable E] (J : GrothendieckTopology C)
    (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E) :
    HasZeroVertex (SheafCat J E) := by
  letI : IsStable (PresheafCat C E) := isStable_functorCategory _ E
  let z := chosenZeroVertex (PresheafCat C E)
  have hz : sheafProperty J z.vertex := sheafProperty_of_isTerminalVertex J hE _ z.isTerminal
  let w : (SheafCat J E) _⦋0⦌ := ⟨z.vertex, by
    intro α
    have hα : α = 𝟙 _ := Subsingleton.elim _ _
    simpa only [hα, op_id, CategoryTheory.Functor.map_id_apply] using hz⟩
  constructor
  refine ⟨w, ?_, ?_⟩
  · exact fullSubcomplexOnVertices_isInitialVertex_of_image (sheafProperty J) w z.isInitial
  · exact (isFullyFaithful_fullSubcomplexOnVertices_ι (PresheafCat C E) (sheafProperty J)).reflects_isTerminalVertex
      z.isTerminal

end SerrePositivity.InfinityCategories.Sheaves
