module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Sheaves.ExtensiveFiniteProducts
public import SerrePositivity.InfinityCategories.Sheaves.ExtensiveCofanPullback
public import SerrePositivity.InfinityCategories.Sheaves.DescentTopology

/-!
概要：元の extensive 位相の層条件を、空族を含む元の有限積保存と同値にする。
方針：有限余積被覆の全引き戻しで同じ錐の極限性を得て、降下位相へ渡す。
  文献対応：HTT 6.2.2.6 の小さい通常の extensive site における Čech 層条件。
規約：元の指定 fan と準圏値係数を保持する。一般 coverage の判定は仮定しない。
使われ方：S1 の有限積による判定の両方向。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
open SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type u} [SmallCategory C] [FinitaryExtensive C]
variable {E : SSet.{u + 1}} [Quasicategory E]

private def emptyProductShape_isInitial (ι : Type u) [IsEmpty ι] :
    IsInitial ((SSet.uliftFunctor.{u + 1, u}).obj (nerve (Discrete ι))) :=
  SSet.isInitialOfNotNonempty (by
    rintro ⟨a⟩
    exact isEmptyElim (nerveEquiv a.down).as)

/-- 元の空積を保てば、初対象での同じ頂点の値は終対象。 -/
lemma PreservesFiniteProductsOnSite.initial_isTerminal
    (F : Presheaf C E) (hF : PreservesFiniteProductsOnSite F) :
    IsTerminalVertex (F.app _ (ULift.up (nerveVertex (Opposite.op (⊥_ C))))) := by
  let B : PEmpty.{u + 1} → C := PEmpty.elim
  let c : Cofan B := Cofan.mk (⊥_ C) (fun i => PEmpty.elim i)
  have hc : IsColimit c := Cofan.IsColimit.mk c (fun s => initial.to s.pt)
    (fun s i => PEmpty.elim i) (fun s m hm => initialIsInitial.hom_ext _ _)
  have hl := hF PEmpty (fun i => Opposite.op (B i)) (cofanToOppositeFan c)
    ⟨cofanToOppositeFan_isLimit c hc⟩
  have ht := (isLimitCone_iff_terminal_of_initialShape
    (emptyProductShape_isInitial PEmpty) _).mp hl
  rw [mapJoinCone_vertex,
    SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCone.ulift_vertex,
    nerveCone_vertex] at ht
  exact ht

/-- 元の有限積保存は、同じ任意の有限余積被覆の篩錐の降下を与える。 -/
lemma PreservesFiniteProductsOnSite.cofanRestriction_isLimit
    (F : Presheaf C E) (hF : PreservesFiniteProductsOnSite F)
    {ι : Type u} [Finite ι] {B : ι → C} (c : Cofan B) (hc : IsColimit c) :
    IsLimitCone (restrictionCone F (cofanGeneratedSieve c)) := by
  classical
  have hl := hF ι (fun i => Opposite.op (B i)) (cofanToOppositeFan c)
    ⟨cofanToOppositeFan_isLimit c hc⟩
  by_cases hi : Nonempty ι
  · letI := hi
    exact (cofanRestriction_isLimit_iff F
      (PreservesFiniteProductsOnSite.initial_isTerminal F hF) c hc).mpr hl
  · letI : IsEmpty ι := not_nonempty_iff.mp hi
    rw [cofanGeneratedSieve_eq_bot]
    have ht := (isLimitCone_iff_terminal_of_initialShape
      (emptyProductShape_isInitial ι) _).mp hl
    rw [mapJoinCone_vertex,
      SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCone.ulift_vertex,
      nerveCone_vertex] at ht
    exact (restrictionCone_bot_isLimit_iff F c.pt).mpr ht

/-- 元の同じ有限余積被覆のすべての引き戻しで降下する。 -/
lemma PreservesFiniteProductsOnSite.universallyDescending_cofan
    (F : Presheaf C E) (hF : PreservesFiniteProductsOnSite F)
    {ι : Type u} [Finite ι] {B : ι → C} (c : Cofan B) (hc : IsColimit c) :
    UniversallyDescendingSieve F (cofanGeneratedSieve c) := by
  intro V f
  letI (i : ι) : HasPullback f (c.inj i) := cofanPullbackHasPullback c hc f i
  have h := PreservesFiniteProductsOnSite.cofanRestriction_isLimit F hF
    (cofanPullback c f) (cofanPullback_isColimit c hc f)
  rw [cofanPullback_generatedSieve] at h
  exact h

/-- 元の有限積保存から、同じ extensive 位相の全被覆篩での層条件を得る。 -/
lemma isSheaf_extensive_of_preservesFiniteProducts
    (F : Presheaf C E) (hF : PreservesFiniteProductsOnSite F) :
    IsSheaf (extensiveTopology C) F := by
  apply (isSheaf_iff_le_descentTopology (extensiveTopology C) F).mpr
  intro U S hS
  obtain ⟨α, hα, B, π, ⟨hc⟩, hπ⟩ :=
    (extensiveTopology.mem_sieves_iff_contains_colimit_cofan S).mp hS
  letI := hα
  let k : Cofan (fun j : ULift.{u} α => B j.down) :=
    Cofan.mk U (fun j => π j.down)
  have hk : IsColimit k := Cofan.isColimitEquivOfEquiv
    (Equiv.ulift : ULift.{u} α ≃ α) (Cofan.mk U π) hc
  have hgen : cofanGeneratedSieve k ∈ (descentTopology F) U :=
    PreservesFiniteProductsOnSite.universallyDescending_cofan F hF k hk
  have hle : cofanGeneratedSieve k ≤ S := by
    intro V f hf
    obtain ⟨j, g, hg⟩ := (Sieve.mem_ofArrows_iff
      (fun j : ULift.{u} α => B j.down) (fun j => π j.down) f).mp hf
    rw [hg]
    exact S.downward_closed (hπ j.down) g
  exact (descentTopology F).superset_covering hle hgen

/-- extensive 位相の元の層条件は、空族を含む元の指定有限積保存と同値。
HTT 6.2.2.6 の、小さい通常の finitary extensive site と準圏値の Čech 層への特殊化。 -/
@[cite HTT "6.2.2.6" (partial := special)
  "小さい通常の finitary extensive site の Čech 層で、空族を含む指定有限積の判定に特殊化。"]
theorem isSheaf_extensive_iff_preservesFiniteProducts (F : Presheaf C E) :
    IsSheaf (extensiveTopology C) F ↔ PreservesFiniteProductsOnSite F :=
  ⟨IsSheaf.preservesFiniteProductsOnSite F, isSheaf_extensive_of_preservesFiniteProducts F⟩

end SerrePositivity.InfinityCategories.Sheaves
