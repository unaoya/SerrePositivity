module
public import SerrePositivity.KST.Fibration.ZeroStableHomFamilies

/-! # 元の零値 Kan Hom における、任意の指定部分族を保つ全自然同値の延長 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration

/-- 元の完全関手の Kan Hom のうち、零値関手を頂点とする実全部分複体。 -/
def zeroStableHomSpace (A B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) : SSet.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices (A ⟶[SSet.{u}] B) (StableHomZeroVertex A B)

/-- 零値条件を保つ充填を用い、元の Kan Hom の同じ零値部分空間を可縮と判定する。 -/
theorem zeroStableHomSpace_isContractibleKan (A B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (zeroStableHomSpace A B) := by
  intro n b
  let j := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices (A ⟶[SSet.{u}] B) (StableHomZeroVertex A B)).ι
  have hb : ∀ v, StableHomZeroVertex A B ((b ≫ j).app (Opposite.op ⦋0⦌) v) :=
    fun v => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex (b.app (Opposite.op ⦋0⦌) v)
  obtain ⟨F, hF, hz⟩ := zeroStableHomBoundary_fill_zero n (b ≫ j) hb
  let G := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift (StableHomZeroVertex A B) F hz
  have hG : G ≫ j = F := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι _ _ _
  refine ⟨G, ?_⟩
  apply (cancel_mono j).1
  rw [Category.assoc, hG, hF]

/-- 任意の指定部分族を厳密に保ち、元の全 Kan Hom 内で零値関手族を延長できる。 -/
theorem zeroStableHomFamily_extend {A B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}} {T U : SSet.{u}}
    (i : T ⟶ U) [Mono i] (H : T ⟶ (A ⟶[SSet.{u}] B))
    (hH : ∀ v, StableHomZeroVertex A B (H.app (Opposite.op ⦋0⦌) v)) :
    ∃ F : U ⟶ (A ⟶[SSet.{u}] B), i ≫ F = H ∧
      ∀ v, StableHomZeroVertex A B (F.app (Opposite.op ⦋0⦌) v) := by
  let L := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift (StableHomZeroVertex A B) H hH
  let j := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices (A ⟶[SSet.{u}] B) (StableHomZeroVertex A B)).ι
  have ht : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (terminal.from (zeroStableHomSpace A B)) :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.isContractibleKan_iff_trivialKanFibration _).mp (zeroStableHomSpace_isContractibleKan A B)
  have : HasLiftingProperty i (terminal.from (zeroStableHomSpace A B)) := ht.mem i inferInstance
  let sq : CommSq L i (terminal.from (zeroStableHomSpace A B)) (terminal.from U) :=
    ⟨terminal.hom_ext _ _⟩
  refine ⟨sq.lift ≫ j, ?_, ?_⟩
  · rw [← Category.assoc, sq.fac_left]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι _ _ _
  · intro v
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex (sq.lift.app (Opposite.op ⦋0⦌) v)

end SerrePositivity.KST.Fibration
