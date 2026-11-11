module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.VertexFiber
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyWhiskering
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.FilteredInfinity
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FilteredNullHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibrationHomotopyTransport

/-!
概要：同じ filtered な底上の二つの有限図式を一つの共通頂点の fiber へ同時に移す。
方針：二つの底の図式の直和を一つの余錐で収縮し、各図式をその制限で輸送する。
規約：二つの図式は異なる全空間・異なる有限形状を持ってよい。
使われ方：一般 coherent filtered 余極限の有限積比較の有限試験射。

対応節は Kerodon 9.1（Tag 05WY）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories

/-- 概要：二つの有限図式は同じ底の頂点の fiber で同時に表せる。
方針：有限直和の底の図式を一つの頂点へ収縮し、その二つの制限を持ち上げる。
規約：元の指定二射への実際のホモトピーを返す。使われ方：積の全空間模型の検出。 -/
lemma leftFibration_pair_finite_fiber_detection {K L E D B : SSet.{u}}
    [K.Finite] [L.Finite] [Quasicategory B] [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsFilteredInfinity B]
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (q : D ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q]
    (f : K ⟶ E) (g : L ⟶ D) :
    ∃ b : B _⦋0⦌, ∃ s : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b, ∃ t : L ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber q b,
      Nonempty (SSet.Homotopy f (s ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b)) ∧
      Nonempty (SSet.Homotopy g (t ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι q b)) := by
  obtain ⟨b, ⟨H⟩⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.exists_nullHomotopy_of_isFilteredInfinity (coprod.desc (f ≫ p) (g ≫ q))
  have Hf : SSet.Homotopy (f ≫ p) (SSet.const b : K ⟶ B) := by
    simpa only [coprod.inl_desc, SSet.comp_const] using
      _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp H (coprod.inl : K ⟶ K ⨿ L)
  have Hg : SSet.Homotopy (g ≫ q) (SSet.const b : L ⟶ B) := by
    simpa only [coprod.inr_desc, SSet.comp_const] using
      _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp H (coprod.inr : L ⟶ K ⨿ L)
  obtain ⟨s, Hs, _⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibration_transport_along_nullHomotopy p f b Hf
  obtain ⟨t, Ht, _⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibration_transport_along_nullHomotopy q g b Hg
  exact ⟨b, s, t, ⟨Hs⟩, ⟨Ht⟩⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories
