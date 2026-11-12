module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraQuasiIsoInfinity
public import SerrePositivity.KST.LocalizingInvariants.LocalizationEssentialSurjectivity
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraCellResolution

/-!
概要：実 dg 代数の擬同型 ∞ 局所化の各頂点は native cell 分解の像と同値。
方針：既存局所化の本質的全射性と元の cell augmentation の実反転を合成する。
規約：元の頂点と augmentation の辺を使い、モデル構造を入力しない。
使われ方：Postnikov 錐の極限性の全試験対象を、実 cell 源の写像模型へ帰着する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet Opposite
open scoped Simplicial
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R]

def quasiIsoInfinityVertex (A : Mon (Complex R)) : (quasiIsoInfinity R) _⦋0⦌ :=
  (quasiIsoInfinityMap R).app (op ⦋0⦌)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex ((infinityPresentationFunctor R).obj A))

lemma quasiIsoInfinityMap_isEssentiallySurjective :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsEssentiallySurjective (quasiIsoInfinityMap R) :=
  localization_isEssentiallySurjective _ _ (quasiIsoInfinity_isLocalization R)

lemma exists_quasiIsoInfinityVertexIso (v : (quasiIsoInfinity R) _⦋0⦌) :
    ∃ A : Mon (Complex R), Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (quasiIsoInfinityVertex R A) v) := by
  obtain ⟨s, ⟨e⟩⟩ := quasiIsoInfinityMap_isEssentiallySurjective R v
  refine ⟨(s.obj 0).objDown, ?_⟩
  have hs : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex ((infinityPresentationFunctor R).obj (s.obj 0).objDown) = s :=
    ComposableArrows.ext₀ rfl
  simpa only [quasiIsoInfinityVertex, hs] using (show Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso _ _) from ⟨e⟩)

def quasiIsoInfinityIsoOfQuasiIso {A B : Mon (Complex R)} (f : A ⟶ B)
    (hf : QuasiIso f.hom) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (quasiIsoInfinityVertex R A) (quasiIsoInfinityVertex R B) := by
  have := quasiIsoInfinityMap_inverts R f hf
  exact asIso (Truncated.HomotopyCategory.homMk
    (((nerve.edgeMk ((infinityPresentationFunctor R).map f)).map
      (quasiIsoInfinityMap R)).toTruncated))

lemma exists_cellResolutionInfinityVertexIso (v : (quasiIsoInfinity R) _⦋0⦌) :
    ∃ A : Mon (Complex R),
      Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (quasiIsoInfinityVertex R (cellResolution R A)) v) := by
  obtain ⟨A, ⟨e⟩⟩ := exists_quasiIsoInfinityVertexIso R v
  exact ⟨A, ⟨quasiIsoInfinityIsoOfQuasiIso R (cellAugmentation R A)
    (cellAugmentation_quasiIso R A) ≪≫ e⟩⟩

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
