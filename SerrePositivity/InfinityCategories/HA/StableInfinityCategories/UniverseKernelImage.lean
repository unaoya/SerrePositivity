module
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.UniverseVertexIso
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.UniverseZeroObjects
/-!
概要：実零対象核と包含の本質像の一致を任意の追加宇宙へ持ち上げる。
方針：核の零性と本質像の頂点同型をそれぞれ ULift で保ち反映する。
規約：包含の充満忠実性や商の局所化は仮定しない。
使われ方：D-16 の同じ thick 核包含と平坦商を共通宇宙で使う。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories
open CategoryTheory SSet
open scoped _root_.Simplicial
variable {A B C : SSet.{u}} [Quasicategory B] (i : A ⟶ B) (q : B ⟶ C)
  (h : ∀ b : B _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (q.app (Opposite.op ⦋0⦌) b) ↔
    ∃ a : A _⦋0⦌, Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (i.app (Opposite.op ⦋0⦌) a) b))
include h

lemma zeroKernel_ulift_iff_essentialImage
    (b : ((SSet.uliftFunctor.{v}).obj B) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (((SSet.uliftFunctor.{v}).map q).app (Opposite.op ⦋0⦌) b) ↔
      ∃ a : ((SSet.uliftFunctor.{v}).obj A) _⦋0⦌,
        Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso
          (((SSet.uliftFunctor.{v}).map i).app (Opposite.op ⦋0⦌) a) b) := by
  constructor
  · intro hz
    obtain ⟨a, ⟨e⟩⟩ := (h b.down).mp ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.isZeroVertex_iff_ulift _).mpr hz)
    exact ⟨ULift.up a, ⟨_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.uliftVertexIso e⟩⟩
  · rintro ⟨a, ⟨e⟩⟩
    exact (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.isZeroVertex_iff_ulift _).mp ((h b.down).mpr ⟨a.down, ⟨_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.downVertexIso e⟩⟩)

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
