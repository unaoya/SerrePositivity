module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.InnerTwoHornImageDetection
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.PullbackAnodyneRestriction

/-!
概要：底の同型による二次内ホーンの像への元の指定辺保存 Hom の制限は自明 Kan。
方針：同じ底上の元の関手の辺保存を反映し、全相対 Hom の自明 Kan 制限から移す。
規約：元の全空間・関手・標的を変更しない。
使われ方：nerve 上の元の二単体 source 制限の自明 Kan 性。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 底の同型による同じ内ホーンの像への包含は inner anodyne。 -/
lemma innerTwoHorn_image_innerAnodyne {B : SSet.{u}} (s : (Δ[2] : SSet.{u}) ≅ B) :
    innerAnodyneExtensions ((horn 2 1).ι ≫ s.hom) :=
  innerAnodyneExtensions.comp_mem _ _
    (innerAnodyneExtensions.horn_ι (by decide) (by decide))
    (innerAnodyneExtensions.of_isIso _)

/-- 同型による二次内ホーンの像への元の Hom の制限は、同じ関手のままで自明 Kan。 -/
lemma cocartesianPullbackHomRestriction_innerTwoHornImage_trivialKanFibration
    {E F B : SSet.{u}} [Quasicategory B] (s : (Δ[2] : SSet.{u}) ≅ B)
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p] (q : F ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration q] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackHomRestriction p q (Over.mk ((horn 2 1).ι ≫ s.hom))) := by
  let a : Over B := Over.mk ((horn 2 1).ι ≫ s.hom)
  let i : Over.mk (pullback.snd a.hom p ≫ p) ⟶ Over.mk p :=
    Over.homMk (pullback.snd a.hom p) rfl
  letI : Mono a.hom := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.mono_of_innerAnodyne a.hom (innerTwoHorn_image_innerAnodyne s)
  letI : Mono i.left := by
    change Mono (pullback.snd a.hom p)
    infer_instance
  let V := {e | _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge (pullback.fst a.hom p) e}
  let W := {e | _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge p e}
  let hi := fun e he ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.isCocartesianEdge_overPullback_iff p a e).mp he
  have hr (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace q p) _⦋0⦌)
      (hv : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorPredicate q (pullback.snd a.hom p ≫ p) V
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorOverPre q i).app (Opposite.op ⦋0⦌) v)) :
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorPredicate q p W v := by
    obtain ⟨H, hH, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.exists_relativeFunctorVertex q p v
    have hv' := (congrArg
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorPredicate q (pullback.snd a.hom p ≫ p) V)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorOverPre_vertex q i H hH)).mp hv
    have hv'' := (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorPredicate_vertex q
      (pullback.snd a.hom p ≫ p) V (pullback.snd a.hom p ≫ H)
      (by rw [Category.assoc, hH])).mp hv'
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorPredicate_vertex]
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.preservesCocartesianEdges_of_innerTwoHornImage s p q H hH
    rintro e he ⟨b, hb⟩
    obtain ⟨d, hd, hde⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.exists_cocartesianPullbackEdge_of_base_edge p a e he b hb
    have h := hv'' d hd
    change _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge q
      (H.app (Opposite.op ⦋1⦌) ((pullback.snd a.hom p).app (Opposite.op ⦋1⦌) d)) at h
    rwa [hde] at h
  letI := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorOverPre_trivialKanFibration_of_cocartesian q i
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullback_snd_isPrecompositionEquivalence_of_innerAnodyne p a.hom
      (innerTwoHorn_image_innerAnodyne s))
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorPre q i V W hi)
  exact _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.fullRestriction_trivialKanFibration _ _ _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorPre_ι q i V W hi) hr

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
