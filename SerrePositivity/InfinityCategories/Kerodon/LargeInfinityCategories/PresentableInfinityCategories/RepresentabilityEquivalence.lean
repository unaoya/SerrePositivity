module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.ContravariantContinuity
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.FullyFaithfulJointHom
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.QCatEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafRestrictionEquivalence
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.UniverseVertexIso
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableEquivalence

/-!
概要：小さい空間値前層の表現可能性を元の圏同値に沿って移す。
方針：充満忠実な全 Yoneda 比較と前合成同値の同型反映を使う。
規約：元の全 Hom 関手と同じ指定宇宙変更を保持する。
使われ方：Ind の反映模型から一般の presentable 圏への表現対象の移送。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories


/-- 概要：同型な対象の元の全表現可能前層は全自然同型。
方針：同じ頂点同型を持ち上げ、元の全 Yoneda 写像で送る。
規約：元の二対象と同型を保持する。
使われ方：反映像の対象同型による表現対象の移送。 -/
def representablePresheafIsoOfVertexIso {C : SSet.{u}} [Quasicategory C]
    {x y : C _⦋0⦌} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso x y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representablePresheafInfinity x) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representablePresheafInfinity y) := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.uliftVertexIso.{u, u + 1} e) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap C)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap_vertex, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap_vertex] at h
  exact h

/-- 概要：小さい空間値前層の表現可能性は全関手同型で不変。
方針：同じ指定宇宙変更へ自然同型を送り、構成済みの表現同型へ合成する。
規約：元の表現対象は変更しない。
使われ方：反射の余単位と同値模型の比較。 -/
lemma IsRepresentableSmallSpaceFunctor.of_functorIso {C : SSet.{u + 1}}
    [Quasicategory C] {F G : C.op ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}}
    (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.IsRepresentableSmallSpaceFunctor F) (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso F G) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.IsRepresentableSmallSpaceFunctor G := by
  obtain ⟨x, ⟨h⟩⟩ := hF
  exact ⟨x, ⟨h ≪≫ (e.ulift.{u + 1, u + 2}).postcomp _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.spaceUniverseDiagram⟩⟩

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.IsRepresentableSmallSpaceFunctor export _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsRepresentableSmallSpaceFunctor (of_functorIso)


/-- 概要：充満忠実な関手に沿う元の表現可能前層の制限は元の全 Hom と自然同型。
方針：全二変数の Yoneda 制限比較を指定対象で評価する。
規約：同じ関手 f の元の像の対象を保持する。
使われ方：同値による表現可能性の移送。 -/
def fullyFaithfulRepresentableRestrictionIso {C D : SSet.{u}}
    [Quasicategory C] [Quasicategory D] (f : C ⟶ D) (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful f)
    (x : C _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representablePresheafInfinity x)
      ((SSet.uliftFunctor.{u + 1, u}).map (SSet.opFunctor.map f) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representablePresheafInfinity (f.app (Opposite.op ⦋0⦌) x)) := by
  have e := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.FullyFaithfulJointHom.yonedaInfinityMap_fullyFaithfulRestrictionIso f hf).app (ULift.up x)
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap C).app _ (ULift.up x))
    ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.presheafHomWeightDiagram f).app _ (ULift.up (f.app _ x))) at e
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap_vertex, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.presheafHomWeightDiagram_vertex] at e
  exact e

/-- 概要：充満忠実な関手の本質的な像に表現対象があれば制限前層も表現可能。
方針：対象同型と充満忠実な全 Hom 比較を元の表現同型へ合成する。
規約：像への所属は全頂点同型で明示する。
使われ方：反映模型からの局所な表現対象の下降。 -/
lemma isRepresentable_restriction_of_essentialImage {C D : SSet.{u + 1}}
    [Quasicategory C] [Quasicategory D] (i : C ⟶ D) (hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful i)
    (F : D.op ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) (x : C _⦋0⦌) (z : D _⦋0⦌)
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (i.app (Opposite.op ⦋0⦌) x) z)
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representablePresheafInfinity z)
      ((SSet.uliftFunctor.{u + 2, u + 1}).map F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.spaceUniverseDiagram)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.IsRepresentableSmallSpaceFunctor (SSet.opFunctor.map i ≫ F) := by
  refine ⟨x, ⟨?_⟩⟩
  have hc := fullyFaithfulRepresentableRestrictionIso i hi x ≪≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp (representablePresheafIsoOfVertexIso e ≪≫ h)
      ((SSet.uliftFunctor.{u + 2, u + 1}).map (SSet.opFunctor.map i)))
  simpa only [CategoryTheory.Functor.map_comp, Category.assoc] using hc

/-- 概要：元の圏同値による制限が表現可能なら元の小さい空間値前層も表現可能。
方針：表現対象を同じ同値で送り、前合成の充満忠実性で全自然同型を戻す。
規約：同値を抽象的な Hom 集合の全単射へ置き換えない。
使われ方：反映された Ind 模型から元の presentable 圏への移送。 -/
lemma isRepresentable_of_equivalence_restriction {C D : SSet.{u + 1}}
    [Quasicategory C] [Quasicategory D] (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence C D)
    (F : D.op ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.IsRepresentableSmallSpaceFunctor (SSet.opFunctor.map e.hom ≫ F)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.IsRepresentableSmallSpaceFunctor F := by
  obtain ⟨x, ⟨h⟩⟩ := hF
  refine ⟨e.hom.app (Opposite.op ⦋0⦌) x, ?_⟩
  have hi := (fullyFaithfulRepresentableRestrictionIso e.hom
    e.isQCatEquivalence.isFullyFaithful x).symm ≪≫ h
  simp only [CategoryTheory.Functor.map_comp, Category.assoc] at hi
  have he := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.IsQCatEquivalence.ulift.{u + 1, u + 2} e.isQCatEquivalence.opposite
  have hp := he.isPrecompositionEquivalence _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u + 1}
  exact ⟨hp.isFullyFaithful.preimageVertexIso hi⟩

/-- 概要：元の圏同値による制限は小さい空間値前層の表現可能性を保ち反映する。
方針：存在する表現対象を本質的全射性で移し、逆方向は前合成同値で戻す。
規約：元の全表現同型と同じ宇宙を保持する。
使われ方：presentable 圏の Ind 模型を選んだ表現可能性の判定。 -/
lemma isRepresentable_iff_equivalence_restriction {C D : SSet.{u + 1}}
    [Quasicategory C] [Quasicategory D] (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence C D)
    (F : D.op ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.IsRepresentableSmallSpaceFunctor F ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.IsRepresentableSmallSpaceFunctor (SSet.opFunctor.map e.hom ≫ F) := by
  constructor
  · rintro ⟨z, ⟨hz⟩⟩
    exact isRepresentable_restriction_of_essentialImage e.hom
      e.isQCatEquivalence.isFullyFaithful F (e.inv.app _ z) z (e.invHomIso.app z) hz
  · exact isRepresentable_of_equivalence_restriction e F

/-- 概要：圏同値による制限は小余極限を小極限へ送る条件を保ち反映する。
方針：同値の両方向の余極限保存と元の全合成同型を使う。
規約：元の小さい形状全体の保存性を扱う。
使われ方：反映 Ind 模型上の表現可能性から一般の圏へ戻す。 -/
lemma sendsSmallColimitsToLimits_iff_equivalence_restriction {C D : SSet.{u + 1}}
    [Quasicategory C] [Quasicategory D] (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence C D)
    (F : D.op ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.SendsSmallColimitsToLimits F ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.SendsSmallColimitsToLimits (SSet.opFunctor.map e.hom ≫ F) := by
  constructor
  · intro h
    exact h.precomp_op e.hom (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.equivalence_preservesSmallColimits e.isQCatEquivalence)
  · intro h
    have hr := h.precomp_op e.inv (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.equivalence_preservesSmallColimits e.symm.isQCatEquivalence)
    apply hr.of_functorIso
    have hi := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp e.invHomIso.op F
    simpa only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id,
      Category.id_comp, Category.assoc] using hi

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
