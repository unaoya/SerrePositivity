module

public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.AdjunctionOpposite
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.AdjunctionFromHomRepresentation
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.RepresentabilityEquivalence

/-!
概要：反対関手の左随伴の存在を元の関手の右随伴へ戻す。
方針：二重反転の指定同型で元の向きの全関手を作り、既存の反対随伴を使う。
規約：元の関手を保持し、単位・余単位と両三角式を持つ全随伴を返す。
使われ方：反変 Hom の表現可能性から右随伴を構成する。

対応節は Kerodon 8.3（Tag 03LZ）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding

/-- 概要：反対圏の全共変 Hom は元の全反変 Hom と自然同型。
方針：二重反転の充満忠実な指定同型による全 Yoneda 制限比較を使う。
規約：元の対象 y と同じ宇宙を保持する。
使われ方：反変表現可能性を反対圏の共変表現可能性へ渡す。 -/
def oppositeCovariantRepresentableIso {C : SSet.{u}} [Quasicategory C] (y : C _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.covariantRepresentableInfinity (C := C.op) (SSet.opObjEquiv.symm y))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representablePresheafInfinity y) := by
  let e : C.op.op ≅ C := SSet.opFunctorCompOpFunctorIso.app C
  let x : C.op.op _⦋0⦌ := SSet.opObjEquiv.symm (SSet.opObjEquiv.symm y)
  have hx : e.hom.app (Opposite.op ⦋0⦌) x = y := rfl
  have he : (SSet.opFunctorCompOpFunctorIso.app C.op).inv ≫
      SSet.opFunctor.map e.hom = 𝟙 C.op := by
    ext n z
    rfl
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.fullyFaithfulRepresentableRestrictionIso e.hom
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso e).isQCatEquivalence.isFullyFaithful x)
    ((SSet.uliftFunctor.{u + 1, u}).map
      (SSet.opFunctorCompOpFunctorIso.app C.op).inv)
  rw [hx] at h
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.covariantRepresentableInfinity (C := C.op) (SSet.opObjEquiv.symm y))
    ((SSet.uliftFunctor.{u + 1, u}).map
      (SSet.opFunctorCompOpFunctorIso.app C.op).inv ≫
        (SSet.uliftFunctor.{u + 1, u}).map (SSet.opFunctor.map e.hom) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representablePresheafInfinity y) at h
  rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, he, CategoryTheory.Functor.map_id,
    Category.id_comp] at h
  exact h

/-- 概要：反対関手が右随伴なら元の関手は左随伴。
方針：反対側の左随伴を反転し、指定二重反転同型で端点を戻す。
規約：随伴の存在だけでなく元の二関手の全随伴を返す。
使われ方：右随伴の表現可能性判定の双対化。 -/
lemma exists_rightAdjoint_of_opposite_leftAdjoint
    {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y] (F : X ⟶ Y)
    (h : ∃ K : Y.op ⟶ X.op, Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction K (SSet.opFunctor.map F))) :
    ∃ R : Y ⟶ X, Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction F R) := by
  obtain ⟨K, ⟨a⟩⟩ := h
  let R := (SSet.opFunctorCompOpFunctorIso.app Y).inv ≫
    SSet.opFunctor.map K ≫ (SSet.opFunctorCompOpFunctorIso.app X).hom
  have he : SSet.opFunctor.map R = K := by
    ext n x
    rfl
  refine ⟨R, ⟨_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.qcatAdjunctionOfOpposite ?_⟩⟩
  rw [he]
  exact a

/-- 概要：各反変 Hom 合成が元の対象で表現可能なら元の関手は左随伴。
方針：同じ全 Hom 比較を反対圏の共変表現へ移し、comma 始対象からの随伴を戻す。
規約：右随伴関手・大域余単位を存在入力にしない。
使われ方：余極限保存から右随伴を構成する最後の接続。 -/
lemma exists_rightAdjoint_of_contravariantHom_representable
    {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y] (F : X ⟶ Y)
    (h : ∀ y : Y _⦋0⦌, ∃ x : X _⦋0⦌,
      Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representablePresheafInfinity x)
        ((SSet.uliftFunctor.{u + 1, u}).map (SSet.opFunctor.map F) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representablePresheafInfinity y))) :
    ∃ R : Y ⟶ X, Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction F R) := by
  apply exists_rightAdjoint_of_opposite_leftAdjoint F
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.exists_leftAdjoint_of_covariantHom_representable (SSet.opFunctor.map F)
  intro y
  obtain ⟨x, ⟨hx⟩⟩ := h (SSet.opObjEquiv y)
  refine ⟨SSet.opObjEquiv.symm x, ⟨?_⟩⟩
  have hy := (oppositeCovariantRepresentableIso (SSet.opObjEquiv y)).symm
  simp only [Equiv.symm_apply_apply] at hy
  exact oppositeCovariantRepresentableIso x ≪≫ hx ≪≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp hy
      ((SSet.uliftFunctor.{u + 1, u}).map (SSet.opFunctor.map F))

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
