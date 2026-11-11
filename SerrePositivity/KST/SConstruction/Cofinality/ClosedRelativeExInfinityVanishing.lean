module
public import SerrePositivity.KST.SConstruction.Cofinality.ClosedRelativeVanishing
public import SerrePositivity.EInfinity.FrameHom.AnodyneWeakDetection

/-!
概要：同じ本質像の相対実現の Ex∞ 模型でも二次以上のホモトピーは一意。
方針：元の Ex∞ 単位の弱同値と連続 Kan 置換のホモトピー逆で実消滅を移す。
規約：任意の基点を保ち、代表頂点の全射性を仮定しない。
使われ方：相対 fiber の Kan 四角形と長完全列への接続。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction.Cofinality
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open SerrePositivity.SimplicialModel

open scoped Simplicial

/-- 概要：元の本質像の相対実現の Ex∞ の二次以上のホモトピーは一意。
方針：連続 Kan 置換後の Ex∞ 単位の実ホモトピー逆を使い、二つの π 単射で引き戻す。
規約：基点の選び直しや主共終性の仮定を使わない。
使われ方：元の相対 fiber 比較を Kan 完全列へ渡す右項。 -/
theorem completionClosedRelativeExInfinity_higher_subsingleton (r : ℕ)
    (ι : Fin r → SimplexCategoryᵒᵖ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) (n : ℕ) (hn : 1 < n)
    (x : (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.obj (Fibration.Relative.closedRelativeRealization
      (completionImageClosedPredicate r ι f hf))) _⦋0⦌) :
    Subsingleton (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.obj (Fibration.Relative.closedRelativeRealization
        (completionImageClosedPredicate r ι f hf))) n x) := by
  let R := Fibration.Relative.closedRelativeRealization (completionImageClosedPredicate r ι f hf)
  let : KanComplex ((𝟭 SSet.{u}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.obj R)) := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity_kanComplex R
  have hu : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app R) :=
    SerrePositivity.EInfinity.FrameHom.AnodyneWeakDetection.isWeakHomotopyEquivalence _
      (SSet.anodyneExtensions.Q_inverts _ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit_anodyne R))
  have hw := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.continuousKanReplacement_map_isWeakHomotopyEquivalence _ hu
  obtain ⟨g, hg, hk⟩ := hw.isSimplicialHomotopyEquivalence
  have hgi : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence g := ⟨_, hk, hg⟩
  have hπg : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism
      (g : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.obj R) ⟶
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj R) :=
    Spectra.kanPiIsomorphism_of_qCatEquivalence g hgi.isQCatEquivalence
  let z := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.obj R)).app (Opposite.op ⦋0⦌) x
  let : Subsingleton (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj ((𝟭 SSet.{u}).obj R)) n
      (g.app (Opposite.op ⦋0⦌) z)) :=
    completionClosedRelative_higher_subsingleton r ι f hf n hn _
  let : Subsingleton (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.obj R)) n z) :=
    Function.Injective.subsingleton ((hπg z n).1)
  have hv := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.continuousKanReplacementUnit_isWeakHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.obj R)
  have hπu : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.obj R) :
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.obj R ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.obj R)) :=
    Spectra.kanPiIsomorphism_of_qCatEquivalence _
      hv.isSimplicialHomotopyEquivalence.isQCatEquivalence
  exact Function.Injective.subsingleton ((hπu x n).1)

end SerrePositivity.KST.SConstruction.Cofinality
