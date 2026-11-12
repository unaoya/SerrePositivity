module
public import SerrePositivity.KST.SConstruction.Cofinality.RelativeFiberKanSquare
public import SerrePositivity.KST.Fibration.SpectrumZeroFromPositiveLevels

/-!
概要：本質像の元の全旗核の Ex∞ 模型の全ホモトピーは一意。
方針：供給側の実収縮と Ex∞ 単位の局所化可逆性を同じ一点射で消去する。
規約：相対 fiber の全旗自然性を仮定せず、元の核の実現を使う。
使われ方：元の Kan 四角形の fiber の高次消滅。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction.Cofinality
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open SerrePositivity.InfinityCategories
open SerrePositivity.SimplicialModel

open scoped Simplicial

/-- 概要：本質像の元の全旗核の Ex∞ の一点射は局所化同型。
方針：元の核の実収縮から一点射の可逆性を移し、Ex∞ 単位を消去する。
規約：相対 fiber 本体を仮定しない。
使われ方：元の核の全基点ホモトピーの自明性。 -/
lemma completionClosedKernelExInfinity_toPoint_isIso (r : ℕ)
    (ι : Fin r → SimplexCategoryᵒᵖ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) :
    IsIso (AnodyneHomotopy.anodyneQ.map
      (toUnit (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.obj (Fibration.Relative.closedKernelRealization
        (completionImageClosedPredicate r ι f hf))))) := by
  let E := Fibration.Relative.closedKernelRealization (completionImageClosedPredicate r ι f hf)
  let Q := AnodyneHomotopy.anodyneQ
  let t := isTerminalTensorUnit.uniqueUpToIso (terminalIsTerminal (C := SSet.{u}))
  have hE := Fibration.Relative.closedKernelRealization_toPoint_isIso
    (completionImageClosedPredicate r ι f hf)
  have ht : toUnit E ≫ t.hom = terminal.from E := terminal.hom_ext _ _
  have hc : IsIso (Q.map (toUnit E) ≫ Q.map t.hom) :=
    ((Q.map_comp _ _).symm.trans (congrArg Q.map ht)).symm ▸ hE
  have hE' : IsIso (Q.map (toUnit E)) := (isIso_comp_right_iff _ _).mp hc
  have hu : IsIso (Q.map (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app E)) := inferInstance
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app E ≫ toUnit (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.obj E) = toUnit E :=
    isTerminalTensorUnit.hom_ext _ _
  have hh : IsIso (Q.map (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app E) ≫ Q.map (toUnit (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.obj E))) :=
    ((Q.map_comp _ _).symm.trans (congrArg Q.map he)).symm ▸ hE'
  exact (isIso_comp_left_iff _ _).mp hh

/-- 概要：本質像の元の全旗核の Ex∞ の全基点ホモトピーは一意。
方針：既存の Kan 一点射の局所化比較へ同じ実収縮を代入する。
規約：零次を含む全実次数、任意の基点。
使われ方：元の相対 fiber 比較の可縮な角。 -/
lemma completionClosedKernelExInfinity_homotopy_subsingleton (r : ℕ)
    (ι : Fin r → SimplexCategoryᵒᵖ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) (n : ℕ)
    (x : (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.obj (Fibration.Relative.closedKernelRealization
      (completionImageClosedPredicate r ι f hf))) _⦋0⦌) :
    Subsingleton (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.obj (Fibration.Relative.closedKernelRealization
        (completionImageClosedPredicate r ι f hf))) n x) := by
  let : KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.obj (Fibration.Relative.closedKernelRealization
    (completionImageClosedPredicate r ι f hf))) := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity_kanComplex _
  exact Fibration.kanHomotopy_subsingleton_of_toPoint_localized_isIso _
    (completionClosedKernelExInfinity_toPoint_isIso r ι f hf) n x

end SerrePositivity.KST.SConstruction.Cofinality
