module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalMappingOpposite
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorOppositeHom
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.QCatEquivalenceOpposite
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianIntervalPrecomposition

/-!
概要：区間写像空間の反転同型と、元の標準の前後合成とのホモトピー整合。
方針：族の反転を h Fun の反対 Hom 同値と照合し、前合成から後合成へ同値性を移す。
規約：元の辺と標準の合成作用を保持。使われ方：Cartesian 辺による写像空間の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
variable {X : SSet.{u}} (x y : X _⦋0⦌)

/-- 区間写像空間の反転は、両端を交換した反対圏の区間模型と同型である。 -/
def intervalOppositeIso : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y).op ≅
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (X := X.op) (SSet.opObjEquiv.symm y) (SSet.opObjEquiv.symm x) := by
  let M := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y
  let N := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (X := X.op) (SSet.opObjEquiv.symm y) (SSet.opObjEquiv.symm x)
  let R : M.op ⟶ N := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalReverseFamily (𝟙 M)
  let U : N.op ⟶ M := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalUnreverseFamily (A := N.op)
    (SSet.opFunctorCompOpFunctorIso.app N).hom
  let I : N ⟶ M.op := (SSet.opFunctorCompOpFunctorIso.app N).inv ≫ SSet.opFunctor.map U
  have hU : SSet.opFunctor.map U ≫ R = (SSet.opFunctorCompOpFunctorIso.app N).hom := by
    calc
      _ = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalReverseFamily U := by
        simpa only [Category.comp_id] using (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalReverseFamily_precomp U (𝟙 M)).symm
      _ = _ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalReverseFamily_unreverse _
  have hRn : (SSet.opFunctorCompOpFunctorIso.app M).inv ≫ SSet.opFunctor.map R ≫ U = 𝟙 M := by
    let i := (SSet.opFunctorCompOpFunctorIso.app M).inv ≫ SSet.opFunctor.map R
    have hi : SSet.opFunctor.map i ≫ (SSet.opFunctorCompOpFunctorIso.app N).hom = R := by rfl
    change i ≫ U = 𝟙 M
    calc
      _ = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalUnreverseFamily
          (SSet.opFunctor.map i ≫ (SSet.opFunctorCompOpFunctorIso.app N).hom) :=
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalUnreverseFamily_precomp i (SSet.opFunctorCompOpFunctorIso.app N).hom).symm
      _ = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalUnreverseFamily R := congrArg (fun f ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalUnreverseFamily f) hi
      _ = _ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalUnreverseFamily_reverse (𝟙 M)
  have hR : SSet.opFunctor.map R ≫ U = (SSet.opFunctorCompOpFunctorIso.app M).hom := by
    apply (cancel_epi (SSet.opFunctorCompOpFunctorIso.app M).inv).mp
    rw [Iso.inv_hom_id]
    exact hRn
  have hI : SSet.opFunctor.map I ≫ (SSet.opFunctorCompOpFunctorIso.app M).hom = U := by rfl
  have : SSet.opFunctor.{u}.IsEquivalence := SSet.opEquivalence.isEquivalence_functor
  refine ⟨R, I, ?_, ?_⟩
  · apply SSet.opFunctor.map_injective
    apply (cancel_mono (SSet.opFunctorCompOpFunctorIso.app M).hom).mp
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id,
      Category.assoc, hI, hR, Category.id_comp]
  · change ((SSet.opFunctorCompOpFunctorIso.app N).inv ≫ SSet.opFunctor.map U) ≫ R = _
    rw [Category.assoc, hU, Iso.inv_hom_id]
    rfl

/-- 族の反転が、元の h Fun の反対 Hom 同値と一致する。 -/
lemma intervalReverseFamily_hom {A : SSet.{u}} [Quasicategory X]
    (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalReverseFamily f) =
      _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorOppositeHomEquiv (SSet.const x : A ⟶ X) (SSet.const y)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom f) := by
  change SSet.Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHomotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalReverseFamily f))) =
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorOppositeHomEquiv _ _
      (SSet.Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHomotopy f)))
  rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorOppositeHomEquiv_homotopy]
  congr 1
  apply SSet.Truncated.Edge.ext
  change SSet.yonedaEquiv (curry (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHomotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalReverseFamily f)).h) =
    SSet.yonedaEquiv (curry (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.homotopyOpposite (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHomotopy f)).h)
  congr 2
  change (β_ A.op (Δ[1] : SSet.{u})).hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalReverseFamily f) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalReverseFamily_uncurry]
  rfl

/-- 元の辺を、任意のパラメータ上の定値関手間の辺に移す。 -/
def constantFunctorEdge {A E : SSet.{u}} {x y : E _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj E) x y) :
    SSet.Truncated.Edge (X := (truncation 2).obj ((ihom A).obj E))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const x : A ⟶ E)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const y : A ⟶ E)) :=
  ⟨(f.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap A E))).edge,
    (f.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap A E))).src_eq.trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap_vertex A x),
    (f.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap A E))).tgt_eq.trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap_vertex A y)⟩

/-- 定値関手による Hom の作用は、元の辺の代表と整合する。 -/
lemma constantFunctorHomMap_homMk {A E : SSet.{u}} {x y : E _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj E) x y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap A (SSet.Truncated.HomotopyCategory.homMk f) =
      SSet.Truncated.HomotopyCategory.homMk (constantFunctorEdge (A := A) f) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.homMk_transport (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap_vertex A x) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap_vertex A y)
    (f.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap A E))) (constantFunctorEdge f) rfl

/-- 定値関手による元の辺の像は、反対 Hom 同値と整合する。 -/
lemma constantFunctorHomMap_op_homMk {A E : SSet.{u}} [Quasicategory E] {x y : E _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj E) x y) :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorOppositeHomEquiv (SSet.const x : A ⟶ E) (SSet.const y)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap A (SSet.Truncated.HomotopyCategory.homMk f)) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap A.op (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.edgeOp f)) := by
  rw [constantFunctorHomMap_homMk, constantFunctorHomMap_homMk]
  simp only [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorOppositeHomEquiv, Equiv.trans_apply,
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.homotopyCategoryOpHomEquiv_homMk, Iso.homCongr_apply, eqToIso.inv, eqToIso.hom]
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.homMk_transport (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.oppositeInternalHom_vertex (SSet.const y : A ⟶ E))
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.oppositeInternalHom_vertex (SSet.const x : A ⟶ E))
  apply CategoryTheory.Functor.functorHom_ext
  intro n α
  apply ConcreteCategory.hom_ext
  intro a
  change (((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.OppositeInternalHom.oppositeInternalHomIso A E).hom.app (Opposite.op ⦋1⦌)
    (SSet.opObjEquiv.symm (constantFunctorEdge (A := A) f).edge)).app n α) a = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.oppositeInternalHom_apply]
  rfl

/-- 元の後合成を反転した族は、反対圏の標準の前合成とホモトピックである。 -/
lemma intervalReverseFamily_postcompose_hom {E : SSet.{u}} [Quasicategory E]
    (x : E _⦋0⦌) {y z : E _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj E) y z) :
    Nonempty (SSet.Homotopy
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalReverseFamily (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalPostcompose x (SSet.Truncated.HomotopyCategory.homMk f)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalReverseFamily (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y)) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalPrecompose (SSet.opObjEquiv.symm x)
          (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.edgeOp f)))) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom_eq_imp_homotopy
  rw [intervalReverseFamily_hom, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalPostcompose_hom,
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorOppositeHomEquiv_comp, constantFunctorHomMap_op_homMk,
    ← intervalReverseFamily_hom, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalPrecompose_family]

/-- 任意の族の反転は、元の写像の反転と標準の反転同型の合成である。 -/
lemma intervalReverseFamily_eq {A : SSet.{u}} (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalReverseFamily f = SSet.opFunctor.map f ≫ (intervalOppositeIso x y).hom := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalReverseFamily f = SSet.opFunctor.map f ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalReverseFamily (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y))
  simpa only [Category.comp_id] using (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalReverseFamily_precomp f (𝟙 _))

/-- 反対写像の圏同値性から元の写像の圏同値性を回収する。 -/
lemma isQCatEquivalence_of_op {A B : SSet.{u}} [Quasicategory A] [Quasicategory B]
    (f : A ⟶ B) (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (SSet.opFunctor.map f)) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence f := by
  have hff := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_op hf
  let α : A ≅ A.op.op := (SSet.opFunctorCompOpFunctorIso.app A).symm
  let β : B.op.op ≅ B := SSet.opFunctorCompOpFunctorIso.app B
  have hi := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso α).isQCatEquivalence
  have hj := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso β).isQCatEquivalence
  have h := hi.comp (hff.comp hj)
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (α.hom ≫ SSet.opFunctor.map (SSet.opFunctor.map f) ≫ β.hom) at h
  have he : α.hom ≫ SSet.opFunctor.map (SSet.opFunctor.map f) ≫ β.hom = f := by rfl
  rw [he] at h
  exact h

/-- 反対の辺の前合成の同値性を、元の指定辺の後合成へ移す。 -/
lemma intervalPostcompose_isSimplicialHomotopyEquivalence_of_op_precompose
    {E : SSet.{u}} [Quasicategory E] (x : E _⦋0⦌) {y z : E _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj E) y z)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalPrecompose (SSet.opObjEquiv.symm x)
      (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.edgeOp f)))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalPostcompose x (SSet.Truncated.HomotopyCategory.homMk f)) := by
  obtain ⟨H⟩ := intervalReverseFamily_postcompose_hom x f
  have hr := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (intervalOppositeIso x y)).isQCatEquivalence
  have ht := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (intervalOppositeIso x z)).isQCatEquivalence
  have hc := (hr.comp hf.isQCatEquivalence).ofFunctorIso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorIsoOfSimplicialHomotopy H).symm
  rw [intervalReverseFamily_eq] at hc
  exact (isQCatEquivalence_of_op _ (ht.cancel_right hc)).isSimplicialHomotopyEquivalence

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
