module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.PointEndpointEvaluation

/-!
概要：Kan 複体間の Kan fibration は指定端点を保つ可逆 path の相対境界を充填する。
方針：一点の評価と可逆 path の包含の同型で相対内部 Hom に移し、端点と境界の積を使う。
規約：両端の Kan 性と元の射の Kan fibration 性を明示する。
使われ方：Kerodon 4.5.3.24（Tag 02VM）、7.5.4.6（Tag 03BB） の strict fiber と導来ファイバーの比較。

対応節は Kerodon 4.5（Tag 01DE）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence

/-- 概要：可逆 path の指定端点の相対標的は、端点制限と p の相対内部 Hom の標的である。
方針：一点の関手空間の評価と可逆 path の包含の同型で pullback を移す。
規約：対象の Kan 性は可逆 path と通常の path の同型に使う。
使われ方：Kerodon 4.5.3.24（Tag 02VM） の相対充填を二変数随伴で移す表示。 -/
noncomputable def kanRelativePathPullbackObjObj {E B : SSet.{u}}
    [KanComplex E] [KanComplex B] (p : E ⟶ B) (j : Fin 2) :
    internalHom.PullbackObjObj (stdSimplex.δ j.rev : (Δ[0] : SSet.{u}) ⟶ Δ[1]) p where
  pt := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.relativeEquivalencePathTargetAt p j
  fst := pullback.snd (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint B j) p ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.pointFunctorEvaluationIso E).inv
  snd := pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint B j) p ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι B
  isPullback := by
    apply (IsPullback.of_hasPullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint B j) p).flip.of_iso
      (Iso.refl _) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.pointFunctorEvaluationIso E).symm (asIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι B))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.pointFunctorEvaluationIso B).symm
    · simp only [Iso.symm_hom, Iso.refl_hom, Category.id_comp]
    · simp only [Iso.refl_hom, Category.id_comp]
      rfl
    · exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.pointFunctorEvaluationIso_inv_naturality p).symm
    · apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.pointFunctorEvaluationIso B).hom).1
      change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint B j ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.pointFunctorEvaluationIso B).inv) ≫
          (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.pointFunctorEvaluationIso B).hom =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι B ≫
          (pre (stdSimplex.δ j.rev : (Δ[0] : SSet.{u}) ⟶ Δ[1])).app B) ≫
            (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.pointFunctorEvaluationIso B).hom
      rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc,
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.pointFunctorEvaluationIso_interval_pre]
      rfl

/-- 概要：可逆 path の相対写像を相対内部 Hom の標準写像と同定する。
方針：二つの pullback 射影で、指定端点の式と path の後合成の式を使う。
規約：始域の同型は既存の可逆 path の包含そのもの。
使われ方：Kerodon 4.5.3.24（Tag 02VM） の標準写像の持ち上げ性の移送。 -/
lemma relativeEquivalencePathMapAt_kan_pullbackObjObj {E B : SSet.{u}}
    [KanComplex E] [KanComplex B] (p : E ⟶ B) (j : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.relativeEquivalencePathMapAt p j =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι E ≫ (kanRelativePathPullbackObjObj p j).π := by
  let sq := kanRelativePathPullbackObjObj p j
  apply sq.hom_ext
  · rw [Category.assoc, sq.π_fst]
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.relativeEquivalencePathMapAt p j ≫
        (pullback.snd (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint B j) p ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.pointFunctorEvaluationIso E).inv) = _
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.relativeEquivalencePathMapAt_snd]
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint E j ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.pointFunctorEvaluationIso E).inv =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι E ≫
        (pre (stdSimplex.δ j.rev : (Δ[0] : SSet.{u}) ⟶ Δ[1])).app E
    apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.pointFunctorEvaluationIso E).hom).1
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.pointFunctorEvaluationIso_interval_pre]
    rfl
  · rw [Category.assoc, sq.π_snd]
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.relativeEquivalencePathMapAt p j ≫
        (pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint B j) p ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι B) = _
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.relativeEquivalencePathMapAt_fst, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathMap_ι]
    rfl

/-- 概要：Kan fibration の指定端点の相対可逆 path 写像は自明 Kan fibration。
方針：端点包含と境界の pushout-product の anodyne 性を二変数随伴で移す。
規約：元の始域と標的は Kan 複体、p は Kan fibration。
使われ方：Kerodon 4.5.3.24（Tag 02VM）、7.5.4.6（Tag 03BB） の導来ファイバーの比較の可縮な持ち上げ。 -/
lemma relativeEquivalencePathMapAt_trivialKanFibration_of_fibration {E B : SSet.{u}}
    [KanComplex E] [KanComplex B] (p : E ⟶ B) [Fibration p] (j : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.relativeEquivalencePathMapAt p j) := by
  let sq := kanRelativePathPullbackObjObj p j
  have hsq : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration sq.π := by
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibration_iff_boundary _).2
    intro n
    let P := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet.{u})
      (stdSimplex.δ j.rev : (Δ[0] : SSet.{u}) ⟶ Δ[1]) (boundary n).ι
    rw [← internalHomAdjunction₂.hasLiftingProperty_iff P sq]
    exact anodyneExtensions_pushoutObjObjι' P (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalEndpoint_anodyne j) p
      ((HomotopicalAlgebra.fibration_iff p).1 inferInstance)
  let e : Arrow.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.relativeEquivalencePathMapAt p j) ≅ Arrow.mk sq.π :=
    Arrow.isoMk (asIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι E)) (Iso.refl _)
      (by
        change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι E ≫ (kanRelativePathPullbackObjObj p j).π =
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.relativeEquivalencePathMapAt p j ≫ 𝟙 _
        rw [Category.comp_id]
        exact (relativeEquivalencePathMapAt_kan_pullbackObjObj p j).symm)
  exact ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibrations.arrow_mk_iso_iff e).mpr hsq.mem⟩

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
