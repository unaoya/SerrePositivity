module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.Cocone
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.Equivalence
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.EquivalenceAllLimits
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.EquivalenceLimits
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FunctorEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.FunctorLimits
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.FunctorPointwiseLimitCriterion
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.FunctorPointwiseLimitExistence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoreLimit
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.Opposite
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PrecompositionTensor
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TerminalMap
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CosliceOpposite
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.RelativeCoconeAbsolute
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeCoconeOppositeExistence
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CoconeReversePostcomp
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.ConeValEquality
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CatInfinity.OppositeFunctorEvaluation
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.DiagramComparisons.OppositeInternalHom

/-!
概要：点ごとの余極限の存在から関手圏の点ごとの余極限余錐を作る。
方針：指定評価を保つ反転同型で極限の存在へ移し、元の余錐へ戻す。
規約：元の図式と全ての評価点での普遍性を保持する。
使われ方：矢印圏の余極限錐と lax pullback の存在構成。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open _root_.CategoryTheory MonoidalClosed _root_.SSet
open scoped _root_.Simplicial
namespace SerrePositivity.InfinityCategories.HTT.Section5_1_2

/-- 概要：各評価図式が余極限を持てば、全評価が余極限となる関手圏の余極限錐が存在する。
方針：反転した内部 Hom の点ごとの極限錐を作り、元の余錐の全射性で戻す。
規約：元の図式 r を厳密に固定する。
使われ方：Tamme Lemma 8(i) の矢印成分の存在。 -/
lemma exists_colimitCone_functor_of_pointwise {J K C : SSet.{u}} [Quasicategory C]
    (r : J ⟶ (ihom K).obj C)
    (hp : ∀ k : K _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.evaluateFunctorDiagram r k)) :
    ∃ c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone r, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c ∧ ∀ k : K _⦋0⦌,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanPostcomposeCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt k) c) := by
  let e := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.OppositeInternalHom.oppositeInternalHomIso K C
  let r' := SSet.opFunctor.map r ≫ e.hom
  have hr : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasPointwiseLimits r' := by
    intro k'
    obtain ⟨k, rfl⟩ := SSet.opObjEquiv.symm.surjective k'
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit ((SSet.opFunctor.map r ≫ e.hom) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (SSet.opObjEquiv.symm k))
    have he : (SSet.opFunctor.map r ≫ e.hom) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (SSet.opObjEquiv.symm k) =
          SSet.opFunctor.map (r ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt k) := by
      rw [Category.assoc]
      change _ ≫ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.OppositeInternalHom.oppositeInternalHomIso K C).hom ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (SSet.opObjEquiv.symm k) = _
      rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CatInfinity.oppositeInternalHom_evaluate, CategoryTheory.Functor.map_comp]
    rw [he]
    obtain ⟨ck, hck⟩ := hp k
    exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeReverseCone ck, (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isColimitCone_iff_reverseCone ck).1 hck⟩
  obtain ⟨d, hd⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.exists_pointwiseLimitCone r' hr
  have hback : r' ≫ e.inv = SSet.opFunctor.map r := by
    dsimp only [r']
    rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  let d' := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone e.inv d).cast hback
  have hd' : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone d' :=
    (((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso e.symm).isLimitCone_iff d).1
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isLimitCone_of_pointwise d hd)).cast hback
  obtain ⟨c, hc⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanCoconeReverseCone_surjective r d'
  have hval : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeReverseCone c).val ≫ e.hom = d.val := by
    rw [hc]
    change (d.val ≫ e.inv) ≫ e.hom = d.val
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  refine ⟨c, (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isColimitCone_iff_reverseCone c).2 (hc.symm ▸ hd'), ?_⟩
  intro k
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.isLimitCone_reverse_postcomp_iff c (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt k)).1
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.isLimitCone_iff_of_cone_val_eq _ _ ?_).2 (hd (SSet.opObjEquiv.symm k))
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeReverseCone c).val ≫ SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt k) =
    d.val ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (SSet.opObjEquiv.symm k)
  rw [← hval, Category.assoc]
  change _ = _ ≫ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.OppositeInternalHom.oppositeInternalHomIso K C).hom ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (SSet.opObjEquiv.symm k)
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CatInfinity.oppositeInternalHom_evaluate]

end SerrePositivity.InfinityCategories.HTT.Section5_1_2

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "5.1.2.2" (partial := special) "仮定：Cartesian ファイブレーションと切断準圏の図式が各繊維で余極限を持つ（Lean が強い：一定準圏を一点から引き戻した射影の場合）。結論：この切断準圏を底上の相対関手空間の同型で関手準圏に同定し、同じ図式の点ごとの余極限余錐の存在と、任意の余錐の余極限性の点ごとの判定を得る（一致する場合。一般の Cartesian ファイブレーションは含まない）。"] _root_.SerrePositivity.InfinityCategories.HTT.Section5_1_2.exists_colimitCone_functor_of_pointwise
attribute [cite HTT "5.1.2.3"] _root_.SerrePositivity.InfinityCategories.HTT.Section5_1_2.exists_colimitCone_functor_of_pointwise
