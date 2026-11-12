module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PullbackVertexCandidates
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.SlicePostcompEquivalenceLifting
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialRestrictionBaseEvaluation

/-!
概要：元の引き戻し図式の両成分の全余錐を、像の全余錐同型から貼り合わせる。
方針：coslice 後合成の同値持ち上げで全余錐の整合を厳密化し、join 射を引き戻す。
規約：余極限性や第二脚の保存を要求しない。
使われ方：fiber の μ-small 試験図式の全余錐を構成する。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：第二成分の全余錐を第一成分像と同じ固定図式へ送る。
方針：後合成した元の全余錐の値と引き戻しの可換式を使う。
規約：全単体パラメータを保持する。
使われ方：成分余錐の同型の共通の標的。 -/
def pullbackCoconeBaseMap {E D B K : SSet.{u}} (p : E ⟶ B) (q : D ⟶ B)
    (r : K ⟶ pullback p q) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (r ≫ pullback.snd p q) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder ((r ≫ pullback.fst p q) ≫ p) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp (r ≫ pullback.snd p q) q ≫ eqToHom (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (by
    simp only [Category.assoc, pullback.condition]))

/-- 概要：全余錐の底の表示を合わせても元の join 射の後合成値は変わらない。
方針：固定図式の等号移送を各全族の uncurry で除く。
規約：全射の厳密な等式。
使われ方：貼り合わせの可換条件の回収。 -/
lemma pullbackCoconeBaseMap_uncurry {E D B K A : SSet.{u}}
    (p : E ⟶ B) (q : D ⟶ B) (r : K ⟶ pullback p q)
    (a : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (r ≫ pullback.snd p q)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry (a ≫ pullbackCoconeBaseMap p q r) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry a ≫ q := by
  have hbase : (r ≫ pullback.snd p q) ≫ q = (r ≫ pullback.fst p q) ≫ p := by
    simp only [Category.assoc, pullback.condition]
  rw [pullbackCoconeBaseMap, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.sliceUnderUncurry_eqToHom hbase, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_postcomp]

/-- 概要：第二成分余錐の底の表示移送は元の全余錐値の後合成。
方針：頂点の Yoneda 表示へ全 uncurry の等式を適用する。
規約：全余錐値の等式。
使われ方：余錐頂点と元の成分図式の比較。 -/
lemma pullbackCoconeBaseMap_val {E D B K : SSet.{u}}
    (p : E ⟶ B) (q : D ⟶ B) (r : K ⟶ pullback p q)
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (r ≫ pullback.snd p q)) :
    ((pullbackCoconeBaseMap p q r).app (Opposite.op ⦋0⦌) c).val = c.val ≫ q := by
  have h := pullbackCoconeBaseMap_uncurry p q r (SSet.yonedaEquiv.symm c)
  rw [SSet.yonedaEquiv_symm_comp c (pullbackCoconeBaseMap p q r),
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceUnderUncurry_yoneda, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceUnderUncurry_yoneda] at h
  exact h

/-- 概要：第二成分余錐の共通底上の頂点は元の頂点の像そのもの。
方針：全余錐値を右点へ制限する。
規約：元の実頂点の厳密な等式。
使われ方：両成分の像の終対象性の移送。 -/
lemma pullbackCoconeBaseMap_vertex {E D B K : SSet.{u}}
    (p : E ⟶ B) (q : D ⟶ B) (r : K ⟶ pullback p q)
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (r ≫ pullback.snd p q)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex (p := (r ≫ pullback.fst p q) ≫ p)
      ((pullbackCoconeBaseMap p q r).app (Opposite.op ⦋0⦌) c) =
        q.app (Opposite.op ⦋0⦌) c.vertex := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex_eq, pullbackCoconeBaseMap_val, ← Category.assoc,
    SSet.yonedaEquiv_comp]
  rfl

/-- 概要：像の全余錐が同型な両成分から、元の引き戻し図式の全余錐を得る。
方針：coslice 内で同値を持ち上げて元の全 join 射を引き戻す。
規約：第二成分の余錐を厳密に保持し、第一成分は全 coslice 内で同型。
使われ方：compact 始域の成分余錐を元の fiber の全試験余錐へ戻す。 -/
lemma exists_pullbackCocone_of_compatible_components
    {E D B : SSet.{u + 1}} [Quasicategory E] [Quasicategory D] [Quasicategory B]
    {K : SSet.{u + 1}} (p : E ⟶ B) (q : D ⟶ B) (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting p)
    (r : K ⟶ pullback p q)
    (cE : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (r ≫ pullback.fst p q))
    (cD : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (r ≫ pullback.snd p q))
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso ((pullbackCoconeBaseMap p q r).app (Opposite.op ⦋0⦌) cD)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp (r ≫ pullback.fst p q) p).app (Opposite.op ⦋0⦌) cE)) :
    ∃ c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone r,
      Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (r ≫ pullback.fst p q))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone (pullback.fst p q) c) cE) ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone (pullback.snd p q) c = cD := by
  let P := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp (r ≫ pullback.fst p q) p
  let Q := pullbackCoconeBaseMap p q r
  have hP : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting P := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.sliceUnderPostcomp_equivalenceLifting _ p hp
  let w := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pullbackVertexCandidate P Q hP cE cD e
  let ce := (pullback.fst P Q).app (Opposite.op ⦋0⦌) w.vertex
  let cd := (pullback.snd P Q).app (Opposite.op ⦋0⦌) w.vertex
  have hc : P.app (Opposite.op ⦋0⦌) ce = Q.app (Opposite.op ⦋0⦌) cd :=
    ConcreteCategory.congr_hom (NatTrans.congr_app (pullback.condition (f := P) (g := Q))
      (Opposite.op ⦋0⦌)) w.vertex
  have hc' : ce.val ≫ p = cd.val ≫ q := by
    have hQ := pullbackCoconeBaseMap_uncurry p q r (SSet.yonedaEquiv.symm cd)
    have hy : SSet.yonedaEquiv.symm cd ≫ Q =
        SSet.yonedaEquiv.symm (Q.app (Opposite.op ⦋0⦌) cd) :=
      SSet.yonedaEquiv_symm_comp cd Q
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry (SSet.yonedaEquiv.symm cd ≫ Q) = _ at hQ
    rw [hy, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceUnderUncurry_yoneda, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceUnderUncurry_yoneda] at hQ
    have h := congrArg (fun z : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder ((r ≫ pullback.fst p q) ≫ p)) _⦋0⦌ ↦ z.val) hc
    change ce.val ≫ p = _ at h
    exact h.trans hQ
  let c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone r := ⟨pullback.lift ce.val cd.val hc', by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst]
      exact ce.property
    · rw [Category.assoc, pullback.lift_snd]
      exact cd.property⟩
  have hce : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone (pullback.fst p q) c = ce := by
    apply Subtype.ext
    exact pullback.lift_fst _ _ _
  have hcd : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone (pullback.snd p q) c = cd := by
    apply Subtype.ext
    exact pullback.lift_snd _ _ _
  refine ⟨c, ?_, ?_⟩
  · rw [hce]
    exact ⟨w.fstIso⟩
  · rw [hcd]
    exact w.snd_eq

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
