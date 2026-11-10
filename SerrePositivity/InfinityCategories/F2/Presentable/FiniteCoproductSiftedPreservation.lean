module

public import SerrePositivity.InfinityCategories.F2.Presentable.CoproductRealizationPreservation
public import SerrePositivity.InfinityCategories.F2.Presentable.CoproductFromFiniteSubsets

/-!
概要：有限余積と sifted 余極限の保存から全小余極限保存を導く。
方針：有限部分集合の filtered 余極限で小余積を作り、一般 bar 保存判定へ渡す。
規約：空の有限余積を含み、指定全余錐を保つ。
使われ方：P_Σ の全余極限保存判定の一般部。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits Ind

/-- 概要：元の全有限余積を保つ条件。
方針：有限離散形状の元の指定全余錐の像を量化する。
規約：空添字を含む。
使われ方：全小余極限保存の有限条件。 -/
def PreservesFiniteCoproducts {X Y : SSet.{u + 1}} (U : X ⟶ Y) : Prop :=
  ∀ (I : Type u) [Finite I]
    (p : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (Discrete I)) ⟶ X)
    (c : JoinCocone p), IsColimitCone c → IsColimitCone (mapJoinCocone U c)

/-- 概要：有限余積と filtered 余極限の保存から小余積保存を得る。
方針：有限部分集合族の局所有限余積とその filtered 余極限を保存する。
規約：元の指定小余積余錐の像を結論に保持する。
使われ方：全小余極限保存判定の小余積段階。 -/
lemma preservesSmallCoproducts_of_finite_filtered
    {X Y : SSet.{u + 1}} [Quasicategory X] [Quasicategory Y]
    (hX : HasSmallCoproducts X) (U : X ⟶ Y) (hfin : PreservesFiniteCoproducts U)
    (hfilter : PreservesSmallKappaFilteredColimits Cardinal.aleph0 U) :
    PreservesSmallCoproducts U := by
  intro I F c hc
  let Z := finiteSubsetFamily I
  let q := (SSet.uliftFunctor.{u + 1, u}).map (nerveMap (finiteSubsetForget I))
  have hq := Ind.isRightCofinal_ulift (nerveMap (finiteSubsetForget I))
    (finiteSubsetForget_nerve_isRightCofinal I)
  have hcq := (isColimitCone_iff_restrict_rightCofinal q hq c).mp hc
  apply (isColimitCone_iff_restrict_rightCofinal q hq (mapJoinCocone U c)).mpr
  apply colimitPreservation_of_localLeftKan
    ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (Functor.Elements.π Z))) (q ≫ F) U
    (elementsCoproduct_leftKanDiagram_hasColimit Z hX _) ?_ ?_ (c.restrict q) hcq
  · intro v d hd
    rcases v with ⟨v⟩
    obtain ⟨s, rfl⟩ := nerveEquiv.symm.surjective v
    have : Finite (Z.obj s) := by
      change Finite {i // i ∈ s}
      infer_instance
    let a := elementsCoproductKanComparison Z s
    have ha := elementsCoproductKanComparison_isRightCofinal Z s
    apply (isColimitCone_iff_restrict_rightCofinal a ha (mapJoinCocone U d)).mpr
    exact hfin _ _ (d.restrict a) ((isColimitCone_iff_restrict_rightCofinal a ha d).mp hd)
  · have : IsKappaFiltered Cardinal.aleph0 (nerve (Finset I)) :=
      (isKappaFiltered_aleph0_iff _).mpr (finiteSubset_isFilteredInfinity I)
    exact hfilter _

/-- 概要：有限余積と sifted 余極限を保つ関手は全小余極限を保つ。
方針：小余積保存を有限部分集合で導き、幾何学的実現と合わせる。
規約：始域に小余積の存在だけを要求する。
使われ方：P_Σ の全余極限保存判定。 -/
lemma preservesSmallColimits_of_finiteCoproducts_sifted
    {X Y : SSet.{u + 1}} [Quasicategory X] [Quasicategory Y]
    (hX : HasSmallCoproducts X) (U : X ⟶ Y) (hfin : PreservesFiniteCoproducts U)
    (hsift : PreservesSmallSiftedColimits U) : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits U :=
  preservesSmallColimits_of_coproducts_geometricRealizations hX U
    (preservesSmallCoproducts_of_finite_filtered hX U hfin
      (preservesSmallFiltered_of_sifted hsift)) (preservesSmallGeometric_of_sifted hsift)

/-- 概要：全小余極限保存は有限余積保存と sifted 保存に同値。
方針：十分条件と二種類の形状への制限を組み合わせる。
規約：始域の小余積存在を明示する。
使われ方：全小余極限保存の公開判定。 -/
lemma preservesSmallColimits_iff_finiteCoproducts_sifted
    {X Y : SSet.{u + 1}} [Quasicategory X] [Quasicategory Y]
    (hX : HasSmallCoproducts X) (U : X ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits U ↔ PreservesFiniteCoproducts U ∧ PreservesSmallSiftedColimits U :=
  ⟨fun h ↦ ⟨fun I _ p c hc ↦ h (nerve (Discrete I)) p c hc,
      fun I _ p c hc ↦ h I p c hc⟩,
    fun h ↦ preservesSmallColimits_of_finiteCoproducts_sifted hX U h.1 h.2⟩

end SerrePositivity.InfinityCategories.F2.Presentable
