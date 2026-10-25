module

public import SerrePositivity.InfinityCategories.F2.Ind.FiniteColimitPreservationGeneration
public import SerrePositivity.InfinityCategories.F2.Ind.LimitPreservationOpposite
public import SerrePositivity.InfinityCategories.F2.CatInfinity.CoconeReversePostcomp
public import SerrePositivity.InfinityCategories.F1.Joins.FiniteLimitGeneration
public import SerrePositivity.InfinityCategories.F1.Joins.PointConeSpanIso

/-!
概要：空形状と点 cospan の極限保存から、全有限単体集合形状の保存を導く。
方針：二重反転の自然性を保って、全余錐の保存を伴う有限生成を双対化する。
規約：元の指定極限錐の像を結論し、存在だけに弱めない。
使われ方：I-2 d′ の filtered 余極限関手の全有限極限保存。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 空錐と点 cospan の保存から、元の任意の有限形状の極限全錐の保存を得る。 -/
lemma map_isLimit_finite_of_empty_pointCospan {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] [HasFiniteLimits X] (U : X ⟶ Y)
    (he : ∀ (T : SSet.{u}) (p : (⊥ : T.Subcomplex).toSSet ⟶ X) (c : JoinCone p),
      IsLimitCone c → IsLimitCone (mapJoinCone U c))
    (hs : ∀ (p : pointConeSpan.{u}.op ⟶ X) (c : JoinCone p),
      IsLimitCone c → IsLimitCone (mapJoinCone U c))
    {K : SSet.{u}} [K.Finite] {p : K ⟶ X} (c : JoinCone p) (hc : IsLimitCone c) :
    IsLimitCone (mapJoinCone U c) := by
  let : HasFiniteLimits X.op.op := ⟨fun p ↦
    (hasLimit_iff_postcomp_isIso p (SSet.opFunctorCompOpFunctorIso.app X).hom).mpr
      (HasFiniteLimits.hasLimit (X := X) _)⟩
  have hcolim {A : SSet.{u}} [A.Finite] (q : A ⟶ X.op) : HasColimit q :=
    (F1B.kanHasColimit_iff_hasLimit_op q).mpr (HasFiniteLimits.hasLimit _)
  have hE (T : SSet.{u}) (q : (⊥ : T.Subcomplex).toSSet ⟶ X.op) :
      HasPreservedColimit (SSet.opFunctor.map U) q := by
    have : ((⊥ : T.Subcomplex) : SSet.{u}).Finite := SSet.finite_of_iso
      ((initialIsInitial (C := SSet.{u})).uniqueUpToIso Subcomplex.isInitialBot)
    obtain ⟨d, hd⟩ := hcolim q
    refine ⟨d, hd, ?_⟩
    apply (isLimitCone_reverse_postcomp_iff d (SSet.opFunctor.map U)).mp
    apply map_isLimit_of_preservation_op_op U (he T.op)
    exact (F1B.isColimitCone_iff_reverseCone d).mp hd
  have hS (q : pointConeSpan.{u} ⟶ X.op) :
      HasPreservedColimit (SSet.opFunctor.map U) q := by
    have : pointConeSpan.{u}.Finite := SSet.finite_of_iso pointConeSpanIso.symm
    obtain ⟨d, hd⟩ := hcolim q
    refine ⟨d, hd, ?_⟩
    apply (isLimitCone_reverse_postcomp_iff d (SSet.opFunctor.map U)).mp
    apply map_isLimit_of_preservation_op_op U hs
    exact (F1B.isColimitCone_iff_reverseCone d).mp hd
  have h := hasPreservedColimit_finite_of_empty_pointSpan (SSet.opFunctor.map U)
    hE hS K.op (SSet.opFunctor.map p)
  exact (map_reverseCocone_isColimit_iff U c).mp
    (h.map_isColimit c.reverseCocone ((isLimitCone_iff_reverseCocone c).mp hc))

end SerrePositivity.InfinityCategories.F2.Ind
