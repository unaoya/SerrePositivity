module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoreLimit
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.LimitConeExtension

/-!
概要：元の指定極限錐の標準同型の恒等・合成・制限の法則。
方針：錐のホモトピー圏の終対象への射の一意性を、同じ頂点射影で写す。
規約：HTT §1.2.13、Kerodon §7.1（Tag 02H1）の既存の一意性の計算則。
使われ方：S8 の固定された離散重みの値の同型の合成を、同じ元の錐の射へ戻す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
variable {K X : SSet.{u}} [Quasicategory X] {p : K ⟶ X}

/-- 指定極限錐の同じ標準同型は、恒等の射を返す。 -/
lemma limitConeIso_hom_refl (c : JoinCone p) (hc : IsLimitCone c) :
    (limitConeIso c c hc hc).hom = 𝟙 _ :=
  hc.isTerminalHo.hom_ext _ _

/-- 指定極限錐の同じ標準同型の順射は合成を保つ。 -/
lemma limitConeIso_hom_comp (c d e : JoinCone p)
    (hc : IsLimitCone c) (hd : IsLimitCone d) (he : IsLimitCone e) :
    (limitConeIso c d hc hd).hom ≫ (limitConeIso d e hd he).hom =
      (limitConeIso c e hc he).hom :=
  he.isTerminalHo.hom_ext _ _

/-- 同じ標準頂点同型の恒等則。 -/
lemma limitVertexIso_hom_refl (c : JoinCone p) (hc : IsLimitCone c) :
    (limitVertexIso c c hc hc).hom = 𝟙 _ := by
  change (hoFunctor.map (sliceOverProjection p)).toFunctor.map
    (limitConeIso c c hc hc).hom = _
  rw [limitConeIso_hom_refl, CategoryTheory.Functor.map_id]
  rfl

/-- 同じ標準頂点同型の合成則。途中の極限の選択を変えない。 -/
lemma limitVertexIso_hom_comp (c d e : JoinCone p)
    (hc : IsLimitCone c) (hd : IsLimitCone d) (he : IsLimitCone e) :
    (limitVertexIso c d hc hd).hom ≫ (limitVertexIso d e hd he).hom =
      (limitVertexIso c e hc he).hom := by
  change (hoFunctor.map (sliceOverProjection p)).toFunctor.map (limitConeIso c d hc hd).hom ≫
    (hoFunctor.map (sliceOverProjection p)).toFunctor.map (limitConeIso d e hd he).hom =
      (hoFunctor.map (sliceOverProjection p)).toFunctor.map (limitConeIso c e hc he).hom
  rw [← CategoryTheory.Functor.map_comp, limitConeIso_hom_comp]

/-- 同じ全錐の制限が極限であれば、標準同型を制限しても同じ標準同型になる。 -/
lemma limitConeIso_restrict_hom {A : SSet.{u}} (f : A ⟶ K) (c d : JoinCone p)
    (hc : IsLimitCone c) (hd : IsLimitCone d)
    (hcf : IsLimitCone (restrictJoinCone c f)) (hdf : IsLimitCone (restrictJoinCone d f)) :
    (hoFunctor.map (sliceOverRestrict p f)).toFunctor.map (limitConeIso c d hc hd).hom =
      (limitConeIso (restrictJoinCone c f) (restrictJoinCone d f) hcf hdf).hom :=
  hdf.isTerminalHo.hom_ext _ _

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
