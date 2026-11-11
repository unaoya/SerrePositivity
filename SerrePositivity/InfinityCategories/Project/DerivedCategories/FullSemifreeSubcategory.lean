module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.InfinityCategory
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.FullInclusionLift

/-! # semifree の対象条件による充満部分単体集合

概要：semifree 複体の任意の対象条件から D(S) の全部分 quasicategory を構成する。
方針：充満 dg 部分圏の nerve と包含の像との同型を使う。
規約：条件に閉性は要求しない。使われ方：D_Z と Perf_Z の共通基盤。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (S : Type u) [CommRing S] (P : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S → Prop)

/-- 概要：対象条件 P を満たす semifree 複体の dg nerve。
方針：充満 dg 部分圏を取る。規約：元の Hom 複体を保持する。使われ方：計算モデル。 -/
def semifreeFullNerve : SSet.{u + 1} := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve S (DGFullSubcategory (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S) P)

/-- 概要：計算モデルを D(S) に含める。
方針：充満 dg 包含の nerve を使う。規約：対象の包含。使われ方：像の同定。 -/
def semifreeFullNerveInclusion : semifreeFullNerve S P ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory S :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFullSubcategoryInclusion S (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S) P)

/-- 概要：P を満たす頂点が張る D(S) の全部分単体集合。
方針：各単体の全頂点に P を課す。規約：実際の Subcomplex。使われ方：部分 ∞ 圏の正本。 -/
def semifreeFullSubcomplex : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory S).Subcomplex :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fullOnObjects S (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S) P

/-- 概要：計算モデルの包含は各次数で単射。
方針：充満 dg 包含の単射性。規約：単体集合の Mono。使われ方：像への同型。 -/
instance semifreeFullNerveInclusion_mono : Mono (semifreeFullNerveInclusion S P) := by
  dsimp [semifreeFullNerveInclusion]
  infer_instance

/-- 概要：計算モデルの包含像は指定された全部分単体集合である。
方針：充満 dg 包含の像の一般定理。規約：部分集合としての等式。使われ方：正本の同定。 -/
lemma semifreeFullNerveInclusion_range :
    SSet.Subcomplex.range (semifreeFullNerveInclusion S P) = semifreeFullSubcomplex S P :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.range_inclusion S (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S) P

/-- 概要：計算モデルと全部分単体集合の台は単体的に同型である。
方針：単射の像への分解を使う。規約：実際の同型。使われ方：ホーン充填の転送。 -/
def semifreeFullNerveIso :
    semifreeFullNerve S P ≅ (semifreeFullSubcomplex S P : SSet.{u + 1}) :=
  asIso (SSet.Subcomplex.toRange (semifreeFullNerveInclusion S P)) ≪≫
    eqToIso (congrArg (fun K : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory S).Subcomplex => (K : SSet.{u + 1}))
      (semifreeFullNerveInclusion_range S P))

/-- 概要：計算モデルは quasicategory である。
方針：N2 の dg nerve の一般定理。規約：条件 P は任意。使われ方：部分 ∞ 圏の基盤。 -/
instance semifreeFullNerve_quasicategory : SSet.Quasicategory (semifreeFullNerve S P) := by
  dsimp [semifreeFullNerve]
  infer_instance

/-- 概要：指定頂点の全部分単体集合は quasicategory である。
方針：単体的同型を使って内部ホーンを計算モデルで充填する。
規約：対象条件への追加仮定なし。使われ方：D_Z と Perf_Z。 -/
instance semifreeFullSubcomplex_quasicategory :
    SSet.Quasicategory (semifreeFullSubcomplex S P : SSet.{u + 1}) where
  hornFilling' {n} {i} b h0 hn := by
    obtain ⟨f, hf⟩ := SSet.Quasicategory.hornFilling h0 hn (b ≫ (semifreeFullNerveIso S P).inv)
    refine ⟨f ≫ (semifreeFullNerveIso S P).hom, ?_⟩
    rw [← Category.assoc, ← hf, Category.assoc, Iso.inv_hom_id, Category.comp_id]

end SerrePositivity.InfinityCategories.Project.DerivedCategories
