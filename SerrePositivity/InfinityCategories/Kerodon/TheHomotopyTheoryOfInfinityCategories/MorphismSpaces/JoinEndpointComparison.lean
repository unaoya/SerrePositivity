module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FatJoinFixedDiagramComparison

/-!
概要：両端の因子上の図式を同時に固定した fat join 比較の同値性。
方針：左右の因子の次数ごとの直和を作り、join への単射を固定図式比較へ適用する。
規約：一般の join と fat join は Core の既存の構成を使う。
使われ方：Kerodon §4.6.5（Tag 01KW）–4.6.6（Tag 04HY）、左右の写像空間の固定端点を保つ比較。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：join の左右の因子を交わらずに並べる単体集合。
方針：各次数で二つの型の直和を取り、引き戻しは各因子で行う。
規約：次数ごとの直和を明示し、追加の非空性を要求しない。
使われ方：Kerodon §4.6.6（Tag 04HY）、join の両端で同時に図式を固定する始域。 -/
def joinEndpointDiagram (A B : SSet.{u}) : SSet.{u} where
  obj d := A.obj d ⊕ B.obj d
  map α := ↾Sum.map (A.map α) (B.map α)
  map_id d := by
    apply ConcreteCategory.hom_ext
    intro s
    cases s with
    | inl a => exact congrArg Sum.inl (CategoryTheory.Functor.map_id_apply A d a)
    | inr b => exact congrArg Sum.inr (CategoryTheory.Functor.map_id_apply B d b)
  map_comp α β := by
    apply ConcreteCategory.hom_ext
    intro s
    cases s with
    | inl a => exact congrArg Sum.inl (CategoryTheory.Functor.map_comp_apply A α β a)
    | inr b => exact congrArg Sum.inr (CategoryTheory.Functor.map_comp_apply B α β b)

/-- 概要：左右の因子を通常の join に含める射。
方針：直和の二つの場合で左右の join の包含を使う。
規約：両端の因子を同じ射の始域にまとめる。
使われ方：Kerodon §4.6.6（Tag 04HY）、両端固定の関手単体集合の制限射。 -/
def joinEndpointInclusion (A B : SSet.{u}) : joinEndpointDiagram A B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A B where
  app d := ↾Sum.elim ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A B).app d) ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A B).app d)
  naturality d e α := by
    apply ConcreteCategory.hom_ext
    intro s
    cases s with
    | inl a => exact ConcreteCategory.congr_hom ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A B).naturality α) a
    | inr b => exact ConcreteCategory.congr_hom ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A B).naturality α) b

/-- 概要：左右の因子を fat join に含める射。
方針：直和の各場合に fat join の左右の包含を適用する。
規約：始域は通常の join の端点包含と共通。
使われ方：Kerodon §4.6.6（Tag 04HY）、fat join の両端固定の図式。 -/
noncomputable def fatJoinEndpointInclusion (A B : SSet.{u}) :
    joinEndpointDiagram A B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin A B where
  app d := ↾Sum.elim ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl A B).app d) ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr A B).app d)
  naturality d e α := by
    apply ConcreteCategory.hom_ext
    intro s
    cases s with
    | inl a => exact ConcreteCategory.congr_hom ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl A B).naturality α) a
    | inr b => exact ConcreteCategory.congr_hom ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr A B).naturality α) b

/-- 概要：join の両端をまとめた包含は単射。
方針：同じ因子では成分を回収し、異なる因子では join の切断が零と全頂点数で異なる。
規約：空の因子も許す。
使われ方：Kerodon §4.6.6（Tag 04HY）、固定図式の相対的な比較に必要な単射性。 -/
instance joinEndpointInclusion_mono (A B : SSet.{u}) : Mono (joinEndpointInclusion A B) := by
  rw [NatTrans.mono_iff_mono_app]
  rintro ⟨⟨n⟩⟩
  rw [mono_iff_injective]
  intro s t h
  cases s with
  | inl a =>
    cases t with
    | inl a' =>
      exact congrArg Sum.inl (congrArg Prod.fst (eq_of_heq (Sigma.mk.inj h).2))
    | inr b =>
      have hc := congrArg (fun z ↦ z.1.val) h
      change n + 1 = 0 at hc
      omega
  | inr b =>
    cases t with
    | inl a =>
      have hc := congrArg (fun z ↦ z.1.val) h
      change 0 = n + 1 at hc
      omega
    | inr b' =>
      exact congrArg Sum.inr (congrArg Prod.snd (eq_of_heq (Sigma.mk.inj h).2))

/-- 概要：fat join 比較は左右をまとめた端点包含と可換。
方針：各次数で左右に場合分けし、既存の包含の比較式を使う。
規約：両端の因子は任意。
使われ方：Kerodon §4.6.6（Tag 04HY）、両端固定の制限射の可換性。 -/
lemma fatJoinEndpointInclusion_comparison (A B : SSet.{u}) :
    fatJoinEndpointInclusion A B ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinComparison A B = joinEndpointInclusion A B := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro s
  cases s with
  | inl a =>
    exact ConcreteCategory.congr_hom (C := Type u)
      (NatTrans.congr_app (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl_comparison A B) d) a
  | inr b =>
    exact ConcreteCategory.congr_hom (C := Type u)
      (NatTrans.congr_app (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr_comparison A B) d) b

/-- 概要：fat join の両端をまとめた包含も単射。
方針：通常の join の包含との合成が単射であることから従う。
規約：fat join 比較そのものの単射性は使わない。
使われ方：Kerodon §4.6.6（Tag 04HY）、固定図式上の同値性の仮定の確認。 -/
instance fatJoinEndpointInclusion_mono (A B : SSet.{u}) :
    Mono (fatJoinEndpointInclusion A B) := by
  have : Mono (fatJoinEndpointInclusion A B ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinComparison A B) := by
    rw [fatJoinEndpointInclusion_comparison]
    infer_instance
  exact mono_of_mono (fatJoinEndpointInclusion A B) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinComparison A B)

/-- 概要：両端の因子上の図式を固定しても fat join の前合成比較は同値。
方針：端点の二つの包含の単射性と、fat join 比較の単射な前合成の同値を用いる。
規約：標的 X にのみ quasicategory 性を要求する。
使われ方：Kerodon §4.6.5（Tag 01KW）–4.6.6（Tag 04HY）、写像空間の比較で両端を厳密に固定する。 -/
lemma isQCatEquivalence_fatJoinComparison_fixedEndpoints
    (A B X : SSet.{u}) [Quasicategory X] (p : joinEndpointDiagram A B ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap
      ((pre (joinEndpointInclusion A B)).app X)
      ((pre (fatJoinEndpointInclusion A B)).app X)
      ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinComparison A B)).app X)
      (by rw [← NatTrans.comp_app, ← pre_map, fatJoinEndpointInclusion_comparison])
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p)) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_vertexFiberMap_pre
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_fatJoinComparison A B X

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
