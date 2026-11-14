module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.F1BKanComplexHomotopyClasses
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.WeakHomotopyInverse

/-!
概要：Kan 複体間の弱ホモトピー同値は実際のホモトピー逆を持つ。
方針：始域への写像のホモトピー類の全射性で左逆を選び、終域への単射性で右逆も得る。
規約：一般の単体集合の弱可縮性を、Kan 性を含む条件に置き換えない。
使われ方：Kerodon Proposition 3.1.7.13（Tag 00UB）、Quillen A の空間の判定。

対応節は Kerodon 3.1（Tag 00SZ）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes

/-- 概要：Kan 複体間の弱ホモトピー同値は単体的ホモトピー同値。
方針：全ての Kan 標的による検査のうち、始域と終域の二つを使って同じ逆射を得る。
規約：逆の両合成は実際の Δ[1] ホモトピーで恒等射に結ぶ。
使われ方：Kerodon Proposition 3.1.7.13（Tag 00UB）。 -/
lemma IsWeakHomotopyEquivalence.isSimplicialHomotopyEquivalence
    {A B : SSet.{u}} [KanComplex A] [KanComplex B] {f : A ⟶ B}
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence f) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence f := by
  obtain ⟨a, ha⟩ := (hf A).surjective (SSet.π₀.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (𝟙 A)))
  obtain ⟨v, rfl⟩ := SSet.π₀.mk_surjective a
  obtain ⟨g, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv B A).surjective v
  have hfg : SSet.π₀.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (f ≫ g)) = SSet.π₀.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (𝟙 A)) := ha
  obtain ⟨H⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_piZero_eq_iff_homotopy _ _).mp hfg
  have hgf : SSet.π₀.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (g ≫ f)) = SSet.π₀.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (𝟙 B)) := by
    apply (hf B).injective
    change SSet.π₀.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (f ≫ (g ≫ f))) =
      SSet.π₀.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (f ≫ 𝟙 B))
    have h := congrArg (SSet.mapπ₀ ((ihom A).map f)) hfg
    change SSet.π₀.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((f ≫ g) ≫ f)) =
      SSet.π₀.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((𝟙 A) ≫ f)) at h
    simpa only [Category.assoc, Category.id_comp, Category.comp_id] using h
  exact ⟨g, ⟨H⟩, (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_piZero_eq_iff_homotopy _ _).mp hgf⟩

/-- 概要：Kan 複体間では弱ホモトピー同値と quasicategory の同値は一致する。
方針：一方は上のホモトピー逆、他方は全 Kan 標的への前合成から得る。
規約：Kan 性はこの比較補題の仮定であり、弱同値の定義には含まれない。
使われ方：Kerodon Proposition 3.1.7.13（Tag 00UB）、写像空間の同値の判定。 -/
lemma isWeakHomotopyEquivalence_iff_isQCatEquivalence {A B : SSet.{u}}
    [KanComplex A] [KanComplex B] (f : A ⟶ B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence f ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence f :=
  ⟨fun h ↦ h.isSimplicialHomotopyEquivalence.isQCatEquivalence,
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence.isWeakHomotopyEquivalence⟩

/-- 概要：Kan 複体間では弱ホモトピー同値と実際のホモトピー逆の存在は同値。
方針：二つの Kan 標的による逆の構成と、任意の射に対するホモトピー逆の検査を組み合わせる。
規約：弱同値の定義自体には Kan 性を追加しない。
使われ方：Kerodon Proposition 3.1.7.13（Tag 00UB） の判定。 -/
lemma isWeakHomotopyEquivalence_iff_isSimplicialHomotopyEquivalence {A B : SSet.{u}}
    [KanComplex A] [KanComplex B] (f : A ⟶ B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence f ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence f :=
  ⟨IsWeakHomotopyEquivalence.isSimplicialHomotopyEquivalence,
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence.isWeakHomotopyEquivalence⟩

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "2.1.3.5" (partial := component) "仮定：可縮な二つの Kan 複体と任意の射（原典の第一の明記された観察と一致）。結論：一点への二射が弱同値なので cancel_right と Kan Whitehead により、その射は単体ホモトピー同値。一文目に一致するが、これを用いた left fibration の輸送 criterion と hT→H の関手性の議論は含まない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence.isSimplicialHomotopyEquivalence
attribute [cite HTT "3.1.3.2"] _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.isWeakHomotopyEquivalence_iff_isQCatEquivalence
