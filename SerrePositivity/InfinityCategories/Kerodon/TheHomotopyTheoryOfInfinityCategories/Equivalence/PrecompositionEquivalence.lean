module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FunctorCompositionEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.InnerAnodyneEquivalence
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：任意の quasicategory への前合成による比較射の同値判定の補助条件。
方針：前合成が既存の IsQCatEquivalence を満たすことを要求する。
規約：既存の同値の定義は変更せず、非 quasicategory の補助模型に適用する。
使われ方：Kerodon Theorem 4.6.2.8（Tag 01HV） の fat join の比較。

対応節は Kerodon 4.5（Tag 01DE）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence

/-- 概要：全ての quasicategory を標的とする前合成が同値となる条件。
方針：内部 Hom 間の射の IsQCatEquivalence を用いる。
規約：元の二つの単体集合は quasicategory でなくてもよい。
使われ方：Kerodon Theorem 4.6.2.8（Tag 01HV） の比較射の普遍的な同値性。 -/
def IsPrecompositionEquivalence {A B : SSet.{u}} (f : A ⟶ B) : Prop :=
  ∀ (X : SSet.{u}) [Quasicategory X], _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence ((pre f).app X)

/-- 概要：恒等射は前合成の同値条件を満たす。
方針：前合成が恒等射であることを使う。
規約：任意の単体集合 A。
使われ方：Kerodon §4.6.2（Tag 01HM） の比較射の基本例。 -/
lemma isPrecompositionEquivalence_id (A : SSet.{u}) : IsPrecompositionEquivalence (𝟙 A) := by
  intro X hX
  rw [pre_id, NatTrans.id_app]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence.refl _).isQCatEquivalence

/-- 概要：前合成の同値条件は合成で閉じる。
方針：前合成の逆順の合成と同値の合成則を使う。
規約：元の単体集合に quasicategory 性を要求しない。
使われ方：Kerodon §4.6.2（Tag 01HM） の比較の因子分解。 -/
lemma IsPrecompositionEquivalence.comp {A B C : SSet.{u}} {f : A ⟶ B} {g : B ⟶ C}
    (hf : IsPrecompositionEquivalence f) (hg : IsPrecompositionEquivalence g) :
    IsPrecompositionEquivalence (f ≫ g) := by
  intro X hX
  simpa only [pre_map, NatTrans.comp_app] using (hg X).comp (hf X)

/-- 概要：quasicategory の同値は前合成の同値条件を満たす。
方針：既存の明示的な逆データの前合成作用を使う。
規約：この補題では元の二つの単体集合は quasicategory。
使われ方：Kerodon §4.5.1（Tag 01DQ）、§4.6.2（Tag 01HM） の既存の同値との接続。 -/
lemma IsQCatEquivalence.isPrecompositionEquivalence {A B : SSet.{u}}
    [Quasicategory A] [Quasicategory B] {f : A ⟶ B} (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence f) :
    IsPrecompositionEquivalence f := fun X _ ↦ hf.precompose X

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence export _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsQCatEquivalence (isPrecompositionEquivalence)


/-- 概要：点ごとに可逆なホモトピー逆があれば前合成の同値条件を満たす。
方針：二つのホモトピーを前合成作用の可逆二胞体にする。
規約：元の二つの単体集合は quasicategory でなくてもよい。
使われ方：Kerodon §4.6.2（Tag 01HM） の標準単体の fat join の変形。 -/
lemma isPrecompositionEquivalence_of_homotopyInverse {A B : SSet.{u}}
    (f : A ⟶ B) (g : B ⟶ A) (H₀ : SSet.Homotopy (f ≫ g) (𝟙 A))
    (H₁ : SSet.Homotopy (g ≫ f) (𝟙 B))
    (h₀ : ∀ a : A _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H₀ a).toTruncated)
    (h₁ : ∀ b : B _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H₁ b).toTruncated) :
    IsPrecompositionEquivalence f := by
  intro X hX
  refine ⟨(pre g).app X, ⟨?_⟩, ⟨?_⟩⟩
  · simpa only [pre_map, NatTrans.comp_app, pre_id, NatTrans.id_app] using
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.functorIsoPrecompositionOfHomotopy H₁ h₁ X
  · simpa only [pre_map, NatTrans.comp_app, pre_id, NatTrans.id_app] using
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.functorIsoPrecompositionOfHomotopy H₀ h₀ X

/-- 概要：前合成の同値条件は前の因子の同値性を消去できる。
方針：前合成の逆順の合成に同値の二対三則を適用する。
規約：元の単体集合に quasicategory 性を要求しない。
使われ方：Kerodon §4.6.2（Tag 01HM） の比較射の因子分解。 -/
lemma IsPrecompositionEquivalence.cancel_left {A B C : SSet.{u}} {f : A ⟶ B} {g : B ⟶ C}
    (hf : IsPrecompositionEquivalence f) (hfg : IsPrecompositionEquivalence (f ≫ g)) :
    IsPrecompositionEquivalence g := by
  intro X hX
  have h := hfg X
  rw [pre_map, NatTrans.comp_app] at h
  exact (hf X).cancel_right h

/-- 概要：前合成の同値条件は後の因子の同値性を消去できる。
方針：前合成の逆順の合成に同値の二対三則を適用する。
規約：元の単体集合に quasicategory 性を要求しない。
使われ方：Kerodon §4.6.2（Tag 01HM） の比較射の切断による検出。 -/
lemma IsPrecompositionEquivalence.cancel_right {A B C : SSet.{u}} {f : A ⟶ B} {g : B ⟶ C}
    (hg : IsPrecompositionEquivalence g) (hfg : IsPrecompositionEquivalence (f ≫ g)) :
    IsPrecompositionEquivalence f := by
  intro X hX
  have h := hfg X
  rw [pre_map, NatTrans.comp_app] at h
  exact (hg X).cancel_left h

/-- 概要：inner anodyne 射は前合成の同値条件を満たす。
方針：関手単体集合の制限の trivial Kan fibration 性を使う。
規約：元の単体集合の quasicategory 性は不要。
使われ方：Kerodon §4.6.2（Tag 01HM） のセルによる比較。 -/
@[kerodon 01EJ]
lemma isPrecompositionEquivalence_of_innerAnodyne {A B : SSet.{u}} (f : A ⟶ B)
    (hf : innerAnodyneExtensions f) : IsPrecompositionEquivalence f := by
  intro X hX
  haveI := _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.trivialKanFibration_pre_of_innerAnodyne f hf X
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration _

/-- 概要：充満忠実な関手の像の頂点どうしの同型は元の頂点の同型へ戻せる。
方針：ホモトピー圏の充満忠実な関手で同型の逆像を取る。
規約：両端は quasicategory。
使われ方：Kerodon §4.8.3（Tag 05AW）、§4.6.2（Tag 01HM） の前合成による同値の検出。 -/
noncomputable def IsFullyFaithful.preimageVertexIso {A B : SSet.{u}}
    [Quasicategory A] [Quasicategory B] {f : A ⟶ B} (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful f)
    {x y : A _⦋0⦌} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (f.app (Opposite.op ⦋0⦌) x) (f.app (Opposite.op ⦋0⦌) y)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso x y := hf.toHoFullyFaithful.preimageIso e

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful export _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsFullyFaithful (preimageVertexIso)


/-- 概要：quasicategory 間では前合成の同値条件から既存の逆データの同値性が従う。
方針：始域を標的とする前合成から逆射を取り、終域を標的とする充満忠実性で余単位を戻す。
規約：この逆方向では元の二つの単体集合は quasicategory。
使われ方：Kerodon §4.5.1（Tag 01DQ） の同値の普遍的な検出。 -/
lemma IsPrecompositionEquivalence.isQCatEquivalence {A B : SSet.{u}}
    [Quasicategory A] [Quasicategory B] {f : A ⟶ B} (hf : IsPrecompositionEquivalence f) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence f := by
  obtain ⟨v, ⟨hv⟩⟩ := (hf A).choose.isEssentiallySurjective (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (𝟙 A))
  obtain ⟨g, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv B A).surjective v
  have hunit : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (f ≫ g) (𝟙 A) := hv
  have hcomp : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (f ≫ (g ≫ f)) (f ≫ 𝟙 B) := by
    simpa only [Category.assoc, Category.comp_id, Category.id_comp] using
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp hunit f
  have hcounit : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (g ≫ f) (𝟙 B) :=
    (hf B).isFullyFaithful.preimageVertexIso
      (x := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (g ≫ f)) (y := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (𝟙 B)) hcomp
  exact ⟨g, ⟨hunit⟩, ⟨hcounit⟩⟩

/-- 概要：quasicategory 間では前合成の同値条件と既存の同値性は同値。
方針：前合成の保存と二つの標的による検出を組み合わせる。
規約：既存の IsQCatEquivalence の定義はそのまま。
使われ方：Kerodon §4.5.1（Tag 01DQ）、§4.6.2（Tag 01HM） の補助条件の整合性。 -/
lemma isPrecompositionEquivalence_iff_isQCatEquivalence {A B : SSet.{u}}
    [Quasicategory A] [Quasicategory B] (f : A ⟶ B) :
    IsPrecompositionEquivalence f ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence f :=
  ⟨IsPrecompositionEquivalence.isQCatEquivalence, IsQCatEquivalence.isPrecompositionEquivalence⟩

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
