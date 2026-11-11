module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.EquivalenceCylinderFunctorIso
public import Mathlib.CategoryTheory.Limits.Types.Pushouts

/-!
概要：pushout 上での単体的ホモトピーの貼り合わせ。
方針：直積の pushout 保存と零単体の共同全射性を用いる。
規約：貼り合わせは共通部分で厳密に一致する。
使われ方：Kerodon Lemma 4.6.4.25（Tag 01KV） の相対自然同型。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：共通部分で一致する二つのホモトピーは pushout 上へ貼り合わさる。
方針：標準区間との直積が pushout を保つことを使う。
規約：二つの端点は同じ全体の射の制限で指定する。
使われ方：Kerodon Lemma 4.6.4.25（Tag 01KV） の共通図式を固定した貼り合わせ。 -/
noncomputable def pushoutHomotopy {A B C D X : SSet.{u}}
    {i : A ⟶ B} {j : A ⟶ C} {r : B ⟶ D} {s : C ⟶ D}
    (hP : IsPushout i j r s) {f g : D ⟶ X}
    (H₁ : SSet.Homotopy (r ≫ f) (r ≫ g)) (H₂ : SSet.Homotopy (s ≫ f) (s ≫ g))
    (hw : (i ▷ (Δ[1] : SSet.{u})) ≫ H₁.h = (j ▷ (Δ[1] : SSet.{u})) ≫ H₂.h) :
    SSet.Homotopy f g where
  h := (hP.map (tensorRight (Δ[1] : SSet.{u}))).desc H₁.h H₂.h hw
  h₀ := by
    apply hP.hom_ext
    · rw [← Category.assoc, ← SSet.ι₀_comp, Category.assoc, IsPushout.inl_desc, H₁.h₀]
      rfl
    · rw [← Category.assoc, ← SSet.ι₀_comp, Category.assoc, IsPushout.inr_desc, H₂.h₀]
      rfl
  h₁ := by
    apply hP.hom_ext
    · rw [← Category.assoc, ← SSet.ι₁_comp, Category.assoc, IsPushout.inl_desc, H₁.h₁]
      rfl
    · rw [← Category.assoc, ← SSet.ι₁_comp, Category.assoc, IsPushout.inr_desc, H₂.h₁]
      rfl
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro z
    exact False.elim z.1.property

/-- 概要：貼り合わせたホモトピーの左側への制限は指定されたもの。
方針：pushout の desc の計算。
規約：等式は全時刻で厳密。
使われ方：Kerodon Lemma 4.6.4.25（Tag 01KV） の貼り合わせ。 -/
lemma pushoutHomotopy_inl {A B C D X : SSet.{u}}
    {i : A ⟶ B} {j : A ⟶ C} {r : B ⟶ D} {s : C ⟶ D}
    (hP : IsPushout i j r s) {f g : D ⟶ X}
    (H₁ : SSet.Homotopy (r ≫ f) (r ≫ g)) (H₂ : SSet.Homotopy (s ≫ f) (s ≫ g))
    (hw : (i ▷ (Δ[1] : SSet.{u})) ≫ H₁.h = (j ▷ (Δ[1] : SSet.{u})) ≫ H₂.h) :
    (r ▷ (Δ[1] : SSet.{u})) ≫ (pushoutHomotopy hP H₁ H₂ hw).h = H₁.h :=
  IsPushout.inl_desc _ _ _ _

/-- 概要：貼り合わせたホモトピーの右側への制限は指定されたもの。
方針：pushout の desc の計算。
規約：等式は全時刻で厳密。
使われ方：Kerodon Lemma 4.6.4.25（Tag 01KV） の貼り合わせ。 -/
lemma pushoutHomotopy_inr {A B C D X : SSet.{u}}
    {i : A ⟶ B} {j : A ⟶ C} {r : B ⟶ D} {s : C ⟶ D}
    (hP : IsPushout i j r s) {f g : D ⟶ X}
    (H₁ : SSet.Homotopy (r ≫ f) (r ≫ g)) (H₂ : SSet.Homotopy (s ≫ f) (s ≫ g))
    (hw : (i ▷ (Δ[1] : SSet.{u})) ≫ H₁.h = (j ▷ (Δ[1] : SSet.{u})) ≫ H₂.h) :
    (s ▷ (Δ[1] : SSet.{u})) ≫ (pushoutHomotopy hP H₁ H₂ hw).h = H₂.h :=
  IsPushout.inr_desc _ _ _ _

/-- 概要：pushout 上のホモトピーが両側で点ごとに可逆なら全体でも点ごとに可逆。
方針：各頂点が pushout の片側から来ることを使う。
規約：quasicategory 性はこの検出には不要。
使われ方：Kerodon Lemma 4.6.4.25（Tag 01KV） の自然同型の貼り合わせ。 -/
lemma pushoutHomotopy_isInvertible {A B C D X : SSet.{u}}
    {i : A ⟶ B} {j : A ⟶ C} {r : B ⟶ D} {s : C ⟶ D}
    (hP : IsPushout i j r s) {f g : D ⟶ X} (H : SSet.Homotopy f g)
    (H₁ : SSet.Homotopy (r ≫ f) (r ≫ g)) (H₂ : SSet.Homotopy (s ≫ f) (s ≫ g))
    (h₁ : (r ▷ (Δ[1] : SSet.{u})) ≫ H.h = H₁.h)
    (h₂ : (s ▷ (Δ[1] : SSet.{u})) ≫ H.h = H₂.h)
    (hi₁ : ∀ x, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H₁ x).toTruncated)
    (hi₂ : ∀ x, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H₂ x).toTruncated)
    (x : D _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H x).toTruncated := by
  have ht := hP.map ((evaluation _ (Type u)).obj (Opposite.op ⦋0⦌))
  obtain ⟨y, rfl⟩ | ⟨y, rfl⟩ := Types.eq_or_eq_of_isPushout ht x
  · have he := congrArg (fun z : B ⊗ (Δ[1] : SSet.{u}) ⟶ X ↦
        z.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant y 1, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge)) h₁
    have hn : r.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant y 1) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (r.app (Opposite.op ⦋0⦌) y) 1 :=
      ConcreteCategory.congr_hom (r.naturality (SimplexCategory.const ⦋1⦌ ⦋0⦌ 0).op) y
    dsimp at he
    rw [hn, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one] at he
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr he).2 (hi₁ y)
  · have he := congrArg (fun z : C ⊗ (Δ[1] : SSet.{u}) ⟶ X ↦
        z.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant y 1, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge)) h₂
    have hn : s.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant y 1) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (s.app (Opposite.op ⦋0⦌) y) 1 :=
      ConcreteCategory.congr_hom (s.naturality (SimplexCategory.const ⦋1⦌ ⦋0⦌ 0).op) y
    dsimp at he
    rw [hn, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one] at he
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr he).2 (hi₂ y)

/-- 概要：共通部分で一致する点ごとに可逆なホモトピーを貼ると自然同型を得る。
方針：ホモトピーの貼り合わせと点ごとの可逆性の判定を組み合わせる。
規約：標的 X のみ quasicategory とする。
使われ方：Kerodon Lemma 4.6.4.25（Tag 01KV） の相対的な自然同型。 -/
lemma nonempty_functorIso_of_pushout_homotopies {A B C D X : SSet.{u}} [Quasicategory X]
    {i : A ⟶ B} {j : A ⟶ C} {r : B ⟶ D} {s : C ⟶ D}
    (hP : IsPushout i j r s) {f g : D ⟶ X}
    (H₁ : SSet.Homotopy (r ≫ f) (r ≫ g)) (H₂ : SSet.Homotopy (s ≫ f) (s ≫ g))
    (hw : (i ▷ (Δ[1] : SSet.{u})) ≫ H₁.h = (j ▷ (Δ[1] : SSet.{u})) ≫ H₂.h)
    (hi₁ : ∀ x, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H₁ x).toTruncated)
    (hi₂ : ∀ x, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H₂ x).toTruncated) :
    Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) := by
  let H := pushoutHomotopy hP H₁ H₂ hw
  exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.functorIsoOfPointwiseInvertibleHomotopy H
    (pushoutHomotopy_isInvertible hP H H₁ H₂
      (pushoutHomotopy_inl hP H₁ H₂ hw) (pushoutHomotopy_inr hP H₁ H₂ hw) hi₁ hi₂)⟩

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
