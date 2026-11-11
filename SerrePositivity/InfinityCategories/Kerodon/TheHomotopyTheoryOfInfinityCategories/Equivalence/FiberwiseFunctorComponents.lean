module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Diagrams.SimplexDiagram
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：fiber ごとの関手の族から、各標準単体上の実際の図式を回収する。
方針：底の一致を型に反映し、族の単体的自然性を回収した図式の自然性へ移す。
規約：余極限保存・充填性はこの局所計算には不要。
使われ方：局所図式の cocone を作り、全空間上の図式へ降ろす。

対応節は Kerodon 4.5（Tag 01DE）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence

/-- 概要：構造射の等式で fiber ごとの図式の型を揃える。
方針：等式による型の輸送。
規約：底図式の射の等式であり、自然同型ではない。
使われ方：一つの大域的な底への射を保つ局所図式の回収。 -/
@[kerodon 046N]
def fiberwiseFunctorValue {B T D : SSet.{u}} {F : Over B ⥤ SSet.{u}}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FiberwiseFunctorSimplex F D T) {σ : T ⟶ B} (h : s.1 = σ) :
    F.obj (Over.mk σ) ⟶ D := h ▸ s.2

/-- 概要：底を等式で揃えても元の fiber ごとの図式を表す。
方針：等式を消去して依存和を比較する。
規約：元のデータ全体の厳密な等式。
使われ方：単体的自然性から回収した成分の自然性を導く。 -/
lemma fiberwiseFunctorValue_pair {B T D : SSet.{u}} {F : Over B ⥤ SSet.{u}}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FiberwiseFunctorSimplex F D T) {σ : T ⟶ B} (h : s.1 = σ) :
    (⟨σ, fiberwiseFunctorValue s h⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FiberwiseFunctorSimplex F D T) = s := by
  rcases s with ⟨τ, hτ⟩
  cases h
  rfl

/-- 概要：全空間への標準単体の底成分は射影との合成。
方針：Yoneda の単射性と合成則。
規約：標準単体は任意の次元。
使われ方：局所成分の定義域を大域的な底への射で固定する。 -/
lemma fiberwiseFunctor_simplex_base {B D : SSet.{u}} (F : Over B ⥤ SSet.{u})
    {n : SimplexCategory} (f : stdSimplex.obj n ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseFunctor F D) :
    (SSet.yonedaEquiv f).1 = f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseFunctorProjection F D := by
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp]
  rfl

/-- 概要：全空間への族を任意の標準単体に制限して局所図式を回収する。
方針：族の単体の底を射影との合成へ書き換える。
規約：元の族の底への射は f と射影の合成。
使われ方：全単体の図式の cocone の脚。 -/
def fiberwiseFunctorComponent {B A D : SSet.{u}} (F : Over B ⥤ SSet.{u})
    (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseFunctor F D) {n : SimplexCategory} (σ : stdSimplex.obj n ⟶ A) :
    F.obj (Over.mk (σ ≫ (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseFunctorProjection F D))) ⟶ D :=
  fiberwiseFunctorValue (SSet.yonedaEquiv (σ ≫ f))
    ((fiberwiseFunctor_simplex_base F (σ ≫ f)).trans (Category.assoc _ _ _))

/-- 概要：回収した局所図式は元の族の単体を表す。
方針：底の書き換えに対する依存和の不変性。
規約：実際の単体全体の等式。
使われ方：局所図式の貼り合わせの自然性。 -/
lemma fiberwiseFunctorComponent_pair {B A D : SSet.{u}} (F : Over B ⥤ SSet.{u})
    (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseFunctor F D) {n : SimplexCategory} (σ : stdSimplex.obj n ⟶ A) :
    (⟨σ ≫ (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseFunctorProjection F D), fiberwiseFunctorComponent F f σ⟩ :
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FiberwiseFunctorSimplex F D (stdSimplex.obj n)) = SSet.yonedaEquiv (σ ≫ f) :=
  fiberwiseFunctorValue_pair _ _

/-- 概要：回収した局所図式は面・退化に沿う制限と可換。
方針：元の族の単体的自然性を依存和の等式で使う。
規約：底の射は大域的に同じものを保つ。
使われ方：全単体の図式から大域図式へ降ろす際の cocone 条件。 -/
lemma fiberwiseFunctorComponent_precomp {B A D : SSet.{u}} (F : Over B ⥤ SSet.{u})
    (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseFunctor F D) {m n : SimplexCategory}
    (σ : stdSimplex.obj n ⟶ A) (α : m ⟶ n) :
    F.map (Over.homMk (stdSimplex.map α) rfl :
        Over.mk ((stdSimplex.map α ≫ σ) ≫ (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseFunctorProjection F D)) ⟶
          Over.mk (σ ≫ (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseFunctorProjection F D))) ≫
        fiberwiseFunctorComponent F f σ =
      fiberwiseFunctorComponent F f (stdSimplex.map α ≫ σ) := by
  have hn : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseFunctorRestrict F D (stdSimplex.map α)
      (SSet.yonedaEquiv (σ ≫ f)) = SSet.yonedaEquiv ((stdSimplex.map α ≫ σ) ≫ f) :=
    SSet.yonedaEquiv_naturality α (σ ≫ f)
  have he := (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseFunctorRestrict F D (stdSimplex.map α))
    (fiberwiseFunctorComponent_pair F f σ)).trans
      (hn.trans (fiberwiseFunctorComponent_pair F f (stdSimplex.map α ≫ σ)).symm)
  exact eq_of_heq (Sigma.mk.inj he).2

/-- 概要：局所図式の自然性を、同じ単体の任意の表示の上で使う。
方針：制限前後の単体の等式を消去して前合成の式へ戻す。
規約：Over の可換性の証明の選択には依存しない。
使われ方：全単体の添字圏の射に対する cocone の自然性。 -/
lemma fiberwiseFunctorComponent_naturality {B A D : SSet.{u}} (F : Over B ⥤ SSet.{u})
    (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseFunctor F D) {m n : SimplexCategory}
    (σ : stdSimplex.obj n ⟶ A) (τ : stdSimplex.obj m ⟶ A) (α : m ⟶ n)
    (hτ : stdSimplex.map α ≫ σ = τ) :
    F.map (Over.homMk (stdSimplex.map α) (by
        change stdSimplex.map α ≫ (σ ≫ (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseFunctorProjection F D)) =
          τ ≫ (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseFunctorProjection F D)
        exact (Category.assoc _ _ _).symm.trans
          (congrArg (fun q ↦ q ≫ (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseFunctorProjection F D)) hτ)) :
        Over.mk (τ ≫ (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseFunctorProjection F D)) ⟶
          Over.mk (σ ≫ (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseFunctorProjection F D))) ≫
        fiberwiseFunctorComponent F f σ = fiberwiseFunctorComponent F f τ := by
  subst τ
  exact fiberwiseFunctorComponent_precomp F f σ α

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
