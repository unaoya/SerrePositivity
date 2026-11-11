module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalFamilyClasses
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanHomotopyEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PreFiberKan

/-!
概要：写像空間の同値をパラメータ付きの定値関手間 Hom の全単射に移す。
方針：実際のホモトピー類への後合成と模型の同値の逆則を使う。
規約：始域パラメータに quasicategory 性は不要。
使われ方：随伴の写像空間による特徴づけの逆方向の入力の表示。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：写像空間間の射はパラメータ族のホモトピー類に作用する。
方針：族とホモトピーを同じ射で後合成する。
規約：射自体の同値性は要求しない。
使われ方：写像空間の同値を商へ移す。 -/
noncomputable def intervalFamilyClassMap {A X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {x₀ x₁ : X _⦋0⦌} {y₀ y₁ : Y _⦋0⦌}
    (q : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x₀ x₁ ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace y₀ y₁) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalFamilyHomotopyClass A X x₀ x₁ → _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalFamilyHomotopyClass A Y y₀ y₁ :=
  Quotient.map (· ≫ q) (by
    intro f g ⟨H⟩
    refine ⟨{ h := H.h ≫ q, h₀ := ?_, h₁ := ?_, rel := ?_ }⟩
    · rw [← Category.assoc, H.h₀]
      rfl
    · rw [← Category.assoc, H.h₁]
      rfl
    · apply SSet.hom_ext
      intro d
      apply ConcreteCategory.hom_ext
      intro a
      exact False.elim a.1.property)

/-- 概要：写像空間の同値は任意のパラメータ族のホモトピー類の全単射を与える。
方針：指定された同値の逆と二つの逆則を族の前合成で引き戻す。
規約：逆則は実際の単体的ホモトピーを通して商の等式になる。
使われ方：写像空間の同値から h Fun の Hom 対応を得る。 -/
noncomputable def intervalFamilyClassEquiv (A : SSet.{u}) {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {x₀ x₁ : X _⦋0⦌} {y₀ y₁ : Y _⦋0⦌}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x₀ x₁) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace y₀ y₁)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalFamilyHomotopyClass A X x₀ x₁ ≃ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalFamilyHomotopyClass A Y y₀ y₁ where
  toFun := intervalFamilyClassMap e.hom
  invFun := intervalFamilyClassMap e.inv
  left_inv c := by
    refine Quotient.inductionOn c ?_
    intro f
    apply Quotient.sound
    exact ⟨by simpa only [Category.assoc, Category.comp_id] using
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp e.homInvIso f).simplicialHomotopy⟩
  right_inv c := by
    refine Quotient.inductionOn c ?_
    intro f
    apply Quotient.sound
    exact ⟨by simpa only [Category.assoc, Category.comp_id] using
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp e.invHomIso f).simplicialHomotopy⟩

/-- 概要：写像空間の同値が誘導する定値関手間 Hom の全単射。
方針：Hom を族のホモトピー類で表示し、同値で後合成して戻す。
規約：任意のパラメータ A に同じ指定同値を使う。
使われ方：写像空間による随伴対応から単位・余単位へ接続する準備。 -/
noncomputable def intervalMappingEquivalenceHomEquiv (A : SSet.{u}) {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {x₀ x₁ : X _⦋0⦌} {y₀ y₁ : Y _⦋0⦌}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x₀ x₁) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace y₀ y₁)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.ConstantFunctorHom A X x₀ x₁ ≃ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.ConstantFunctorHom A Y y₀ y₁ :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalFamilyHomotopyEquiv A X x₀ x₁).symm.trans
    ((intervalFamilyClassEquiv A e).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalFamilyHomotopyEquiv A Y y₀ y₁))

/-- 概要：誘導した Hom 対応は代表族を指定同値の順射で後合成する。
方針：ホモトピー類の全単射の両逆と商の計算則。
規約：同じ族 f を用いる。
使われ方：パラメータ自然性と選択独立性の計算。 -/
lemma intervalMappingEquivalenceHomEquiv_family {A X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {x₀ x₁ : X _⦋0⦌} {y₀ y₁ : Y _⦋0⦌}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x₀ x₁) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace y₀ y₁))
    (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x₀ x₁) :
    intervalMappingEquivalenceHomEquiv A e (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom f) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom (f ≫ e.hom) := by
  unfold intervalMappingEquivalenceHomEquiv
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalFamilyHomotopyEquiv_mk f]
  simp only [Equiv.trans_apply, Equiv.symm_apply_apply]
  rfl

/-- 概要：写像空間同値が誘導する Hom の対応はパラメータに自然。
方針：任意の Hom を族で表し、後合成と前合成の結合則を使う。
規約：パラメータ A,B に quasicategory 性は不要。
使われ方：点ごとの同値に由来する対応のパラメータ自然性。 -/
lemma intervalMappingEquivalenceHomEquiv_precomp {A B X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {x₀ x₁ : X _⦋0⦌} {y₀ y₁ : Y _⦋0⦌}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x₀ x₁) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace y₀ y₁))
    (i : A ⟶ B) (α : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.ConstantFunctorHom B X x₀ x₁) :
    intervalMappingEquivalenceHomEquiv A e (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHomPrecomp i α) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHomPrecomp i (intervalMappingEquivalenceHomEquiv B e α) := by
  obtain ⟨f, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom_surjective B X x₀ x₁ α
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom_precomp, intervalMappingEquivalenceHomEquiv_family,
    intervalMappingEquivalenceHomEquiv_family, ← _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom_precomp, Category.assoc]

/-- 概要：順射がホモトピックな二つの写像空間同値は同じ Hom 対応を誘導する。
方針：Hom を族で表し、比較のホモトピーを族で前合成する。
規約：同値の逆射や逆則の選択は一致する必要がない。
使われ方：模型比較の選択による任意性を相殺する。 -/
lemma intervalMappingEquivalenceHomEquiv_eq_of_homotopy {A X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {x₀ x₁ : X _⦋0⦌} {y₀ y₁ : Y _⦋0⦌}
    (e d : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x₀ x₁) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace y₀ y₁))
    (H : SSet.Homotopy e.hom d.hom) :
    intervalMappingEquivalenceHomEquiv A e = intervalMappingEquivalenceHomEquiv A d := by
  apply Equiv.ext
  intro α
  obtain ⟨f, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom_surjective A X x₀ x₁ α
  rw [intervalMappingEquivalenceHomEquiv_family, intervalMappingEquivalenceHomEquiv_family]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalFamilyHom_eq_of_homotopy
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorIsoOfSimplicialHomotopy H) f).simplicialHomotopy

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
