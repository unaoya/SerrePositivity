module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationInfinity

/-!
概要：固定した底上の対象からの相対関手空間による豊穣評価。
方針：相対合成を curry して Hom の作用を作り、単位則と結合則から豊穣関手則を得る。
規約：値域は Kan 複体の単体的圏、定義域は固定底上の left fibrations。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、strict transport の coherent な関手性。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：相対 Hom の後合成を豊穣 Hom の射として表す。
方針：二つの相対関手空間の合成を第一因子について curry する。
規約：a が評価の定義域、b と c が可変の標的。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、left fibrations の間の高次の射への評価の作用。 -/
def relativeFunctorPostHom {B : SSet.{u}} (a b c : Over B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace c.hom b.hom ⟶
      (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace b.hom a.hom)).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace c.hom a.hom) :=
  curry (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorComposition a b c)

/-- 概要：豊穣後合成は相対恒等射を恒等の内部 Hom の単位へ写す。
方針：uncurry して右単位則を使う。
規約：標的が同じ場合の豊穣関手の単位則。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、相対 Hom の豊穣評価の単位の整合性。 -/
lemma relativeFunctorPostHom_id {B : SSet.{u}} (a b : Over B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorIdentity b ≫ relativeFunctorPostHom a b b =
      MonoidalClosed.id (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace b.hom a.hom) := by
  apply uncurry_injective
  rw [relativeFunctorPostHom, uncurry_natural_left, uncurry_curry,
    MonoidalClosed.id_eq, uncurry_curry]
  apply (cancel_epi (ρ_ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace b.hom a.hom)).inv).1
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorComposition_id, Iso.inv_hom_id]

/-- 概要：二つの豊穣後合成の合成を uncurry すると二回の相対評価の合成になる。
方針：各次数・各パラメーターで閉構造の合成と評価を計算する。
規約：結合子の逆により三つの相対 Hom の括弧を揃える。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、豊穣評価の合成則の準備。 -/
lemma relativeFunctorPostHom_comp_uncurry {B : SSet.{u}} (a b c d : Over B) :
    uncurry ((relativeFunctorPostHom a b c ⊗ₘ relativeFunctorPostHom a c d) ≫
      MonoidalClosed.comp (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace b.hom a.hom)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace c.hom a.hom) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace d.hom a.hom)) =
    (α_ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace b.hom a.hom) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace c.hom b.hom)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace d.hom c.hom)).inv ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorComposition a b c ▷ _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorComposition a c d := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨x, f, g⟩
  apply Subtype.ext
  apply CategoryTheory.Functor.functorHom_ext
  intro e α
  apply ConcreteCategory.hom_ext
  intro y
  rfl

/-- 概要：相対 Hom の豊穣後合成は相対合成を保つ。
方針：uncurry して二回の評価の式に移し、相対合成の結合則を使う。
規約：四つの底上の対象の充填性は不要。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、豊穣評価の合成の整合性。 -/
lemma relativeFunctorPostHom_comp {B : SSet.{u}} (a b c d : Over B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorComposition b c d ≫ relativeFunctorPostHom a b d =
    (relativeFunctorPostHom a b c ⊗ₘ relativeFunctorPostHom a c d) ≫
      MonoidalClosed.comp (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace b.hom a.hom)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace c.hom a.hom) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace d.hom a.hom) := by
  apply uncurry_injective
  rw [relativeFunctorPostHom, uncurry_natural_left, uncurry_curry,
    relativeFunctorPostHom_comp_uncurry]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorComposition_assoc a b c d).symm

/-- 概要：固定した底上の対象からの相対 Hom は left fibrations の単体的圏から Kan 複体への豊穣関手。
方針：相対 Hom の後合成を Hom の作用とし、既存の相対単位則・結合則を使う。
規約：底 B の quasicategory 性は要求しない。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、strict transport の対象ごとの coherent な評価。 -/
def relativeFunctorEnrichedEvaluation {B : SSet.{u}} (a : Over B) :
    EnrichedFunctor SSet.{u} (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject B) _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u} where
  obj p := ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace p.val.hom a.hom, inferInstance⟩
  map p q := relativeFunctorPostHom a p.val q.val
  map_id p := relativeFunctorPostHom_id a p.val
  map_comp p q r := relativeFunctorPostHom_comp a p.val q.val r.val

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
