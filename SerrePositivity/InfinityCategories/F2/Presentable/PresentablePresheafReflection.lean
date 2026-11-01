module

public import SerrePositivity.InfinityCategories.F2.Presentable.IndPresheafReflection
public import SerrePositivity.InfinityCategories.F1B.QCatEquivalenceAdjunction
public import SerrePositivity.InfinityCategories.Core.EquivalenceCalculus

/-!
概要：presentable 圏自体を前層圏の充満忠実な右随伴の像として表す。
方針：小さい compact 生成圏の Ind 反映と、元の全同値の随伴を合成する。
規約：元の圏を別の定義へ置き換えず、全関手の随伴と充満忠実性を供給する。
使われ方：小余極限の反映計算と随伴関手定理。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2.Presentable
open Ind

/-- 概要：presentable 圏は小さい底の前層圏の反映像となる。
方針：構成した Ind 反映を元の全同値へ合成する。
規約：反映の存在や右随伴の充満忠実性を追加入力にしない。
使われ方：元の presentable 圏での小余極限と小極限の計算。 -/
lemma IsPresentable.exists_presheafReflection {C : SSet.{u + 1}} [Quasicategory C]
    (hC : IsPresentable C) :
    ∃ (A : SSet.{u}) (hA : Quasicategory A), letI := hA
      ∃ (L : PresheafInfinity A ⟶ C) (R : C ⟶ PresheafInfinity A),
        Nonempty (QCatAdjunction L R) ∧ IsFullyFaithful R ∧ PreservesSmallColimits L := by
  obtain ⟨κ, hκ, A, hA, ⟨r⟩, ⟨e⟩⟩ := hC.exists_reflectiveIndModel
  have := hA
  let a := r.adjunction.comp e.toAdjunction
  refine ⟨A, hA, r.reflector ≫ e.hom, e.inv ≫ indInclusionPresheaf κ A,
    ⟨a⟩, ?_, adjunction_preservesSmallColimits a⟩
  exact e.symm.isQCatEquivalence.isFullyFaithful.comp (indInclusionPresheaf_isFullyFaithful κ A)

/-- 概要：反映 Ind 模型の同じ全同値によって元の圏の全小余極限を構成する。
方針：前層余極限を反映してから元の圏へ輸送する。
規約：元の圏の余完備性を入力に追加しない。
使われ方：presentable の反映表示による余極限の具体的構成。 -/
lemma reflectiveIndModel_hasSmallColimits {κ : Cardinal.{u}} {A : SSet.{u}}
    [Quasicategory A] {C : SSet.{u + 1}} [Quasicategory C]
    (r : ReflectiveSubcategory (PresheafInfinity A) (IsIndVertex κ A))
    (e : QCatEquivalence (IndInfinity κ A) C) : HasSmallColimits C :=
  (reflectiveSubcategory_hasSmallColimits r (presheaf_hasSmallColimits A)).of_equivalence e


end SerrePositivity.InfinityCategories.F2.Presentable
