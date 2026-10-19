module

public import SerrePositivity.InfinityCategories.F1B.KanRelativeLeftConstantFamily

/-!
概要：定値パラメータ族への後合成による絶対的な余極限の保存。
方針：終対象上の相対余極限に移し、関手圏の標準相対余極限を絶対条件へ戻す。
規約：パラメータに可縮性や quasicategory 性を要求しない。
使われ方：元の左 Kan 条件を全パラメータの Hom 判定へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：図式と余錐の値が等しければ余極限性は同値。
方針：図式の等式を消去し、余錐の部分型の外延性を使う。
規約：異なる表示の図式上の余錐も比較する。
使われ方：標準局所余錐の後合成の表示を揃える。 -/
lemma kanIsColimitCone_congr {J D : SSet.{u}} {p q : J ⟶ D} (hpq : p = q)
    (c : JoinCocone p) (d : JoinCocone q) (hcd : c.val = d.val) :
    IsColimitCone c ↔ IsColimitCone d := by
  subst q
  have he : c = d := Subtype.ext hcd
  rw [he]

/-- 概要：定値パラメータ族への写像は余極限余錐を保つ。
方針：終対象への射についての標準相対余極限と絶対条件の同値を使う。
規約：パラメータ A は任意の単体集合。
使われ方：局所 Kan 余極限をパラメータ付き関手圏へ移す。 -/
lemma kanIsColimitCone_constantFamily {A J D : SSet.{u}} [Quasicategory D]
    {p : J ⟶ D} (c : JoinCocone p) (hc : IsColimitCone c) :
    IsColimitCone (kanCoconeConstantFamily c A) := by
  let U := stdSimplex.isTerminalObj₀.from D
  have : InnerFibration U := (quasicategory_iff_of_isTerminal U stdSimplex.isTerminalObj₀).1
    inferInstance
  have hrel : IsRelativeColimitCone U c := kanIsRelativeColimitCone_of_lifting U c
    ((kanRelativeCoconeLifting_iff_isColimit_of_terminal U stdSimplex.isTerminalObj₀ c).2 hc)
  have hf := kanIsRelativeColimitCone_constantFamily (A := A) U c hrel
  have ht : IsTerminal ((ihom A).obj (Δ[0] : SSet.{u})) :=
    IsTerminal.isTerminalObj (ihom A) _ stdSimplex.isTerminalObj₀
  exact (kanRelativeCoconeLifting_iff_isColimit_of_terminal ((ihom A).map U) ht _).1
    (kanRelativeCoconeLifting_of_isRelativeColimitCone ((ihom A).map U) _ hf)

/-- 概要：標準局所余錐の余極限性は定値パラメータ族への後合成で保たれる。
方針：各局所余錐の後合成の厳密な式で定値族の余錐と比較する。
規約：δ とパラメータ A は任意。
使われ方：元の左 Kan 関手から出る写像空間の制限の全パラメータ判定。 -/
lemma kanLeftCanonicalColimits_constantFamily {A K C D : SSet.{u}} [Quasicategory D]
    (δ : K ⟶ C) (F : C ⟶ D)
    (hF : ∀ c : C _⦋0⦌, IsColimitCone (leftKanCanonicalCocone δ F c)) :
    ∀ c : C _⦋0⦌,
      IsColimitCone (leftKanCanonicalCocone δ (F ≫ constantFunctorMap A D) c) := by
  intro c
  have hc := kanIsColimitCone_constantFamily (A := A) (leftKanCanonicalCocone δ F c) (hF c)
  have hp : leftKanDiagram δ (δ ≫ F) c ≫ constantFunctorMap A D =
      leftKanDiagram δ (δ ≫ (F ≫ constantFunctorMap A D)) c := by
    simp only [leftKanDiagram, Category.assoc]
  have hv := (kanLeftCanonicalCocone_postcomp_val δ F (constantFunctorMap A D) c).symm
  exact (kanIsColimitCone_congr hp
    (kanCoconeConstantFamily (leftKanCanonicalCocone δ F c) A)
    (leftKanCanonicalCocone δ (F ≫ constantFunctorMap A D) c) hv).1 hc


end SerrePositivity.InfinityCategories.F1B
