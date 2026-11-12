module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.TotalKanProductComparison
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyWhiskering

/-!
概要：底で一致する二つの指定ホモトピーを、引き戻し内のホモトピーへまとめる。
方針：円柱全体に引き戻しの普遍性を適用し、両端を射影で照合する。
規約：底の円柱は厳密に一致することを要求する。
使われ方：共通境界を貼った有限検出から積比較の単射性を証明する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：二射影のホモトピーが底で一致すれば引き戻し内のホモトピーを得る。
方針：元の二つの円柱を pullback.lift で貼る。
規約：両端は指定された元の二射。使われ方：fiber 輸送の境界の整合。 -/
def pullbackHomotopy {A E D B : SSet.{u}} (p : E ⟶ B) (q : D ⟶ B)
    {a a' : A ⟶ pullback p q}
    (H : SSet.Homotopy (a ≫ pullback.fst p q) (a' ≫ pullback.fst p q))
    (G : SSet.Homotopy (a ≫ pullback.snd p q) (a' ≫ pullback.snd p q))
    (h : H.h ≫ p = G.h ≫ q) : SSet.Homotopy a a' where
  h := pullback.lift H.h G.h h
  h₀ := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, H.h₀]; rfl
    · rw [Category.assoc, pullback.lift_snd, G.h₀]; rfl
  h₁ := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, H.h₁]; rfl
    · rw [Category.assoc, pullback.lift_snd, G.h₁]; rfl
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

/-- 概要：組み合わせたホモトピーの第一射影は元の円柱そのもの。
方針：引き戻しの射影公式。規約：全時刻で一致。使われ方：境界の輸送の追跡。 -/
lemma pullbackHomotopy_fst {A E D B : SSet.{u}} (p : E ⟶ B) (q : D ⟶ B)
    {a a' : A ⟶ pullback p q}
    (H : SSet.Homotopy (a ≫ pullback.fst p q) (a' ≫ pullback.fst p q))
    (G : SSet.Homotopy (a ≫ pullback.snd p q) (a' ≫ pullback.snd p q))
    (h : H.h ≫ p = G.h ≫ q) : (pullbackHomotopy p q H G h).h ≫ pullback.fst p q = H.h :=
  pullback.lift_fst _ _ _

/-- 概要：組み合わせたホモトピーの第二射影は元の円柱そのもの。
方針：引き戻しの射影公式。規約：全時刻で一致。使われ方：境界の輸送の追跡。 -/
lemma pullbackHomotopy_snd {A E D B : SSet.{u}} (p : E ⟶ B) (q : D ⟶ B)
    {a a' : A ⟶ pullback p q}
    (H : SSet.Homotopy (a ≫ pullback.fst p q) (a' ≫ pullback.fst p q))
    (G : SSet.Homotopy (a ≫ pullback.snd p q) (a' ≫ pullback.snd p q))
    (h : H.h ≫ p = G.h ≫ q) : (pullbackHomotopy p q H G h).h ≫ pullback.snd p q = G.h :=
  pullback.lift_snd _ _ _

end SerrePositivity.InfinityCategories.F2
