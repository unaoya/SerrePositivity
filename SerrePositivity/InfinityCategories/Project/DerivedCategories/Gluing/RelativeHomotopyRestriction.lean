module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.RelativePrismHomotopyPrecomp
/-! # 指定部分図式上の相対固定を因子分解へ移す

概要：指定部分図式で固定された比較を、その部分図式を経る全入力へ制限する。
方針：元の相対等式を同じパラメーター点で評価し、因子分解等式を使う。
規約：時間方向の固定等式を保持し、相対比較の存在は要求しない。
使われ方：供給待ちの内角相対比較から、単位対角の四辺固定を取り出す。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped _root_.Simplicial
lemma dgGluingRelativeHomotopy_restrict_fixed {A B C D Z : SSet.{u}}
    {F G : B ⟶ Z} (H : SSet.Homotopy F G) (i : A ⟶ B)
    (hH : (i ▷ (Δ[1] : SSet.{u})) ≫ H.h = fst A Δ[1] ≫ i ≫ G)
    (j : C ⟶ B) (p : D ⟶ C) (a : D ⟶ A) (e : p ≫ j = a ≫ i) :
    (p ▷ (Δ[1] : SSet.{u})) ≫ (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp H j).h =
      fst D Δ[1] ≫ p ≫ j ≫ G := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  have he := congrArg (fun q => q.app n s.1) e
  change j.app n (p.app n s.1) = i.app n (a.app n s.1) at he
  have hh := congrArg (fun q => q.app n (a.app n s.1, s.2)) hH
  change H.h.app n (i.app n (a.app n s.1), s.2) = G.app n (i.app n (a.app n s.1)) at hh
  change H.h.app n (j.app n (p.app n s.1), s.2) = G.app n (j.app n (p.app n s.1))
  rw [he]
  exact hh
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
