module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyWhiskering
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.KanBoundaryHomotopyFinalExtension
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.RelativeHomotopySharedFinal

/-!
概要：境界も移動する相対持ち上げを、境界を厳密に固定した持ち上げへ補正する。
方針：始域の境界円柱を終点固定で延長し、標的の同じ終点への二円柱を相対比較する。
規約：標的比較は境界上で全時刻定値。使われ方：有限相対持ち上げによる弱同値性の判定。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

/-- 概要：両円柱が境界で厳密に可換なら、境界を固定し標的比較も境界上で定値にできる。
方針：終点固定延長と共通終点への相対外ホーン充填。
規約：有限性不要、両対象は Kan。使われ方：実際の比較の境界固定相対持ち上げ。 -/
lemma relativeKanHomotopy_strictification {K X Y : SSet.{u}} [KanComplex X] [KanComplex Y]
    (A : K.Subcomplex) (f : X ⟶ Y) (a : (A : SSet.{u}) ⟶ X) (e : K ⟶ Y) (r : K ⟶ X)
    (he : A.ι ≫ e = a ≫ f) (L : SSet.Homotopy a (A.ι ≫ r))
    (G : SSet.Homotopy e (r ≫ f))
    (hG : (A.ι ▷ (Δ[1] : SSet.{u})) ≫ G.h = L.h ≫ f) :
    ∃ r' : K ⟶ X, A.ι ≫ r' = a ∧ ∃ T : SSet.Homotopy e (r' ≫ f),
      (A.ι ▷ (Δ[1] : SSet.{u})) ≫ T.h =
        fst (A : SSet.{u}) (Δ[1] : SSet.{u}) ≫ a ≫ f := by
  obtain ⟨r', hr', S, hS⟩ := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.kanComplex_extend_boundary_homotopy_final A r a L
  let V := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp S f
  let U : SSet.Homotopy (A.ι ≫ e) (A.ι ≫ (r ≫ f)) :=
    { h := L.h ≫ f
      h₀ := by
        change SSet.ι₀ ≫ L.h ≫ f = A.ι ≫ e
        rw [← Category.assoc, L.h₀, ← he]
      h₁ := by
        change SSet.ι₁ ≫ L.h ≫ f = A.ι ≫ (r ≫ f)
        rw [← Category.assoc, L.h₁, Category.assoc]
      rel := (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp L f).rel }
  have hV : (A.ι ▷ (Δ[1] : SSet.{u})) ≫ V.h = U.h := by
    change (A.ι ▷ (Δ[1] : SSet.{u})) ≫ (S.h ≫ f) = L.h ≫ f
    rw [← Category.assoc, hS]
  obtain ⟨T, hT⟩ := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.exists_relativeHomotopySharedFinal A G V U hG hV
  refine ⟨r', hr', T, ?_⟩
  rw [hT, he]

end SerrePositivity.InfinityCategories.Project.FilteredExchange
