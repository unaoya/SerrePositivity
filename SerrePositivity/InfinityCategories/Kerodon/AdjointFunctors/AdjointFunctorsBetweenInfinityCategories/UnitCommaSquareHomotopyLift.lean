module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.SquareHomotopyTranspose
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.SquareBoundary
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitCommaSquareParameters
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitCommaSquareCoherenceReplacement

/-!
概要：全境界固定の関手正方形のホモトピーを時間付き comma 正方形へ持ち上げる。
方針：時間をパラメータへ転置し、固定四辺から新しい coherence を復元する。
規約：Y 側の標的は時間を忘れる前合成で一定にする。
使われ方：B1 の正方形の復元比較を写像空間の族のホモトピーへ戻す。

対応節は Kerodon 6.2（Tag 02EH）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories

/-- 概要：正方形のホモトピーを時間付き comma 正方形として表すデータ。
方針：時間付き正方形と、標的・関手表示の厳密な回収を保持する。
規約：時間をパラメータの第二因子に置く。
使われ方：写像空間の族のホモトピーの両端を検証する。 -/
structure UnitCommaSquareHomotopyLift {A X Y : SSet.{u}} {G : Y ⟶ X} {x : X _⦋0⦌}
    {v w : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber G x) _⦋0⦌} (s t : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitCommaFiberSquare G x v w A)
    (H : SSet.Homotopy s.functorSquare t.functorSquare) where
  square : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitCommaFiberSquare G x v w (A ⊗ (Δ[1] : SSet.{u}))
  target : square.target = ((Δ[1] : SSet.{u}) ◁ fst A (Δ[1] : SSet.{u})) ≫ s.target
  functorSquare : square.functorSquare = _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.diagramHomotopyTranspose H.h

/-- 概要：全境界固定の図式ホモトピーから時間付き comma 正方形を構成する。
方針：元の標的の時間一定の拡張と転置した図式の四辺を照合し、coherence を置き換える。
規約：X,Y の quasicategory 性は不要。
使われ方：正方形の比較を族のホモトピーとして実現する。 -/
noncomputable def unitCommaSquareHomotopyLift {A X Y : SSet.{u}} {G : Y ⟶ X} {x : X _⦋0⦌}
    {v w : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber G x) _⦋0⦌} (s t : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitCommaFiberSquare G x v w A)
    (H : SSet.Homotopy s.functorSquare t.functorSquare)
    (hH : (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.squareBoundary.ι ▷ (Δ[1] : SSet.{u})) ≫ H.h =
      fst _ (Δ[1] : SSet.{u}) ≫ _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.squareBoundary.ι ≫ s.functorSquare) :
    UnitCommaSquareHomotopyLift s t H := by
  let i := fst A (Δ[1] : SSet.{u})
  let s₀ := s.precomp i
  let P := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.diagramHomotopyTranspose H.h
  have hP : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.squareBoundary.ι ≫ P = _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.squareBoundary.ι ≫ s₀.functorSquare := by
    have hh := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.diagramHomotopyTranspose_restriction H.h _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.squareBoundary.ι
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.squareBoundary.ι ≫ s.functorSquare) hH
    change _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.squareBoundary.ι ≫ _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.diagramHomotopyTranspose H.h =
      _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.squareBoundary.ι ≫ (s.precomp i).functorSquare
    rw [s.precomp_functorSquare]
    simpa only [Category.assoc] using hh
  let Q : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionSquare
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberHomotopy (SSet.const v : A ⊗ (Δ[1] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber G x))
      s₀.targetHomotopy
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberHomotopy (SSet.const w : A ⊗ (Δ[1] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber G x)) :=
    { diagram := P
      bottom := (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.squareBoundary_restriction_edge hP _ _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.squareBoundary_range_bottom_le).trans
        s₀.functorSquare_bottom
      top := (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.squareBoundary_restriction_edge hP _ _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.squareBoundary_range_top_le).trans
        s₀.functorSquare_top
      left := (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.squareBoundary_restriction_edge hP _ _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.squareBoundary_range_left_le).trans
        s₀.functorSquare_left
      right := (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.squareBoundary_restriction_edge hP _ _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.squareBoundary_range_right_le).trans
        s₀.functorSquare_right }
  exact ⟨s₀.withFunctorSquare Q, s.precomp_target i, s₀.withFunctorSquare_functorSquare Q⟩

section
variable {A X Y : SSet.{u}} {G : Y ⟶ X} {x : X _⦋0⦌}
variable {v w : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber G x) _⦋0⦌} {s t : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitCommaFiberSquare G x v w A}
variable {H : SSet.Homotopy s.functorSquare t.functorSquare} (L : UnitCommaSquareHomotopyLift s t H)

/-- 概要：時間付き正方形を時間零で制限すると元の始点正方形。
方針：標的と関手正方形の二データを時間零で回収する。
規約：正方形の厳密な等式。
使われ方：族のホモトピーの始点。 -/
lemma UnitCommaSquareHomotopyLift.zero : L.square.precomp SSet.ι₀ = s := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitCommaFiberSquare.ext_functorSquare
  · rw [L.square.precomp_target, L.target, ← Category.assoc, ← MonoidalCategory.whiskerLeft_comp,
      SSet.ι₀_fst, MonoidalCategory.whiskerLeft_id, Category.id_comp]
  · rw [L.square.precomp_functorSquare, L.functorSquare, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.diagramHomotopyTranspose_zero]

/-- 概要：標的を共有する時間付き正方形を時間一で制限すると元の終点正方形。
方針：標的の一致と関手正方形の時間一の回収を使う。
規約：Y 側の標的の一致を明示的に受け取る。
使われ方：族のホモトピーの終点。 -/
lemma UnitCommaSquareHomotopyLift.one (ht : s.target = t.target) : L.square.precomp SSet.ι₁ = t := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitCommaFiberSquare.ext_functorSquare
  · rw [L.square.precomp_target, L.target, ← Category.assoc, ← MonoidalCategory.whiskerLeft_comp,
      SSet.ι₁_fst, MonoidalCategory.whiskerLeft_id, Category.id_comp]
    exact ht
  · rw [L.square.precomp_functorSquare, L.functorSquare, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.diagramHomotopyTranspose_one]

/-- 概要：標的を共有する全境界固定の正方形ホモトピーは写像空間の族のホモトピーになる。
方針：時間付き正方形を族へ戻し、両端の正方形の厳密な回収を使う。
規約：元の図式の変形そのものを転置し、Hom の等式から経路を取り直さない。
使われ方：B1 の正方形の復元比較から往復の族のホモトピーへ進む。 -/
noncomputable def UnitCommaSquareHomotopyLift.familyHomotopy (ht : s.target = t.target) :
    SSet.Homotopy s.family t.family where
  h := L.square.family
  h₀ := by rw [← L.square.precomp_family, L.zero]; rfl
  h₁ := by rw [← L.square.precomp_family, L.one ht]; rfl
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro a
    exact False.elim a.1.property

end

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories
