module

public import SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.KanConeComparison
public import SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.ConePoints
public import SerrePositivity.HomotopicalAlgebra.Simplicial.PiZeroLocalization

/-!
# 共通図式で一致する錐の類と比較同型

概要：Hovey §5.4 の両側の錐比較は共通図式で一致する元の錐の類を保つ。
方針：同じ Kan 置換単位の自然性と比較同型の可換三角形を使う。
規約：元の族を保持し、共通図式の Kan 性は要求しない。
使われ方：通常の錐の始域 frame と右 frame のクラス照合。
-/

@[expose] public section

noncomputable section

universe u

namespace SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.SerrePositivity.DiagramModel.WeightedCones _root_.SerrePositivity.SimplicialModel

variable (K : Type u) [SmallCategory K]

/-- 概要：同じ各値の Kan 置換単位は図式射に自然（Hovey §5）。
方針：元の Kan 置換の自然性を各単体で評価する。
規約：元の図式の全射を保持する。
使われ方：元の錐の族を共通の Kan 図式へ送る式。 -/
lemma kanDiagramUnit_naturality {F G : K ⥤ SSet.{u}} (f : F ⟶ G) :
    f ≫ _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.kanDiagramUnit K G = _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.kanDiagramUnit K F ≫ _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.kanDiagramMap K f := by
  ext k n x
  exact congrArg (fun q => (q.app n) x) (AnodyneKanReplacement.unit.naturality (f.app k))

variable (W : K ⥤ SSet.{u})

/-- 概要：共通図式への比較射は同じ族の錐の類へ送る（Hovey §5.4）。
方針：錐の類の後合成と Kan 置換単位の自然性を使う。
規約：元の射と単位の合成で作った同じ錐の類。
使われ方：共通図式内で両側の元の錐の類を照合する。 -/
lemma coneComparisonArrow_class {F H : K ⥤ SSet.{u}} (f : F ⟶ H) (s : W ⟶ F) :
    (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.coneComparisonArrow K W SSet.π₀Functor f) (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.coneClass K W s) =
      _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.coneClass K W ((s ≫ f) ≫ _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.kanDiagramUnit K H) := by
  change SSet.mapπ₀ ((coneSpace K W).map (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.kanDiagramMap K f))
    (SSet.mapπ₀ ((coneSpace K W).map (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.kanDiagramUnit K F)) (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.coneClass K W s)) = _
  rw [_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.coneClass_map, _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.coneClass_map]
  apply congrArg (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.coneClass K W)
  rw [Category.assoc, ← _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.kanDiagramUnit_naturality, ← Category.assoc]

/-- 概要：両側の元の錐が共通図式で一致すれば比較同型は同じ類を結ぶ（Hovey §5.4）。
方針：比較の右側の像で判定し、二つの元の族の一致を使う。
規約：共通図式の値の Kan 性を仮定しない。
使われ方：具体的な通常の錐の正規化。 -/
lemma kanConeComparisonIso_class (hW : (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.boundaries K).rlp.llp (initial.to W))
    {F G H : K ⥤ SSet.{u}} (f : F ⟶ H) (g : G ⟶ H)
    (hF : ∀ k, SSet.KanComplex (F.obj k)) (hG : ∀ k, SSet.KanComplex (G.obj k))
    (hf : ∀ k, IsIso (AnodyneHomotopy.anodyneQ.map (f.app k)))
    (hg : ∀ k, IsIso (AnodyneHomotopy.anodyneQ.map (g.app k)))
    (s : W ⟶ F) (t : W ⟶ G) (h : s ≫ f = t ≫ g) :
    (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.kanConeComparisonIso K W hW SSet.π₀Functor PiZeroLocalization.inverts_anodyne
      f g hF hG hf hg).hom (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.coneClass K W s) = _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.coneClass K W t := by
  let a := _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.coneComparisonArrow K W SSet.π₀Functor g
  have : IsIso a := _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.coneComparisonArrow_isIso K W hW SSet.π₀Functor
    PiZeroLocalization.inverts_anodyne g hG hg
  apply ((CategoryTheory.isIso_iff_bijective a).mp inferInstance).1
  have he := ConcreteCategory.congr_hom (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.kanConeComparisonIso_fac K W hW SSet.π₀Functor
    PiZeroLocalization.inverts_anodyne f g hF hG hf hg) (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.coneClass K W s)
  refine he.trans ?_
  change (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.coneComparisonArrow K W SSet.π₀Functor f) (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.coneClass K W s) =
    (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.coneComparisonArrow K W SSet.π₀Functor g) (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.coneClass K W t)
  rw [_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.coneComparisonArrow_class, _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.coneComparisonArrow_class, h]

end SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight
