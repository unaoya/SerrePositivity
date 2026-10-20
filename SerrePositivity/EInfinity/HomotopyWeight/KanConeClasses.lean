module

public import SerrePositivity.EInfinity.HomotopyWeight.KanConeComparison
public import SerrePositivity.EInfinity.HomotopyWeight.ConePoints
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

namespace SerrePositivity.EInfinity.HomotopyWeight

open CategoryTheory Limits
open SerrePositivity.DiagramModel.WeightedCones SerrePositivity.SimplicialModel

variable (K : Type u) [SmallCategory K]

/-- 概要：同じ各値の Kan 置換単位は図式射に自然（Hovey §5）。
方針：元の Kan 置換の自然性を各単体で評価する。
規約：元の図式の全射を保持する。
使われ方：元の錐の族を共通の Kan 図式へ送る式。 -/
lemma kanDiagramUnit_naturality {F G : K ⥤ SSet.{u}} (f : F ⟶ G) :
    f ≫ kanDiagramUnit K G = kanDiagramUnit K F ≫ kanDiagramMap K f := by
  ext k n x
  exact congrArg (fun q => (q.app n) x) (AnodyneKanReplacement.unit.naturality (f.app k))

variable (W : K ⥤ SSet.{u})

/-- 概要：共通図式への比較射は同じ族の錐の類へ送る（Hovey §5.4）。
方針：錐の類の後合成と Kan 置換単位の自然性を使う。
規約：元の射と単位の合成で作った同じ錐の類。
使われ方：共通図式内で両側の元の錐の類を照合する。 -/
lemma coneComparisonArrow_class {F H : K ⥤ SSet.{u}} (f : F ⟶ H) (s : W ⟶ F) :
    (coneComparisonArrow K W SSet.π₀Functor f) (coneClass K W s) =
      coneClass K W ((s ≫ f) ≫ kanDiagramUnit K H) := by
  change SSet.mapπ₀ ((coneSpace K W).map (kanDiagramMap K f))
    (SSet.mapπ₀ ((coneSpace K W).map (kanDiagramUnit K F)) (coneClass K W s)) = _
  rw [coneClass_map, coneClass_map]
  apply congrArg (coneClass K W)
  rw [Category.assoc, ← kanDiagramUnit_naturality, ← Category.assoc]

/-- 概要：両側の元の錐が共通図式で一致すれば比較同型は同じ類を結ぶ（Hovey §5.4）。
方針：比較の右側の像で判定し、二つの元の族の一致を使う。
規約：共通図式の値の Kan 性を仮定しない。
使われ方：具体的な通常の錐の正規化。 -/
lemma kanConeComparisonIso_class (hW : (boundaries K).rlp.llp (initial.to W))
    {F G H : K ⥤ SSet.{u}} (f : F ⟶ H) (g : G ⟶ H)
    (hF : ∀ k, SSet.KanComplex (F.obj k)) (hG : ∀ k, SSet.KanComplex (G.obj k))
    (hf : ∀ k, IsIso (AnodyneHomotopy.anodyneQ.map (f.app k)))
    (hg : ∀ k, IsIso (AnodyneHomotopy.anodyneQ.map (g.app k)))
    (s : W ⟶ F) (t : W ⟶ G) (h : s ≫ f = t ≫ g) :
    (kanConeComparisonIso K W hW SSet.π₀Functor PiZeroLocalization.inverts_anodyne
      f g hF hG hf hg).hom (coneClass K W s) = coneClass K W t := by
  let a := coneComparisonArrow K W SSet.π₀Functor g
  have : IsIso a := coneComparisonArrow_isIso K W hW SSet.π₀Functor
    PiZeroLocalization.inverts_anodyne g hG hg
  apply ((CategoryTheory.isIso_iff_bijective a).mp inferInstance).1
  have he := ConcreteCategory.congr_hom (kanConeComparisonIso_fac K W hW SSet.π₀Functor
    PiZeroLocalization.inverts_anodyne f g hF hG hf hg) (coneClass K W s)
  refine he.trans ?_
  change (coneComparisonArrow K W SSet.π₀Functor f) (coneClass K W s) =
    (coneComparisonArrow K W SSet.π₀Functor g) (coneClass K W t)
  rw [coneComparisonArrow_class, coneComparisonArrow_class, h]

end SerrePositivity.EInfinity.HomotopyWeight
