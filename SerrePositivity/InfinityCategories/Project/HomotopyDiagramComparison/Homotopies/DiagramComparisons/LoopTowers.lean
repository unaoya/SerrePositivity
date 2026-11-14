module

public import Mathlib.CategoryTheory.Adjunction.Limits
public import SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.SuspensionLoop
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.DiagramComparisons.PointedTowers
public import SerrePositivity.Spectra.Pointed.Basic
public import SerrePositivity.Spectra.Pointed.InternalHom
public import SerrePositivity.Spectra.Pointed.Smash
public import SerrePositivity.Spectra.PointedSimplicialSet.Basic
public import SerrePositivity.Spectra.PointedSimplicialSet.InternalHom
public import SerrePositivity.Spectra.PointedSimplicialSet.Spheres

/-!
概要：loop は点つき塔の明示的極限を保存する。
方針：loop を写した錐と loop の塔の整合族の錐の普遍性を比較する。
規約：通常の厳密同型であり Kan 性や fibration 性は要求しない。
使われ方：BF 1978 §2、HA §1.4.2、HTT 4.2.4.1、Sp の塔の Ω 条件。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open SerrePositivity.KST.Spectra
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section

local instance : (PointedObject.basedHomFunctor PointedSimplicialSet.circle.{u}).IsRightAdjoint :=
  (PointedSimplicialSet.smashHomAdjunction PointedSimplicialSet.circle.{u}).isRightAdjoint

/-- 概要：loop の塔の明示的極限を頂点とする錐。
方針：loop による遷移と整合族の射影を使う。
規約：図式は元の塔の図式に loop を後合成したもの。
使われ方：二種類の極限の標準同型の標的の錐。 -/
def loopTowerCone (X : ℕ → PointedSimplicialSet.{u})
    (d : ∀ n, X (n + 1) ⟶ X n) :
    Cone (Functor.ofOpSequence d ⋙
      PointedObject.basedHomFunctor PointedSimplicialSet.circle.{u}) where
  pt := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointedTowerLimit (fun n ↦ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace (X n))
    (fun n ↦ PointedObject.basedHomMap PointedSimplicialSet.circle.{u} (d n))
  π := NatTrans.ofOpSequence
    (fun n ↦ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointedTowerProjection (fun n ↦ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace (X n))
      (fun n ↦ PointedObject.basedHomMap PointedSimplicialSet.circle.{u} (d n)) n) (fun n ↦ by
      change 𝟙 _ ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointedTowerProjection (fun n ↦ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace (X n))
        (fun n ↦ PointedObject.basedHomMap PointedSimplicialSet.circle.{u} (d n)) n =
        _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointedTowerProjection (fun n ↦ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace (X n))
          (fun n ↦ PointedObject.basedHomMap PointedSimplicialSet.circle.{u} (d n)) (n + 1) ≫
          (PointedObject.basedHomFunctor PointedSimplicialSet.circle.{u}).map
            ((Functor.ofOpSequence d).map (homOfLE (Nat.le_succ n)).op)
      rw [Category.id_comp, Functor.ofOpSequence_map_homOfLE_succ]
      exact (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointedTowerProjection_comp _ _ n).symm)

/-- 概要：loop の塔の明示的な錐は極限錐。
方針：任意の錐の隣接段の整合条件を使って整合族へ持ち上げる。
規約：元の図式に loop を後合成した図式の通常の極限性。
使われ方：loop と塔の極限の標準比較同型。 -/
def loopTowerCone_isLimit (X : ℕ → PointedSimplicialSet.{u})
    (d : ∀ n, X (n + 1) ⟶ X n) : IsLimit (loopTowerCone X d) where
  lift c := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointedTowerLift _ _ (fun n ↦ c.π.app (Opposite.op n)) (fun n ↦ by
    have h := c.w (homOfLE (Nat.le_succ n)).op
    rw [Functor.comp_map, Functor.ofOpSequence_map_homOfLE_succ] at h
    change c.π.app (Opposite.op (n + 1)) ≫
      PointedObject.basedHomMap PointedSimplicialSet.circle.{u} (d n) =
        c.π.app (Opposite.op n) at h
    exact h)
  fac c j := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointedTowerLift_projection _ _ _ _ j.unop
  uniq c m hm := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointedTowerLimit_hom_ext _ _ (fun n ↦ by
    exact (hm (Opposite.op n)).trans
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointedTowerLift_projection (fun n ↦ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace (X n))
        (fun n ↦ PointedObject.basedHomMap PointedSimplicialSet.circle.{u} (d n))
        (fun n ↦ c.π.app (Opposite.op n)) _ n).symm)

/-- 概要：点つき塔の極限の loop と loop の塔の極限の標準同型。
方針：右随伴による極限保存と明示的な極限錐の一意性を使う。
規約：順射は各射影に loop を適用した射を成分に持つ。
使われ方：Sp の塔の随伴構造射を塔の π_* 比較へ移す。 -/
def loopTowerIso (X : ℕ → PointedSimplicialSet.{u})
    (d : ∀ n, X (n + 1) ⟶ X n) :
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointedTowerLimit X d) ≅
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointedTowerLimit (fun n ↦ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace (X n))
        (fun n ↦ PointedObject.basedHomMap PointedSimplicialSet.circle.{u} (d n)) :=
  (isLimitOfPreserves (PointedObject.basedHomFunctor PointedSimplicialSet.circle.{u})
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointedTowerCone_isLimit X d)).conePointUniqueUpToIso (loopTowerCone_isLimit X d)

/-- 概要：loop と塔の同型の各射影は元の射影への loop の作用。
方針：極限錐の一意同型の成分の計算を使う。
規約：全ての自然数の段での厳密な点つき射の等式。
使われ方：極限の随伴構造射の成分計算。 -/
lemma loopTowerIso_hom_projection (X : ℕ → PointedSimplicialSet.{u})
    (d : ∀ n, X (n + 1) ⟶ X n) (n : ℕ) :
    (loopTowerIso X d).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointedTowerProjection _ _ n =
      PointedObject.basedHomMap PointedSimplicialSet.circle.{u} (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointedTowerProjection X d n) :=
  (isLimitOfPreserves (PointedObject.basedHomFunctor PointedSimplicialSet.circle.{u})
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointedTowerCone_isLimit X d)).conePointUniqueUpToIso_hom_comp
      (loopTowerCone_isLimit X d) (Opposite.op n)

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
