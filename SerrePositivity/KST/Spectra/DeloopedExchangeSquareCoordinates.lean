module

public import SerrePositivity.KST.Spectra.DeloopedTracedExchange

/-!
概要：Ω 条件の厳密な可換式を、二重後合成と交換区間全体の同じ可換式へ移す。
方針：二重内部 Hom の合成保存と区間の前後合成の式を用いる。
規約：区間を再選択しない。使われ方：交換自然性の共通終辺・射影辺の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.KST.Spectra.LoopExchangePaths

/-- 元の二重後合成は、点つき射の厳密な合成を保つ。 -/
lemma doublePost_comp {A B C : PointedSimplicialSet.{u}} (f : A ⟶ B) (g : B ⟶ C) :
    doublePost f ≫ doublePost g = doublePost (f ≫ g) := by
  change (ihom CirclePower.space.{u}).map ((ihom CirclePower.space.{u}).map f) ≫
      (ihom CirclePower.space.{u}).map ((ihom CirclePower.space.{u}).map g) =
    (ihom CirclePower.space.{u}).map ((ihom CirclePower.space.{u}).map (f ≫ g))
  simp only [Functor.map_comp]

/-- 二つの Ω 条件の可換式は、元の二重後合成の可換式へ厳密に移る。 -/
lemma doublePost_square {Y Y' Z Z' : PointedSimplicialSet.{u}}
    (h : Y ⟶ PointedObject.basedHom CirclePower.space.{u} Z)
    (h' : Y' ⟶ PointedObject.basedHom CirclePower.space.{u} Z')
    (v : Y ⟶ Y') (w : Z ⟶ Z')
    (hc : h ≫ PointedObject.basedHomMap CirclePower.space.{u} w = v ≫ h') :
    doublePost h ≫ TripleCircle.loopPost w = doublePost v ≫ doublePost h' := by
  change doublePost h ≫ doublePost (PointedObject.basedHomMap CirclePower.space.{u} w) = _
  rw [doublePost_comp, doublePost_comp, hc]

end LoopExchangePaths
namespace PointedMapping.VerticalPath

/-- 区間への二度の後合成は、元の合成射への一度の後合成と辺全体で一致する。 -/
lemma basedPost_basedPost_path {A E V W : PointedSimplicialSet.{u}} {f g : A ⟶ E}
    (P : VerticalPath (PointedObject.toPoint E) f g) (a : E ⟶ V) (b : V ⟶ W) :
    ((P.basedPost a).basedPost b).path = (P.basedPost (a ≫ b)).path := by
  change (P.path ≫ (PointedObject.basedHomMap A a).right) ≫
      (PointedObject.basedHomMap A b).right =
    P.path ≫ (PointedObject.basedHomMap A (a ≫ b)).right
  have hc := (ihom A).map_comp a b
  change PointedObject.basedHomMap A (a ≫ b) =
    PointedObject.basedHomMap A a ≫ PointedObject.basedHomMap A b at hc
  simpa only [Under.comp_right, Category.assoc] using
    congrArg (fun q => P.path ≫ q.right) hc.symm

end PointedMapping.VerticalPath
end SerrePositivity.KST.Spectra
