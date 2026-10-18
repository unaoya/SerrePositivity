module
public import SerrePositivity.KST.ProExcision.NerveOppositeSimplex

/-!
# 反対圏の nerve の反転への実単体写像

概要：反対圏の nerve を元の圏の nerve の順序反転へ送る実単体射を構成する。
方針：可合成射の列の反転と任意の単体射の rev の可換性を使う。
規約：KST Proposition 4.14、SW92 §1.2。二つの単体方向を混同しない。
使われ方：行側の対角 bar の実比較。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Opposite
variable (C : Type u) [Category.{v} C]

/-- 概要：薄い有限添字圏の等しい端点の射の像は反対向きに移しても異種等号で一致する。
方針：端点の等号を消去し、添字圏の射の一意性を使う。
規約：SW92 §1.2 の実単体比較。使われ方：rev による端点の輸送の整合。 -/
lemma oppositeFunctorMap_heq {N : ℕ} (F : Fin N ⥤ Cᵒᵖ)
    {i j i' j' : Fin N} (hi : i = i') (hj : j = j') (f : i ⟶ j) (g : i' ⟶ j') :
    (F.map f).unop ≍ (F.map g).unop := by
  subst i'
  subst j'
  obtain rfl := Subsingleton.elim f g
  rfl

/-- 概要：反対圏の nerve から元の nerve の順序反転への実単体射。
方針：単体ごとに列の順序と矢印を反転し、面・退化に自然であることを示す。
規約：SW92 §1.2 の反対 bar 比較。使われ方：自然な実同型の正方向。 -/
def nerveOppositeMap : nerve Cᵒᵖ ⟶ (nerve C).op where
  app k := ↾fun F ↦ SSet.opObjEquiv.symm (oppositeNerveSimplex F)
  naturality {k l} φ := by
    apply ConcreteCategory.hom_ext
    intro F
    change ComposableArrows Cᵒᵖ k.unop.len at F
    change oppositeNerveSimplex
        (F.whiskerLeft (SimplexCategory.toCat.map φ.unop).toFunctor) =
      (oppositeNerveSimplex F).whiskerLeft
        (SimplexCategory.toCat.map (SimplexCategory.rev.map φ.unop)).toFunctor
    apply CategoryTheory.Functor.hext
    case h_obj =>
      intro i
      change unop (F.obj (φ.unop.toOrderHom i.rev)) =
        unop (F.obj ((SimplexCategory.rev.map φ.unop).toOrderHom i).rev)
      simp only [SimplexCategory.rev_map_apply, Fin.rev_rev]
      rfl
    case h_map =>
      intro i j h
      change HEq
        (F.map (homOfLE (φ.unop.toOrderHom.monotone (Fin.rev_le_rev.mpr (leOfHom h))))).unop
        (F.map (homOfLE (Fin.rev_le_rev.mpr
          ((SimplexCategory.rev.map φ.unop).toOrderHom.monotone (leOfHom h))))).unop
      exact oppositeFunctorMap_heq C F
        (by simp only [SimplexCategory.rev_map_apply, Fin.rev_rev]; rfl)
        (by simp only [SimplexCategory.rev_map_apply, Fin.rev_rev]; rfl) _ _

end SerrePositivity.KST.ProExcision
