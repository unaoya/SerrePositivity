module

public import SerrePositivity.KST.Spectra.PointedMappingFamilyVertices

/-!
概要：点つき射の基点固定ホモトピーと、内部 Hom の辺の対応。
方針：相対 curry の区間の両端点を計算し、逆向きは辺を uncurry する。
規約：Kan 性は対応そのものには不要。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.2（Tag 00VJ）。写像空間の連結成分の具体的な計算。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra.PointedMapping

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X Y : PointedSimplicialSet.{u}} {f g : X ⟶ Y}
  (H : SSet.Homotopy f.right g.right)
  (hH : X.hom ▷ (Δ[1] : SSet.{u}) ≫ H.h =
    toUnit (𝟙_ SSet.{u} ⊗ (Δ[1] : SSet.{u})) ≫ Y.hom)

/-- 概要：基点固定ホモトピーの curry の始点は始点射の定数な零次パラメータ族。
方針：包含後で通常の curry の自然性と始点の式を使う。
規約：区間の始点は面添字一。
使われ方：Goerss–Jardine I §7。内部 Hom の辺の始点。 -/
theorem paramCurry_homotopy_zero :
    stdSimplex.δ (1 : Fin 2) ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.paramCurry X Y H.h hH = pointFamily f := by
  have h₀ : SSet.ι₀ ≫ H.h = f.right := H.h₀
  have hface : X.right ◁ stdSimplex.δ (1 : Fin 2) ≫ H.h =
      fst X.right (Δ[0] : SSet.{u}) ≫ f.right := by
    rw [stdSimplex.δ_one_eq_const]
    change (fst X.right (Δ[0] : SSet.{u}) ≫ SSet.ι₀) ≫ H.h = _
    rw [Category.assoc, h₀]
  apply (cancel_mono (PointedObject.basedHomι X Y)).1
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.paramCurry_ι, pointFamily, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.paramCurry_ι,
    ← MonoidalClosed.curry_natural_left, hface]

/-- 概要：基点固定ホモトピーの curry の終点は終点射の定数な零次パラメータ族。
方針：包含後で通常の curry の自然性と終点の式を使う。
規約：区間の終点は面添字零。
使われ方：Goerss–Jardine I §7。内部 Hom の辺の終点。 -/
theorem paramCurry_homotopy_one :
    stdSimplex.δ (0 : Fin 2) ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.paramCurry X Y H.h hH = pointFamily g := by
  have h₁ : SSet.ι₁ ≫ H.h = g.right := H.h₁
  have hface : X.right ◁ stdSimplex.δ (0 : Fin 2) ≫ H.h =
      fst X.right (Δ[0] : SSet.{u}) ≫ g.right := by
    rw [stdSimplex.δ_zero_eq_const]
    change (fst X.right (Δ[0] : SSet.{u}) ≫ SSet.ι₁) ≫ H.h = _
    rw [Category.assoc, h₁]
  apply (cancel_mono (PointedObject.basedHomι X Y)).1
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.paramCurry_ι, pointFamily, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.paramCurry_ι,
    ← MonoidalClosed.curry_natural_left, hface]

/-- 概要：基点固定ホモトピーが表す点つき内部 Hom の辺。
方針：区間族を curry して Yoneda で一次単体へ移す。
規約：始点と終点は familyVertex で表した射。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.2（Tag 00VJ）。点つきホモトピーを π₀ の等式へ移す。 -/
def edgeOfHomotopy : (PointedObject.basedHom X Y).right.Edge (familyVertex f) (familyVertex g) :=
  SSet.Edge.mk (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.paramCurry X Y H.h hH))
    (by
      rw [← stdSimplex.yonedaEquiv_δ_comp, paramCurry_homotopy_zero]
      rfl)
    (by
      rw [← stdSimplex.yonedaEquiv_δ_comp, paramCurry_homotopy_one]
      rfl)

variable {H hH}

/-- 概要：内部 Hom の辺は点つき射間の区間ホモトピーを与える。
方針：辺の Yoneda の逆を uncurry し、零次パラメータで端点を評価する。
規約：基点固定条件は homotopyOfEdge_base に保持する。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.2（Tag 00VJ）。π₀ の辺から実際の写像の比較へ戻す。 -/
def homotopyOfEdge (e : (PointedObject.basedHom X Y).right.Edge (familyVertex f) (familyVertex g)) :
    SSet.Homotopy f.right g.right where
  h := MonoidalClosed.uncurry (SSet.yonedaEquiv.symm e.edge ≫ PointedObject.basedHomι X Y)
  h₀ := by
    have hι : SSet.ι₀ (X := X.right) = zeroSection X.right ≫
        X.right ◁ stdSimplex.δ (1 : Fin 2) := rfl
    rw [hι, Category.assoc, ← MonoidalClosed.uncurry_natural_left,
      SSet.Edge.δ_one_yonedaEquiv_symm_assoc]
    change (familyMap X Y (familyVertex f)).right = f.right
    exact congrArg Under.Hom.right (familyMap_familyVertex f)
  h₁ := by
    have hι : SSet.ι₁ (X := X.right) = zeroSection X.right ≫
        X.right ◁ stdSimplex.δ (0 : Fin 2) := rfl
    rw [hι, Category.assoc, ← MonoidalClosed.uncurry_natural_left,
      SSet.Edge.δ_zero_yonedaEquiv_symm_assoc]
    change (familyMap X Y (familyVertex g)).right = g.right
    exact congrArg Under.Hom.right (familyMap_familyVertex g)
  rel := by ext m ⟨⟨z, hz⟩, t⟩; exact hz.elim

/-- 概要：内部 Hom の辺から得たホモトピーは全区間で基点を固定する。
方針：点つき内部 Hom の等化子条件の uncurry を使う。
規約：標的の Kan 性は不要。
使われ方：Kerodon §3.2.2（Tag 00VJ）。球面へ戻すホモトピーの相対条件。 -/
theorem homotopyOfEdge_base
    (e : (PointedObject.basedHom X Y).right.Edge (familyVertex f) (familyVertex g)) :
    X.hom ▷ (Δ[1] : SSet.{u}) ≫ (homotopyOfEdge e).h =
      toUnit (𝟙_ SSet.{u} ⊗ (Δ[1] : SSet.{u})) ≫ Y.hom :=
  _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.uncurry_basepoint X Y (SSet.yonedaEquiv.symm e.edge)

end

end SerrePositivity.KST.Spectra.PointedMapping
