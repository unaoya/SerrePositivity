module

public import SerrePositivity.KST.Spectra.PointedHomotopyClasses

/-!
概要：点つき curry' の非基点側の単位射は、元のパラメータ族の同じ頂点を表す。
方針：既存の familyVertex と閉構造の頂点の厳密同定を用いる。
規約：Kan 性は不要。使われ方：companion の円の射と元の BK 切断点の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra.PointedMapping

/-- 点つき閉構造の単位射の頂点は、元の写像族の頂点そのもの。 -/
lemma unitUnderlyingHom_curry'_vertex {X Y : PointedSimplicialSet.{u}} (f : X ⟶ Y) :
    SSet.unitHomEquiv _
      (PointedSimplicialSet.unitUnderlyingHom (PointedObject.basedHom X Y) (curry' f)) =
        familyVertex f := by
  rw [familyVertex_eq_pointedHomVertex]
  rfl

/-- 元の単位の点の射を後合成すると、頂点の後合成そのものを得る。 -/
lemma unitHomEquiv_post {X Y : SSet.{u}} (p : 𝟙_ SSet.{u} ⟶ X) (f : X ⟶ Y) :
    SSet.unitHomEquiv Y (p ≫ f) = f.app (Opposite.op ⦋0⦌) (SSet.unitHomEquiv X p) := rfl

end SerrePositivity.KST.Spectra.PointedMapping
