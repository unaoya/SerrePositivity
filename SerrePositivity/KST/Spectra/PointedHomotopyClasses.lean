module

public import SerrePositivity.KST.Spectra.PointedVertexComparison
public import SerrePositivity.KST.Spectra.PointedMappingComponents

/-!
概要：点つき射のホモトピー類の合成と suspension に関する整合性。
方針：頂点の二つの表示を比較し、実際の写像空間の射を π₀ へ送る。
規約：成分の操作の定義に Kan 性は要求しない。
使われ方：BF 1978 §2、HTT A.3.3、Goerss–Jardine I §7。段の比較の厳密化。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory SSet

namespace SerrePositivity.KST.Spectra.PointedMapping

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：パラメータ族による頂点は点つき閉構造による頂点と一致する。
方針：点のパラメータ族の射を単位の非基点側の射と比較する。
規約：Kan 性を仮定しない。
使われ方：BF 1978 §2、Goerss–Jardine I §7。suspension と通常のホモトピーの表示の接続。 -/
theorem familyVertex_eq_pointedHomVertex {X Y : PointedSimplicialSet.{u}} (f : X ⟶ Y) :
    familyVertex f = pointedHomVertexEquiv X Y f := by
  dsimp only [familyVertex]
  rw [pointFamily_closed]
  rfl

/-- 概要：実際の点つき射が表す写像空間の連結成分。
方針：通常のパラメータ族の頂点の類を取る。
規約：定義は全ての点つき単体集合の間の射に適用できる。
使われ方：Goerss–Jardine I §7。ホモトピー可換な構造式の表記。 -/
def componentOf {X Y : PointedSimplicialSet.{u}} (f : X ⟶ Y) :
    π₀ (PointedObject.basedHom X Y).right := π₀.mk (familyVertex f)

/-- 概要：標的での後合成は射の成分の等式を保存する。
方針：内部 Hom の後合成を π₀ へ送る。
規約：合成する射は任意。
使われ方：Goerss–Jardine I §7。構造可換式のホモトピーによる修正。 -/
theorem componentOf_comp_right {X Y Z : PointedSimplicialSet.{u}}
    {f g : X ⟶ Y} (h : componentOf f = componentOf g) (p : Y ⟶ Z) :
    componentOf (f ≫ p) = componentOf (g ≫ p) := by
  have hh := congrArg (mapπ₀ (PointedObject.basedHomMap X p).right) h
  simpa only [componentOf, mapπ₀_mk, familyVertex_post] using hh

/-- 概要：源の前合成は射の成分の等式を保存する。
方針：内部 Hom の制限を π₀ へ送る。
規約：合成する射に単射性を要求しない。
使われ方：Goerss–Jardine I §7。構造可換式を部分対象へ制限する。 -/
theorem componentOf_comp_left {W X Y : PointedSimplicialSet.{u}}
    {f g : X ⟶ Y} (h : componentOf f = componentOf g) (i : W ⟶ X) :
    componentOf (i ≫ f) = componentOf (i ≫ g) := by
  have hh := congrArg (mapπ₀ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i Y).right) h
  simpa only [componentOf, mapπ₀_mk, familyVertex_pre] using hh

/-- 概要：suspension の写像空間の射は通常の射の suspension の成分を与える。
方針：閉構造の頂点表示に直して suspension の頂点での式を適用する。
規約：両側の対象の Kan 性は不要。
使われ方：BF 1978 §2、HTT A.3.3。段の構造射の作用を成分へ送る。 -/
theorem componentOf_suspension_map {X Y : PointedSimplicialSet.{u}} (f : X ⟶ Y) :
    mapπ₀ (suspensionHom X Y).right (componentOf f) =
      componentOf (PointedSimplicialSet.circle.{u} ◁ f) := by
  simp only [componentOf, mapπ₀_mk, familyVertex_eq_pointedHomVertex,
    pointedHomVertexEquiv_suspension]

/-- 概要：suspension は点つき射の成分の等式を保存する。
方針：suspension の実際の写像空間の射を π₀ へ送る。
規約：Kan 性を仮定しない。
使われ方：BF 1978 §2、HA §1.4.2。ホモトピー可換なスペクトルの射の厳密化。 -/
theorem componentOf_suspension {X Y : PointedSimplicialSet.{u}}
    {f g : X ⟶ Y} (h : componentOf f = componentOf g) :
    componentOf (PointedSimplicialSet.circle.{u} ◁ f) =
      componentOf (PointedSimplicialSet.circle.{u} ◁ g) := by
  rw [← componentOf_suspension_map, ← componentOf_suspension_map, h]

end

end SerrePositivity.KST.Spectra.PointedMapping
