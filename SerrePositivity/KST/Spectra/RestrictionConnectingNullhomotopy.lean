module

public import SerrePositivity.KST.Spectra.RestrictionBoundaryFamilies

/-!
概要：基本群から成分への連結射の代表が持つ元の源上の nullhomotopy。
方針：零次の相対商の代表を実際の点つき射へ戻し、一次の充填族の両端点を評価する。
規約：充填の向きは出力射から基点への向きであり、逆向きへ無言で変更しない。
使われ方：Goerss–Jardine I §8、VIII §1。連結射と loop の交換の符号を計算する基本段。
-/

@[expose] public section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial

namespace SerrePositivity.KST.Spectra.UnbasedPointedMapping

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {A B : SSet.{u}} (i : A ⟶ B) (Y : PointedSimplicialSet.{u})
  {s : (obj A Y).right.PtSimplex 1 ((pre i Y).right.app _ (obj B Y).basepoint)}
  (L : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BoundaryLift (pre i Y).right (obj B Y).basepoint s)

/-- 概要：零次の相対商の代表を実際の点つき射へ戻す。
方針：代表単体を頂点に送り、pointed Hom の頂点と射の標準同値を使う。
規約：Kan 性は不要。射の代表は選び直さない。
使われ方：Goerss–Jardine VIII §1。連結射の成分の幾何的代表。 -/
def cofiberBoundaryMap : relativeSource i ⟶ Y :=
  PointedMapping.familyMap (relativeSource i) Y
    (SSet.yonedaEquiv (cofiberBoundarySimplex i Y L).map)

/-- 概要：相対商の零次代表を元の源へ戻すと充填族の始点。
方針：零次パラメータの切断の自然性と充填の最後の面の式を使う。
規約：始点は面添字一。終点ではない。
使われ方：Goerss–Jardine I §8。連結射の向きの基本段。 -/
@[reassoc]
lemma relativeProjection_cofiberBoundaryMap :
    relativeProjection i ≫ (cofiberBoundaryMap i Y L).right =
      SSet.ι₀ ≫ boundaryLiftFamily i Y L := by
  change relativeProjection i ≫
    (PointedMapping.zeroSection (relativeSource i).right ≫
      uncurry (SSet.yonedaEquiv.symm (SSet.yonedaEquiv (cofiberBoundarySimplex i Y L).map) ≫
        PointedObject.basedHomι (relativeSource i) Y)) = _
  rw [Equiv.symm_apply_apply, ← Category.assoc, PointedMapping.zeroSection_natural,
    Category.assoc]
  change PointedMapping.zeroSection B ≫
    (relativeProjection i ▷ (Δ[0] : SSet.{u}) ≫ boundaryLiftOutputFamily i Y L) = _
  rw [boundaryLiftOutputFamily_last]
  rfl

/-- 概要：元の源上の連結射の代表から定数射への実際の区間ホモトピー。
方針：一次の相対ホーン充填を使い、最後の面と既知の面を両端点へ移す。
規約：出力から零への向き。指定部分への制限は底のループの族となる。
使われ方：Goerss–Jardine VIII §1。loop と連結射の符号の比較。 -/
def boundaryLiftNullhomotopy :
    SSet.Homotopy (relativeProjection i ≫ (cofiberBoundaryMap i Y L).right)
      (SSet.const Y.basepoint) where
  h := boundaryLiftFamily i Y L
  h₀ := (relativeProjection_cofiberBoundaryMap i Y L).symm
  h₁ := by
    have hι : SSet.ι₁ (X := B) = PointedMapping.zeroSection B ≫
      B ◁ stdSimplex.δ (0 : Fin 2) := rfl
    rw [hι, Category.assoc, boundaryLiftFamily_face i Y L 0 (by decide), comp_toUnit_assoc]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedConstant_eq_const Y B
  rel := by
    ext m ⟨⟨z, hz⟩, t⟩
    exact hz.elim

/-- 概要：この nullhomotopy は指定部分の上で元の底のループの族と一致する。
方針：相対ホーン充填の源の制限式を適用する。
規約：底のループの向きは元のまま。
使われ方：Goerss–Jardine I §8、VIII §1。指定部分上の向きの検査。 -/
@[reassoc]
lemma boundaryLiftNullhomotopy_source :
    i ▷ (Δ[1] : SSet.{u}) ≫ (boundaryLiftNullhomotopy i Y L).h = uncurry s.map :=
  boundaryLiftFamily_source i Y L

end
end SerrePositivity.KST.Spectra.UnbasedPointedMapping
