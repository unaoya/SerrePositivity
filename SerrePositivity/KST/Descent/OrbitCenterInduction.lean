module

public import SerrePositivity.KST.Descent.ClosedCenterTransitivity
public import SerrePositivity.KST.Descent.OrbitComparisonCube

/-!
# 軌道正方形の実際の中心への帰納入力

## 概要
構成済みの軌道中心に、切断と点の推移性を移し、その始域の被約化後にも被覆を得る。

## 方針
任意の閉埋め込みへの引き戻しの補題を、実際の一致中心の包含に適用する。

## 規約
中心とその作用は既存の orbitCenterAction のまま保持する。帰納の結論を仮定に追加しない。

## 使われ方
論文 定理 3.1 の真閉中心に対する次元帰納の幾何的入力。
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace SerrePositivity.KST.Descent

variable {S : Scheme.{u}} {B V : FiniteTypeSchemes S} {I : Type u} [Finite I]
variable (p : V ⟶ B) [IsSeparated V.obj.hom] (sections : I → (B ⟶ V))
variable {G : Type u} [Group G] (action : G →* Aut V)
variable (over_base : ∀ g, (action g).asIso.hom ≫ p = p)

/-- 概要：実際の軌道中心の射でも点のファイバーが推移的（論文 定理 3.1）。
方針：中心の包含への閉底変換の推移性を適用する。
規約：中心上の既存の群作用と指定射をそのまま用いる。
使われ方：中心上の切断の移動が全体を覆うための条件。 -/
theorem orbitCenterAction_transitive_on_fibers
    (transitive : ∀ x y : V.obj.left, p.hom.left x = p.hom.left y →
      ∃ g : G, (action g).asIso.hom.hom.left x = y)
    (x y : (closedCenterPullback p (coincidenceClosedSet (fun i ↦ (sections i).hom))).obj.left)
    (same_base : (closedCenterPullbackSecond p (coincidenceClosedSet
      (fun i ↦ (sections i).hom))).hom.left x =
        (closedCenterPullbackSecond p (coincidenceClosedSet
          (fun i ↦ (sections i).hom))).hom.left y) :
    ∃ g : G, (orbitCenterAction p sections action over_base g).asIso.hom.hom.left x = y :=
  closedBaseChangeAction_transitive_on_fibers p
    (reducedClosedAsFiniteTypeInclusion B (coincidenceClosedSet (fun i ↦ (sections i).hom)))
    action over_base transitive x y same_base

/-- 概要：元の切断を実際の軌道中心の切断へ移す（論文 定理 3.1）。
方針：一致中心の包含と切断の合成を実際の引き戻しへ持ち上げる。
規約：始域は被約な一致中心、終域は非被約なままの引き戻し。
使われ方：中心上の帰納で切断の存在を維持する。 -/
noncomputable def orbitCenterSection (s : B ⟶ V) (hs : s ≫ p = 𝟙 B) :
    reducedClosedAsFiniteType B (coincidenceClosedSet (fun i ↦ (sections i).hom)) ⟶
      closedCenterPullback p (coincidenceClosedSet (fun i ↦ (sections i).hom)) :=
  closedBaseChangeSection p
    (reducedClosedAsFiniteTypeInclusion B (coincidenceClosedSet (fun i ↦ (sections i).hom))) s hs

/-- 概要：構成した軌道中心上の射は指定された射影の切断（論文 定理 3.1）。
方針：閉中心への引き戻しの切断の合成公式を適用する。
規約：有限型の圏内での実際の射の等式。
使われ方：被約化した中心への切断の持ち上げ。 -/
@[reassoc (attr := simp)] theorem orbitCenterSection_identity (s : B ⟶ V)
    (hs : s ≫ p = 𝟙 B) : orbitCenterSection p sections s hs ≫
      closedCenterPullbackSecond p (coincidenceClosedSet (fun i ↦ (sections i).hom)) =
        𝟙 (reducedClosedAsFiniteType B (coincidenceClosedSet (fun i ↦ (sections i).hom))) :=
  closedBaseChangeSection_identity p
    (reducedClosedAsFiniteTypeInclusion B (coincidenceClosedSet (fun i ↦ (sections i).hom))) s hs

/-- 概要：被約化した実際の中心の始域は元の切断の移動で覆われる（論文 定理 3.1）。
方針：被約な一致中心からの切断を始域の被約化へ持ち上げ、閉底変換の被覆を適用する。
規約：中心・作用・切断をアフィンの別のモデルに変更しない。
使われ方：次元の低い被約な基底で、構成済みの軌道段階を繰り返すための入力。 -/
theorem orbitCenter_reducedSection_covering
    (transitive : ∀ x y : V.obj.left, p.hom.left x = p.hom.left y →
      ∃ g : G, (action g).asIso.hom.hom.left x = y)
    (s : B ⟶ V) (hs : s ≫ p = 𝟙 B) :
    ⋃ t : TranslatedSectionIndex
        (finiteTypeReductionAction (orbitCenterAction p sections action over_base))
      (finiteTypeReductionLift (orbitCenterSection p sections s hs)),
      Set.range t.val.hom.left = Set.univ :=
  closedBaseChange_reducedSection_covering p
    (reducedClosedAsFiniteTypeInclusion B (coincidenceClosedSet (fun i ↦ (sections i).hom)))
    action over_base transitive s hs

end SerrePositivity.KST.Descent
