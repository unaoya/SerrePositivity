module

public import SerrePositivity.KST.Descent.OrbitAction
public import SerrePositivity.KST.Descent.SquareAction

/-!
# 実際の軌道正方形の四頂点の同変性

## 概要
構成済みの軌道の抽象 blowup 正方形に、四頂点の作用と四辺の同変性を与える。

## 方針
一致中心 Z ⊂ B に自明に作用し、その V への引き戻しに作用を構成する。
例外部分 W ×_V (V ×_B Z) には、同変な cospan の引き戻し作用を用いる。

## 規約
中心と例外部分の実際のスキーム構造を保持する。
前層の境界の同変性は、後続で降下の長完全列の自然性から得る必要がある。

## 使われ方
論文 定理 3.1 の G 同変な軌道正方形と、不変部分の全次数の完全列。
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace SerrePositivity.KST.Descent

variable {S : Scheme.{u}} {B V : FiniteTypeSchemes S} {I : Type u} [Finite I]
variable {G : Type*} [Group G]

/-- 概要：一致中心の引き戻し V ×_B Z の G 作用（論文 定理 3.1）。
方針：V の作用と B・Z の自明作用を、実際の閉中心の引き戻しへ移す。
規約：V の作用が射 p の上にあることを明示する。
使われ方：軌道正方形の左下の作用。 -/
noncomputable def orbitCenterAction (p : V ⟶ B) [IsSeparated V.obj.hom]
    (sections : I → (B ⟶ V)) (action : G →* Aut V)
    (over_base : ∀ g, (action g).asIso.hom ≫ p = p) :
    G →* Aut (closedCenterPullback p (coincidenceClosedSet (fun i ↦ (sections i).hom))) :=
  closedPullbackAction p
    (reducedClosedAsFiniteTypeInclusion B (coincidenceClosedSet (fun i ↦ (sections i).hom)))
    action 1 1 (by intro g; simpa using over_base g) (by intro g; simp)

/-- 概要：一致中心の引き戻しの包含は G 同変（論文 定理 3.1）。
方針：引き戻しの第一射影の同変性を使う。
規約：包含のスキーム構造を変更しない。
使われ方：軌道正方形の下辺と前層 L の中心への制限。 -/
theorem orbitCenterInclusion_equivariant (p : V ⟶ B) [IsSeparated V.obj.hom]
    (sections : I → (B ⟶ V)) (action : G →* Aut V)
    (over_base : ∀ g, (action g).asIso.hom ≫ p = p) (g : G) :
    (orbitCenterAction p sections action over_base g).asIso.hom ≫
        closedCenterPullbackFirst p (coincidenceClosedSet (fun i ↦ (sections i).hom)) =
      closedCenterPullbackFirst p (coincidenceClosedSet (fun i ↦ (sections i).hom)) ≫
        (action g).asIso.hom :=
  closedPullbackAction_fst p
    (reducedClosedAsFiniteTypeInclusion B (coincidenceClosedSet (fun i ↦ (sections i).hom)))
    action 1 1 (by intro g; simpa using over_base g) (by intro g; simp) g

/-- 概要：軌道の抽象 blowup 正方形の四頂点と四辺の G 同変構造（定理 3.1）。
方針：非交和の作用・中心の引き戻しの作用・例外部分の引き戻し作用を組み合わせる。
規約：境界の同変性や降下の結論をこの幾何データの仮定に入れない。
使われ方：前層 L を実際の軌道正方形へ適用し、不変部分の長完全列へ進む。 -/
noncomputable def orbitAbstractBlowupAction [MulAction G I] [IsReduced V.obj.left]
    (p : V ⟶ B) [IsSeparated p.hom.left] [IsSeparated V.obj.hom]
    (sections : I → (B ⟶ V)) (section_identity : ∀ i, sections i ≫ p = 𝟙 B)
    (covering : ⋃ i, Set.range (sections i).hom.left = Set.univ)
    (action : G →* Aut V) (over_base : ∀ g, (action g).asIso.hom ≫ p = p)
    (equivariant : ∀ g i, sections (g • i) = sections i ≫ (action g).asIso.hom) :
    SquareAction (orbitAbstractBlowup p sections section_identity covering).square G := by
  have : IsClosedImmersion (closedCenterPullbackFirst p
      (coincidenceClosedSet (fun i ↦ (sections i).hom))).hom.left := by
    change IsClosedImmersion (CategoryTheory.Limits.pullback.fst p.hom.left _)
    infer_instance
  exact closedImmersionSquareAction (orbitMorphism p sections section_identity)
    (closedCenterPullbackFirst p (coincidenceClosedSet (fun i ↦ (sections i).hom)))
    (orbitAction p sections section_identity action equivariant)
    (orbitCenterAction p sections action over_base) action
    (orbitMorphism_equivariant p sections section_identity action equivariant)
    (orbitCenterInclusion_equivariant p sections action over_base)

end SerrePositivity.KST.Descent
