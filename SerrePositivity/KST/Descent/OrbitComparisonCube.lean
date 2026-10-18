module

public import SerrePositivity.KST.Descent.EquivariantOrbitGeometry
public import SerrePositivity.KST.Descent.EquivariantSquareComparison

/-!
# 軌道正方形から基底の恒等中心正方形への比較

## 概要
実際の軌道正方形と基底の一致中心の恒等正方形を、同変な立方体で比較する。
自然な blowup 列が供給されれば、不変部分の全次数の比較を得る。

## 方針
中心 V ×_B Z の第二射影と V → B を使い、上の二頂点の射は合成で構成する。
中心の第二射影の不変性は、引き戻し上の作用から証明する。

## 規約
原典の中心と四つの指定射を保持する。
中項・例外部分の不変部分の同型性の証明は、(3.8) と帰納仮定から別途供給する。

## 使われ方
論文 定理 3.1 の (3.7) を、自然な全次数の長完全列の比較として実現する。
-/

@[expose] public section

universe u w t

open CategoryTheory AlgebraicGeometry

namespace SerrePositivity.KST.Descent

variable {S : Scheme.{u}} {B V : FiniteTypeSchemes S} {I : Type u} [Finite I]

/-- 概要：基底 B とその一致中心 Z の恒等変形の abstract blowup（定理 3.1）。
方針：一致中心の包含と、その台の補開集合を用いる。
規約：比較先は元の軌道正方形の中心を取る基底 B。
使われ方：全次数の比較元の分裂列。 -/
noncomputable def orbitBaseBlowup [IsSeparated V.obj.hom] (sections : I → (B ⟶ V)) :
    AbstractBlowupSquare S :=
  identityCenterBlowup
    (reducedClosedAsFiniteTypeInclusion B (coincidenceClosedSet (fun i ↦ (sections i).hom)))
    (closedCenterComplement (coincidenceClosedSet (fun i ↦ (sections i).hom))) (by
      change _ = (Set.range (reducedClosedInclusion _))ᶜ
      rw [range_reducedClosedInclusion]
      rfl)

/-- 概要：実際の軌道正方形から基底の恒等中心正方形への立方体（定理 3.1）。
方針：基底への射と中心の第二射影の可換式から四頂点の射を構成する。
規約：境界や前層の比較とは独立な幾何的な射。
使われ方：自然な blowup 列の引き戻し比較。 -/
noncomputable def orbitComparisonCube [IsReduced V.obj.left]
    (p : V ⟶ B) [IsSeparated p.hom.left] [IsSeparated V.obj.hom]
    (sections : I → (B ⟶ V)) (section_identity : ∀ i, sections i ≫ p = 𝟙 B)
    (covering : ⋃ i, Set.range (sections i).hom.left = Set.univ) :
    (orbitAbstractBlowup p sections section_identity covering).square ⟶
      (orbitBaseBlowup sections).square :=
  toIdentityCenterSquare _
    (reducedClosedAsFiniteTypeInclusion B (coincidenceClosedSet (fun i ↦ (sections i).hom)))
    p (closedCenterPullbackSecond p (coincidenceClosedSet (fun i ↦ (sections i).hom)))
    (closedCenterSquare p (coincidenceClosedSet (fun i ↦ (sections i).hom))).fac

/-- 概要：中心 V ×_B Z の第二射影は作用で不変（論文 定理 3.1）。
方針：B と Z の自明作用から誘導した引き戻し作用の第二射影を使う。
規約：中心を被約化していない。
使われ方：比較立方体の閉中心の射の同変性。 -/
theorem orbitCenterProjection_invariant {G : Type*} [Group G]
    (p : V ⟶ B) [IsSeparated V.obj.hom] (sections : I → (B ⟶ V))
    (action : G →* Aut V) (over_base : ∀ g, (action g).asIso.hom ≫ p = p) (g : G) :
    (orbitCenterAction p sections action over_base g).asIso.hom ≫
        closedCenterPullbackSecond p (coincidenceClosedSet (fun i ↦ (sections i).hom)) =
      closedCenterPullbackSecond p (coincidenceClosedSet (fun i ↦ (sections i).hom)) :=
  (closedPullbackAction_snd p
    (reducedClosedAsFiniteTypeInclusion B (coincidenceClosedSet (fun i ↦ (sections i).hom)))
    action 1 1 (by intro g; simpa using over_base g) (by intro g; simp) g).trans
      (Category.comp_id _)

/-- 概要：軌道の比較立方体は G 同変（論文 定理 3.1）。
方針：基底への射の不変性と、中心の第二射影の不変性を使う。
規約：基底の恒等中心正方形の四頂点には自明に作用する。
使われ方：幾何的な比較を有理不変部分の全次数の列へ移す。 -/
theorem orbitComparisonCube_equivariant [IsReduced V.obj.left] {G : Type*} [Group G]
    [MulAction G I] (p : V ⟶ B) [IsSeparated p.hom.left] [IsSeparated V.obj.hom]
    (sections : I → (B ⟶ V)) (section_identity : ∀ i, sections i ≫ p = 𝟙 B)
    (covering : ⋃ i, Set.range (sections i).hom.left = Set.univ)
    (action : G →* Aut V) (over_base : ∀ g, (action g).asIso.hom ≫ p = p)
    (equivariant : ∀ g i, sections (g • i) = sections i ≫ (action g).asIso.hom) :
    EquivariantSquareMap (orbitAbstractBlowupAction p sections section_identity covering
      action over_base equivariant) (SquareAction.trivial (orbitBaseBlowup sections).square G)
      (orbitComparisonCube p sections section_identity covering) :=
  toIdentityCenterSquare_equivariant
    (orbitAbstractBlowupAction p sections section_identity covering action over_base equivariant)
    (reducedClosedAsFiniteTypeInclusion B (coincidenceClosedSet (fun i ↦ (sections i).hom)))
    p (closedCenterPullbackSecond p (coincidenceClosedSet (fun i ↦ (sections i).hom)))
    (closedCenterSquare p (coincidenceClosedSet (fun i ↦ (sections i).hom))).fac over_base
    (orbitCenterProjection_invariant p sections action over_base)

namespace NaturalBlowupSequences

/-- 概要：実際の軌道正方形と基底の恒等中心正方形の固定部分の列の比較（定理 3.1）。
方針：構成した同変立方体に自然な blowup 列を適用する。
規約：列の存在と自然性は実降下から供給する明示的な接続データ。
使われ方：(3.8) と中心上の帰納を五項補題へ接続する。 -/
noncomputable def orbitFixedComparison {Coefficient : Type w}
    {L : GradedPresheaf.{u + 1, u, w, t} (FiniteTypeSchemes S) Coefficient}
    (data : NaturalBlowupSequences L) [IsReduced V.obj.left]
    {G : Type*} [Group G] [Finite G] [MulAction G I]
    (p : V ⟶ B) [IsSeparated p.hom.left] [IsSeparated V.obj.hom]
    (sections : I → (B ⟶ V)) (section_identity : ∀ i, sections i ≫ p = 𝟙 B)
    (covering : ⋃ i, Set.range (sections i).hom.left = Set.univ)
    (action : G →* Aut V) (over_base : ∀ g, (action g).asIso.hom ≫ p = p)
    (equivariant : ∀ g i, sections (g • i) = sections i ≫ (action g).asIso.hom)
    (H : Coefficient) :=
  data.fixedComparison (orbitAbstractBlowup p sections section_identity covering)
    (orbitBaseBlowup sections)
    (orbitAbstractBlowupAction p sections section_identity covering action over_base equivariant)
    (SquareAction.trivial (orbitBaseBlowup sections).square G)
    (orbitComparisonCube p sections section_identity covering)
    (orbitComparisonCube_equivariant p sections section_identity covering
      action over_base equivariant) H

end NaturalBlowupSequences

end SerrePositivity.KST.Descent
