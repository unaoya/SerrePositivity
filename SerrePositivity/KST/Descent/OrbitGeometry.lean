module

public import SerrePositivity.KST.Descent.SectionCoincidence
public import SerrePositivity.KST.Descent.CoincidenceCenter
public import SerrePositivity.KST.Descent.ClosedCenterSquare
public import SerrePositivity.KST.Descent.ClosedImmersionSquare

/-!
# 定理 3.1 の軌道正方形の幾何

## 概要
被約な有限型対象 V と、その分離射 V → B の有限個の切断から、
一致場所を中心とする実際の抽象 blowup 正方形を構成する。

## 方針
軌道射 W = ⊔_I B → V を有限型の圏内に構成し、既存の有限性を適用する。
B の一致場所の被約閉中心を V へ引き戻し、軌道射の補集合上の同型を証明する。

## 規約
中心は V 上でさらに被約化せず、B の中心の実際の引き戻しを保持する。
切断の像の被覆は明示的な幾何仮定であり、主定理の降下の結論は仮定しない。

## 使われ方
論文 定理 3.1 の W → V = (X ×_S B)_red と、中心 V ×_B Z の正方形。
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace SerrePositivity.KST.Descent

variable {S : Scheme.{u}} {B V : FiniteTypeSchemes S} {I : Type u} [Finite I]

/-- 概要：有限型の圏内に構成した軌道射の始域 W（論文 定理 3.1）。
方針：切断の有限非交和からの射の有限性を使い、構造射との合成を有限型にする。
規約：始域のスキームは標準の非交和そのもの。
使われ方：前層 L が評価する軌道正方形の右上の対象。 -/
noncomputable def orbitSource (p : V ⟶ B) [IsSeparated p.hom.left]
    (sections : I → (B ⟶ V)) (section_identity : ∀ i, sections i ≫ p = 𝟙 B) :
    FiniteTypeSchemes S := by
  have : IsFinite (sectionOrbitMap (fun i ↦ (sections i).hom.left)) :=
    sectionOrbitMap_isFinite p.hom.left (fun i ↦ (sections i).hom.left)
      (fun i ↦ congrArg (fun k ↦ k.hom.left) (section_identity i))
  have : LocallyOfFiniteType V.obj.hom := V.property.1
  have : QuasiCompact V.obj.hom := V.property.2
  exact ⟨Over.mk (sectionOrbitMap (fun i ↦ (sections i).hom.left) ≫ V.obj.hom),
    locallyOfFiniteType_comp _ _, quasiCompact_comp _ _⟩

/-- 概要：軌道射 W → V を有限型の圏内の射にする（論文 定理 3.1）。
方針：非交和の指定射を基底上の射として包む。
規約：前層 L の定義域の射。
使われ方：抽象 blowup 正方形の固有な辺。 -/
noncomputable def orbitMorphism (p : V ⟶ B) [IsSeparated p.hom.left]
    (sections : I → (B ⟶ V)) (section_identity : ∀ i, sections i ≫ p = 𝟙 B) :
    orbitSource p sections section_identity ⟶ V :=
  ObjectProperty.homMk (Over.homMk (sectionOrbitMap (fun i ↦ (sections i).hom.left)))

/-- 概要：有限型の圏内の軌道射は有限（論文 定理 3.1）。
方針：スキームの射として証明済みの有限切断の補題を使う。
規約：被約性や像の被覆は有限性には不要。
使われ方：抽象 blowup 正方形の固有性。 -/
instance orbitMorphism_isFinite (p : V ⟶ B) [IsSeparated p.hom.left]
    (sections : I → (B ⟶ V)) (section_identity : ∀ i, sections i ≫ p = 𝟙 B) :
    IsFinite (orbitMorphism p sections section_identity).hom.left :=
  sectionOrbitMap_isFinite p.hom.left (fun i ↦ (sections i).hom.left)
    (fun i ↦ congrArg (fun k ↦ k.hom.left) (section_identity i))

/-- 概要：B の一致中心の補集合を V へ引き戻した開集合（論文 定理 3.1）。
方針：有限個の等化子の像の和の閉性を使う。
規約：中心は B 上で取る。
使われ方：軌道射の制限の同型となる開集合。 -/
noncomputable def orbitComplement (p : V ⟶ B) [IsSeparated V.obj.hom]
    (sections : I → (B ⟶ V)) : V.obj.left.Opens :=
  p.hom.left ⁻¹ᵁ closedCenterComplement (coincidenceClosedSet (fun i ↦ (sections i).hom))

/-- 概要：B の一致中心の V への引き戻しの像の補集合（論文 定理 3.1）。
方針：実際の引き戻しの第一射影の像の公式を用いる。
規約：引き戻した中心の非被約な構造を変更しない。
使われ方：抽象 blowup の中心と補開集合の整合性。 -/
theorem orbitComplement_eq (p : V ⟶ B) [IsSeparated V.obj.hom]
    (sections : I → (B ⟶ V)) :
    (orbitComplement p sections : Set V.obj.left) =
      (Set.range (closedCenterPullbackFirst p
        (coincidenceClosedSet (fun i ↦ (sections i).hom))).hom.left)ᶜ := by
  change p.hom.left ⁻¹' (coincidenceLocus (fun i ↦ (sections i).hom))ᶜ =
    (Set.range (pullback.fst p.hom.left
      (reducedClosedInclusion (coincidenceClosedSet (fun i ↦ (sections i).hom)))))ᶜ
  rw [Scheme.Pullback.range_fst, range_reducedClosedInclusion]
  rfl

/-- 概要：軌道射と B の一致中心から実際の抽象 blowup 正方形（論文 定理 3.1）。
方針：有限性から固有性、切断の一致場所の外での同型から補集合条件を証明する。
規約：中心は V ×_B Z。像の被覆を除く降下の結論は入力しない。
使われ方：前層 L の公理 (2) を軌道正方形に適用する幾何データ。 -/
noncomputable def orbitAbstractBlowup [IsReduced V.obj.left]
    (p : V ⟶ B) [IsSeparated p.hom.left] [IsSeparated V.obj.hom]
    (sections : I → (B ⟶ V)) (section_identity : ∀ i, sections i ≫ p = 𝟙 B)
    (covering : ⋃ i, Set.range (sections i).hom.left = Set.univ) : AbstractBlowupSquare S := by
  have : IsClosedImmersion (closedCenterPullbackFirst p
      (coincidenceClosedSet (fun i ↦ (sections i).hom))).hom.left := by
    change IsClosedImmersion (pullback.fst p.hom.left _)
    infer_instance
  apply abstractBlowupOfClosedImmersion (orbitMorphism p sections section_identity)
    (closedCenterPullbackFirst p (coincidenceClosedSet (fun i ↦ (sections i).hom)))
    (orbitComplement p sections) (orbitComplement_eq p sections)
  exact sectionOrbitMap_restrict_isIso p.hom (fun i ↦ (sections i).hom)
    (fun i ↦ congrArg (fun k ↦ k.hom) (section_identity i)) covering
    (orbitComplement p sections) (fun y ↦ y.property)

end SerrePositivity.KST.Descent
