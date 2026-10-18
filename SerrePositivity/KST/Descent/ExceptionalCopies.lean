module

public import SerrePositivity.KST.Descent.FiniteTypeUniversal
public import SerrePositivity.KST.Descent.OrbitCoproduct
public import SerrePositivity.KST.Descent.OrbitComparisonCube

/-!
# 軌道正方形の例外部分のコピー分解

## 概要
E = W ×_V (V ×_B Z) を、Z のコピーの非交和として有限型の圏内で構成する。

## 方針
引き戻し正方形の合成により E = W ×_B Z の普遍性を示す。
有限非交和が底変換で保たれることを、指定されたコピーの包含に適用する。

## 規約
中心と例外部分のスキーム構造を被約化しない。
分解は単なる点集合の同相ではなく、スキームの圏と有限型の圏内の余極限の普遍性。

## 使われ方
論文 定理 3.1・(3.8) の例外部分の不変部分の比較。
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace SerrePositivity.KST.Descent

variable {S : Scheme.{u}} {B V : FiniteTypeSchemes S} {I : Type u} [Finite I]
variable (p : V ⟶ B) [IsSeparated p.hom.left] [IsSeparated V.obj.hom]
variable (sections : I → (B ⟶ V)) (section_identity : ∀ i, sections i ≫ p = 𝟙 B)

set_option quotPrecheck false in
local notation "Z₀" =>
  reducedClosedAsFiniteType B (coincidenceClosedSet (fun i ↦ (sections i).hom))
set_option quotPrecheck false in
local notation "z₀" =>
  reducedClosedAsFiniteTypeInclusion B (coincidenceClosedSet (fun i ↦ (sections i).hom))
set_option quotPrecheck false in
local notation "c₀" =>
  closedCenterPullbackFirst p (coincidenceClosedSet (fun i ↦ (sections i).hom))
set_option quotPrecheck false in
local notation "c₁" =>
  closedCenterPullbackSecond p (coincidenceClosedSet (fun i ↦ (sections i).hom))
local notation "q₀" => orbitMorphism p sections section_identity

/-- 概要：軌道正方形の実際の例外部分（論文 定理 3.1）。
方針：軌道射と、基底の中心を引き戻した閉埋め込みの引き戻しを取る。
規約：非被約な構造もそのまま保持する。
使われ方：中心のコピーの非交和となる対象。 -/
noncomputable def orbitExceptionalSource : FiniteTypeSchemes S :=
  closedImmersionPullback q₀ c₀

/-- 概要：例外部分から W への射影（論文 定理 3.1）。
方針：実際の例外正方形の第一射影。
規約：有限型の圏内の射。
使われ方：コピーの包含の第一射影。 -/
noncomputable def orbitExceptionalToSource :
    orbitExceptionalSource p sections section_identity ⟶ orbitSource p sections section_identity :=
  (closedImmersionSquare q₀ c₀).f₁₂

/-- 概要：例外部分から基底の閉中心 Z への指定射（論文 (3.8)）。
方針：例外正方形の第二射影と中心の第二射影を合成する。
規約：比較立方体の左上の射と同じ合成。
使われ方：例外部分のコピーの fold。 -/
noncomputable def orbitExceptionalProjection :
    orbitExceptionalSource p sections section_identity ⟶ Z₀ :=
  (closedImmersionSquare q₀ c₀).f₁₃ ≫ c₁

/-- 概要：例外部分は W と Z の B 上の引き戻しでもある（論文 定理 3.1）。
方針：例外正方形と中心の正方形を縦に合成する。
規約：有限型の圏内の普遍性。
使われ方：Z のコピーの包含の構成。 -/
theorem orbitExceptional_isPullback :
    IsPullback (orbitExceptionalToSource p sections section_identity)
      (orbitExceptionalProjection p sections section_identity)
      (orbitFold p sections section_identity) z₀ :=
  (closedImmersionSquare_isPullback q₀ c₀).paste_vert
    (closedImmersionSquare_isPullback p z₀)

/-- 概要：例外部分の合成引き戻しはスキームの圏でも Cartesian（論文 §3）。
方針：二つの実際のスキームの引き戻し正方形を合成する。
規約：有限型の圏内だけの普遍性に限定しない。
使われ方：スキームの有限非交和の底変換。 -/
theorem orbitExceptional_isPullback_scheme :
    IsPullback (orbitExceptionalToSource p sections section_identity).hom.left
      (orbitExceptionalProjection p sections section_identity).hom.left
      (orbitFold p sections section_identity).hom.left (z₀).hom.left :=
  (closedImmersionSquare_cartesian q₀ c₀).paste_vert
    (closedCenterSquare_cartesian p (coincidenceClosedSet (fun i ↦ (sections i).hom)))

/-- 概要：例外部分への各 Z のコピーの指定包含（論文 (3.8)）。
方針：Z → B → W と Z の恒等射を合成引き戻しへ持ち上げる。
規約：中心と例外部分の構造を保つ実際のスキームの射。
使われ方：例外部分の前層のコピー比較。 -/
noncomputable def orbitExceptionalComponent (i : I) :
    Z₀ ⟶ orbitExceptionalSource p sections section_identity :=
  (orbitExceptional_isPullback p sections section_identity).lift
    (z₀ ≫ orbitComponent p sections section_identity i) (𝟙 Z₀) (by
      simp only [Category.assoc, orbitComponent_fold, Category.comp_id, Category.id_comp])

/-- 概要：例外部分のコピーの W への射影（論文 (3.8)）。
方針：合成引き戻しの持ち上げの第一射影。
規約：指定された B のコピーに入る。
使われ方：非交和の底変換の普遍性。 -/
@[reassoc (attr := simp)] theorem orbitExceptionalComponent_source (i : I) :
    orbitExceptionalComponent p sections section_identity i ≫
        orbitExceptionalToSource p sections section_identity =
      z₀ ≫ orbitComponent p sections section_identity i :=
  IsPullback.lift_fst _ _ _ _

/-- 概要：各 Z のコピー上の例外部分の fold は恒等射（論文 (3.8)）。
方針：合成引き戻しの持ち上げの第二射影。
規約：全てのコピーで同じ指定射。
使われ方：前層の比較と対角写像の一致。 -/
@[reassoc (attr := simp)] theorem orbitExceptionalComponent_projection (i : I) :
    orbitExceptionalComponent p sections section_identity i ≫
        orbitExceptionalProjection p sections section_identity = 𝟙 Z₀ :=
  IsPullback.lift_snd _ _ _ _

/-- 概要：例外部分と指定包含は Z のコピーの非交和（論文 定理 3.1・(3.8)）。
方針：スキームの有限非交和の底変換で普遍性を得て、有限型の圏へ反映する。
規約：コピーの分解とその指定包含を同時に証明する。
使われ方：前層の積保存から例外部分の固定比較を導く。 -/
noncomputable def orbitExceptionalIsCoproduct :
    IsColimit (Cofan.mk (orbitExceptionalSource p sections section_identity)
      (orbitExceptionalComponent p sections section_identity)) := by
  apply finiteTypeCofanIsColimitOfSchemeIsColimit
  have original : IsColimit (Cofan.mk (orbitSource p sections section_identity).obj.left
      (fun i ↦ (orbitComponent p sections section_identity i).hom.left)) :=
    coproductIsCoproduct (fun _ : I ↦ B.obj.left)
  have universal := FinitaryPreExtensive.isUniversal_finiteCoproducts original
  apply Nonempty.some
  refine universal.nonempty_isColimit_of_isPullback_left
    (fun _ : I ↦ 𝟙 B.obj.left) (orbitFold p sections section_identity).hom.left (z₀).hom.left
    (fun _ : I ↦ 𝟙 (Z₀).obj.left) (fun _ : I ↦ (z₀).hom.left)
    (fun _ ↦ IsPullback.id_horiz (z₀).hom.left)
    (orbitExceptional_isPullback_scheme p sections section_identity).flip _ (Iso.refl _) ?_ ?_ ?_
  · intro i
    exact congrArg (fun k ↦ k.hom.left) (orbitComponent_fold p sections section_identity i)
  · intro i
    exact (congrArg
      (fun k ↦ (orbitExceptionalComponent p sections section_identity i).hom.left ≫ k)
      (Category.id_comp (orbitExceptionalProjection p sections section_identity).hom.left)).trans
        (congrArg (fun k ↦ k.hom.left)
          (orbitExceptionalComponent_projection p sections section_identity i))
  · intro i
    exact (congrArg
      (fun k ↦ (orbitExceptionalComponent p sections section_identity i).hom.left ≫ k)
      (Category.id_comp (orbitExceptionalToSource p sections section_identity).hom.left)).trans
        (congrArg (fun k ↦ k.hom.left)
          (orbitExceptionalComponent_source p sections section_identity i))

end SerrePositivity.KST.Descent
