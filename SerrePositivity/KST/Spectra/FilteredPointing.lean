module

public import SerrePositivity.KST.Spectra.FilteredHomotopyComparison
public import Mathlib.CategoryTheory.Filtered.Final

/-!
概要：filtered diagram の一段の頂点から後続段全体に基点を付ける。
方針：under 圏で頂点を遷移射により運び、forget の final 性で余極限を保つ。
規約：基点は元の diagram の指定基点に制限しない。
使われ方：Goerss–Jardine I §7、BF 1978 §2、HA §1.4.2。全基点 π_* 同型の余極限保存。
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {J : Type u} [SmallCategory J]

/-- 概要：一段の頂点を後続段へ運んだ点つき図式。
方針：under 圏の対象 j→k に、F(k) と頂点の像を対応させる。
規約：後続段の遷移は元の F の射。
使われ方：Goerss–Jardine I §7、HA §1.4.2。任意の基点での filtered π_* 比較。 -/
def pointFromStage (F : J ⥤ SSet.{u}) (j : J) (x : (F.obj j) _⦋0⦌) :
    Under j ⥤ PointedSimplicialSet.{u} where
  obj a := PointedSimplicialSet.ofVertex (F.obj a.right) ((F.map a.hom).app _ x)
  map {a b} f := Under.homMk (F.map f.right) (by
    change SSet.const ((F.map a.hom).app _ x) ≫ F.map f.right =
      SSet.const ((F.map b.hom).app _ x)
    rw [SSet.const_comp]
    congr 1
    change (F.map a.hom ≫ F.map f.right).app _ x = (F.map b.hom).app _ x
    rw [← F.map_comp, Under.w f])
  map_id a := by apply Under.UnderMorphism.ext; exact F.map_id a.right
  map_comp f g := by apply Under.UnderMorphism.ext; exact F.map_comp f.right g.right

/-- 概要：Kan 図式の後続段に基点を付けた図式の各段も Kan。
方針：基礎単体集合が元の段そのものであることを使う。
規約：全ての後続段に対する型クラスを束ねる。
使われ方：Goerss–Jardine I §7。全基点のホモトピー群の比較。 -/
instance pointFromStage_kanComplex (F : J ⥤ SSet.{u}) [∀ k, KanComplex (F.obj k)]
    (j : J) (x : (F.obj j) _⦋0⦌) :
    ∀ a, KanComplex ((pointFromStage F j x).obj a).right :=
  fun a ↦ inferInstanceAs (KanComplex (F.obj a.right))

/-- 概要：基点を後続段へ運んだ図式の cocone。
方針：元の cocone の各脚を使い、始段の頂点の像を cocone の基点にする。
規約：元の c の余極限性をまだ要求しない。
使われ方：Goerss–Jardine I §7、HA §1.4.2。任意基点を持つ余極限の図式。 -/
def pointFromStageCocone (F : J ⥤ SSet.{u}) (j : J) (x : (F.obj j) _⦋0⦌)
    (c : Cocone F) : Cocone (pointFromStage F j x) where
  pt := PointedSimplicialSet.ofVertex c.pt ((c.ι.app j).app _ x)
  ι := {
    app a := Under.homMk (c.ι.app a.right) (by
      change SSet.const ((F.map a.hom).app _ x) ≫ c.ι.app a.right =
        SSet.const ((c.ι.app j).app _ x)
      rw [SSet.const_comp]
      congr 1
      exact congrArg (fun z : F.obj j ⟶ c.pt ↦ z.app _ x) (c.w a.hom))
    naturality a b f := by apply Under.UnderMorphism.ext; exact c.w f.right }

/-- 概要：Kan な cocone の対象に始段の頂点の像で基点を付けても Kan。
方針：基礎単体集合を変えない。
規約：c の余極限性は不要。
使われ方：Goerss–Jardine I §7。指定基点の余極限比較の型クラス。 -/
instance pointFromStageCocone_kanComplex (F : J ⥤ SSet.{u}) (j : J) (x : (F.obj j) _⦋0⦌)
    (c : Cocone F) [KanComplex c.pt] :
    KanComplex (pointFromStageCocone F j x c).pt.right := inferInstanceAs (KanComplex c.pt)

/-- 概要：基点を後続段へ運んだ cocone の基礎単体集合は余極限。
方針：filtered 圏の under 圏からの forget が final であることを使う。
規約：元の cocone c の余極限性を要求する。
使われ方：Goerss–Jardine I §7、HA §1.4.2。任意基点でのホモトピー群の余極限比較。 -/
def pointFromStageIsColimit (F : J ⥤ SSet.{u}) (j : J) (x : (F.obj j) _⦋0⦌)
    [IsFiltered J] {c : Cocone F} (hc : IsColimit c) :
    IsColimit (PointedSimplicialSet.forget.mapCocone (pointFromStageCocone F j x c)) :=
  (Functor.Final.isColimitWhiskerEquiv (Under.forget j) c).symm hc

/-- 概要：自然変換は後続段に付けた基点を保つ自然変換を誘導する。
方針：各段の元の射を使い、自然性で運んだ基点の可換式を得る。
規約：標的の始段の基点は元の自然変換による像。
使われ方：Goerss–Jardine I §7、HA §1.4.2。全基点 π_* 同型を指定基点の比較へ還元する。 -/
def pointFromStageMap (F : J ⥤ SSet.{u}) (j : J) (x : (F.obj j) _⦋0⦌)
    {G : J ⥤ SSet.{u}} (t : F ⟶ G) :
    pointFromStage F j x ⟶ pointFromStage G j ((t.app j).app _ x) where
  app a := Under.homMk (t.app a.right) (by
    change SSet.const ((F.map a.hom).app _ x) ≫ t.app a.right =
      SSet.const ((G.map a.hom).app _ ((t.app j).app _ x))
    rw [SSet.const_comp]
    congr 1
    exact congrArg (fun z : F.obj j ⟶ G.obj a.right ↦ z.app _ x) (t.naturality a.hom))
  naturality a b f := by apply Under.UnderMorphism.ext; exact t.naturality f.right

end

end SerrePositivity.KST.Spectra
