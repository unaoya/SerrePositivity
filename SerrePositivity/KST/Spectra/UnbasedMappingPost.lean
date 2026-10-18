module

public import SerrePositivity.KST.Spectra.PointedSkeletalMappingTower

/-!
概要：定数基点を持つ通常の写像空間の係数射への関手性。
方針：内部 Hom の後合成が定数基点を保ち、前合成と可換であることを使う。
規約：源には基点を指定しない。係数射は点つき射。
使われ方：Goerss–Jardine VIII §1。骨格の塔の係数の自然性。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet

namespace SerrePositivity.KST.Spectra.UnbasedPointedMapping

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：通常の写像空間の係数射による後合成は点つき射。
方針：内部 Hom の係数射を使い、curry の自然性で基点保存を確認する。
規約：Kan 性は不要。
使われ方：Goerss–Jardine VIII §1。骨格の塔の段の係数射。 -/
def post (K : SSet.{u}) {Y Z : PointedSimplicialSet.{u}} (p : Y ⟶ Z) :
    obj K Y ⟶ obj K Z :=
  Under.homMk ((ihom K).map p.right) (by
    change curry (snd K (𝟙_ SSet.{u}) ≫ Y.hom) ≫ (ihom K).map p.right =
      curry (snd K (𝟙_ SSet.{u}) ≫ Z.hom)
    rw [← curry_natural_right, Category.assoc, Under.w])

@[reassoc]
lemma pre_post {K L : SSet.{u}} (f : K ⟶ L)
    {Y Z : PointedSimplicialSet.{u}} (p : Y ⟶ Z) :
    pre f Y ≫ post K p = post L p ≫ pre f Z := by
  apply Under.UnderMorphism.ext
  exact pre_comm_ihom_map f p.right

/-- 概要：写像空間の係数を変える共変関手。
方針：通常の内部 Hom の関手法則を点つき射へ移す。
規約：源 K は固定する。
使われ方：Goerss–Jardine VIII §1。係数図式と骨格の塔の比較。 -/
def covariantFunctor (K : SSet.{u}) : PointedSimplicialSet.{u} ⥤ PointedSimplicialSet.{u} where
  obj X := obj K X
  map p := post K p
  map_id X := by
    apply Under.UnderMorphism.ext
    exact (ihom K).map_id X.right
  map_comp p q := by
    apply Under.UnderMorphism.ext
    exact (ihom K).map_comp p.right q.right

/-- 概要：係数射が誘導する骨格の写像空間の塔の射。
方針：各段で係数の後合成を取り、制限との可換式で自然性を示す。
規約：塔の段は通常の n 骨格からの写像空間。
使われ方：Goerss–Jardine VIII §1。実際の塔の微分の係数自然性。 -/
def towerPost (K : SSet.{u}) {Y Z : PointedSimplicialSet.{u}} (p : Y ⟶ Z) :
    tower K Y ⟶ tower K Z where
  app n := post ((SkeletalMapping.source K).obj n.unop) p
  naturality _n _m f := pre_post ((SkeletalMapping.source K).map f.unop) p

end

end SerrePositivity.KST.Spectra.UnbasedPointedMapping
