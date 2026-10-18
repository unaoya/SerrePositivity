module

public import SerrePositivity.KST.Spectra.SkeletalMappingTower
public import SerrePositivity.KST.Spectra.ConstantPointedHomotopyEnd

/-!
概要：定数写像を基点とする骨格の写像空間の点つき Kan 塔。
方針：通常の内部 Hom の制限が定数基点を保つことを示して点つき圏へ戻す。
規約：源に指定基点は要求しない。係数の基点への定数写像を選ぶ。
使われ方：Goerss–Jardine VIII §§1–2。自明作用の hG の π_* の塔。
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalClosed
open CartesianMonoidalCategory SSet Opposite HomotopicalAlgebra
open SSet.modelCategoryQuillen

namespace SerrePositivity.KST.Spectra.UnbasedPointedMapping

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：源の射での前合成は定数基点を保つ。
方針：curry の前合成と第二射影の自然性を使う。
規約：K→L は obj L X→obj K X を誘導する。
使われ方：Goerss–Jardine VIII §1。点つき骨格の塔の遷移。 -/
def pre {K L : SSet.{u}} (f : K ⟶ L) (X : PointedSimplicialSet.{u}) :
    obj L X ⟶ obj K X :=
  Under.homMk ((MonoidalClosed.pre f).app X.right) (by
    change curry (snd L (𝟙_ SSet.{u}) ≫ X.hom) ≫ (MonoidalClosed.pre f).app X.right =
      curry (snd K (𝟙_ SSet.{u}) ≫ X.hom)
    rw [curry_pre_app, ← Category.assoc, whiskerRight_snd])

/-- 概要：定数基点の写像空間を源に関する反変関手にする。
方針：内部 Hom の前合成の恒等と合成法則を点つき射へ移す。
規約：係数 X は固定。
使われ方：Goerss–Jardine VIII §1。骨格の余錐からの点つき錐。 -/
def contravariantFunctor (X : PointedSimplicialSet.{u}) :
    SSet.{u}ᵒᵖ ⥤ PointedSimplicialSet.{u} where
  obj K := obj K.unop X
  map f := pre f.unop X
  map_id K := by
    apply Under.UnderMorphism.ext
    change (MonoidalClosed.pre (𝟙 K.unop)).app X.right = 𝟙 _
    rw [MonoidalClosed.pre_id, NatTrans.id_app]
  map_comp f g := by
    apply Under.UnderMorphism.ext
    change (MonoidalClosed.pre (g.unop ≫ f.unop)).app X.right =
      (MonoidalClosed.pre f.unop).app X.right ≫ (MonoidalClosed.pre g.unop).app X.right
    rw [MonoidalClosed.pre_map, NatTrans.comp_app]

/-- 概要：点つき係数への骨格からの写像空間の塔。
方針：骨格の増加図式を定数基点の反変関手へ送る。
規約：塔の段 n は通常の n 骨格からの写像。
使われ方：Goerss–Jardine VIII §1。自明作用の hG の段ごとの解析。 -/
def tower (K : SSet.{u}) (X : PointedSimplicialSet.{u}) : ℕᵒᵖ ⥤ PointedSimplicialSet.{u} :=
  (SkeletalMapping.source K).op ⋙ contravariantFunctor X

instance tower_level_kanComplex (K : SSet.{u}) (X : PointedSimplicialSet.{u})
    [KanComplex X.right] (n : ℕᵒᵖ) : KanComplex ((tower K X).obj n).right :=
  SkeletalMapping.level_kanComplex K X.right n

/-- 概要：点つき骨格写像空間の塔の基礎の遷移は Kan fibration。
方針：基点を忘れると構成済みの通常の写像空間の遷移になることを使う。
規約：源 K の Kan 性は不要。
使われ方：Goerss–Jardine VIII §1。塔の fiber のホモトピー長完全列。 -/
theorem tower_map_fibration (K : SSet.{u}) (X : PointedSimplicialSet.{u})
    [KanComplex X.right] {n m : ℕᵒᵖ} (f : n ⟶ m) :
    Fibration ((tower K X).map f).right :=
  SkeletalMapping.map_fibration K X.right f

/-- 概要：全体の点つき写像空間から骨格の塔への標準錐。
方針：骨格の包含を定数基点の前合成へ移す。
規約：頂点は obj K X。
使われ方：Goerss–Jardine VIII §1。全体から有限段への制限。 -/
def cone (K : SSet.{u}) (X : PointedSimplicialSet.{u}) : Cone (tower K X) :=
  (contravariantFunctor X).mapCone (SkeletalWeightedEnd.skeletonCocone K).op

/-- 概要：点つき写像空間はその骨格の塔の通常の極限。
方針：基点の忘却が極限を反映することと基礎の写像空間の復元を使う。
規約：Kan 性なしでも成立する厳密な極限。
使われ方：Goerss–Jardine VIII §1。π_* の塔の計算を全体へ戻す界面。 -/
def coneIsLimit (K : SSet.{u}) (X : PointedSimplicialSet.{u}) : IsLimit (cone K X) :=
  isLimitOfReflects PointedSimplicialSet.forget (SkeletalMapping.coneIsLimit K X.right)

end

end SerrePositivity.KST.Spectra.UnbasedPointedMapping
