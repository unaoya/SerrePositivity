module

public import SerrePositivity.KST.Spectra.PointedFreeActionEquivalence
public import SerrePositivity.KST.Spectra.FreeCochainWeight

/-!
概要：任意の点つき Kan 複体の群作用の余単体 cochain 関手。
方針：EG の離散重みから作用図式への点つき end を取り、自由軌道の比較で Kan 性を移す。
規約：スペクトルの一段に限らず点つき単体集合の作用を入力にする。
使われ方：Goerss–Jardine VIII §2、HA §1.4.2。cochain の loop との比較の共通部分。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory SSet Opposite


namespace SerrePositivity.KST.Spectra.PointedActionCochains

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：点つき単体集合の作用の実際の余単体 cochain。
方針：EG の重みと小さい一対象圏上の係数図式を用いる。
規約：係数の Kan 性は対象の定義には不要。
使われ方：Goerss–Jardine VIII §2。作用の余単体模型。 -/
def obj {G : Type u} [Group G] (B : Action PointedSimplicialSet.{u} G) :
    CosimplicialObject PointedSimplicialSet.{u} :=
  weightedCochains (GroupActionCochains.universalCoverWeight G)
    (FreeActionFamily.pointedCoefficients B)

/-- 概要：点つき単体集合の作用の cochain は作用の圏からの関手。
方針：作用図式と重み付き cochain の二つの関手を合成する。
規約：全ての関手法則は厳密。
使われ方：Goerss–Jardine VIII §2。係数の作用の射への自然性。 -/
def functor (G : Type u) [Group G] : Action PointedSimplicialSet.{u} G ⥤
    CosimplicialObject PointedSimplicialSet.{u} :=
  Action.FunctorCategoryEquivalence.functor ⋙
    (Functor.whiskeringLeft (AsSmall.{u} (SingleObj G)) (SingleObj G)
      PointedSimplicialSet.{u}).obj AsSmall.down ⋙
    weightedCochainsFunctor (GroupActionCochains.universalCoverWeight G)

/-- 概要：点つき同変射が誘導する実際の余単体 cochain の射。
方針：cochain 関手の射を取り出す。
規約：射の定義に Kan 性は不要。
使われ方：Goerss–Jardine VIII §2。cochain の係数の比較。 -/
def map {G : Type u} [Group G] {B C : Action PointedSimplicialSet.{u} G} (τ : B ⟶ C) :
    obj B ⟶ obj C := (functor G).map τ

/-- 概要：点つき作用の cochain の次数 n は自由作用の end と同型。
方針：EG_n の自由軌道の同型を end の重みの反変関手で送る。
規約：G は第一因子、残る n 個の座標への作用は自明。
使われ方：Goerss–Jardine VIII §2。cochain の各値の関数空間の表示。 -/
def freeIso {G : Type u} [Group G] (B : Action PointedSimplicialSet.{u} G) (n : ℕ) :
    (obj B).obj (SimplexCategory.mk n) ≅
      PointedWeightedEnd.obj (FreeActionFamily.weight (Fin n → G))
        (FreeActionFamily.pointedCoefficients B) :=
  (PointedWeightedEnd.weightFunctor (FreeActionFamily.pointedCoefficients B)).mapIso
    (GroupActionCochains.universalCoverFreeIso G n).symm.op

/-- 概要：自由軌道への比較は係数の点つき同変射に自然。
方針：end の重みの前合成と係数の後合成の可換性を適用する。
規約：次数 n の実際の射の等式。
使われ方：Goerss–Jardine VIII §2。cochain の各値のホモトピー不変性。 -/
lemma freeIso_natural {G : Type u} [Group G]
    {B C : Action PointedSimplicialSet.{u} G} (τ : B ⟶ C) (n : ℕ) :
    (map τ).app (SimplexCategory.mk n) ≫ (freeIso C n).hom =
      (freeIso B n).hom ≫ PointedWeightedEnd.map (FreeActionFamily.weight (Fin n → G))
        (FreeActionFamily.pointedCoefficientsMap τ) := by
  change PointedWeightedEnd.map
      ((GroupActionCochains.universalCoverWeight G).obj (op (SimplexCategory.mk n)))
      (FreeActionFamily.pointedCoefficientsMap τ) ≫
        PointedWeightedEnd.preMap (GroupActionCochains.universalCoverFreeIso G n).inv
          (FreeActionFamily.pointedCoefficients C) =
    PointedWeightedEnd.preMap (GroupActionCochains.universalCoverFreeIso G n).inv
      (FreeActionFamily.pointedCoefficients B) ≫
        PointedWeightedEnd.map (FreeActionFamily.weight (Fin n → G))
          (FreeActionFamily.pointedCoefficientsMap τ)
  exact PointedWeightedEnd.map_preMap _ _

/-- 概要：Kan 係数の群作用の cochain は各次数で Kan。
方針：自由軌道の点つき end の Kan 性を比較同型で移す。
規約：群の有限性は不要。
使われ方：Goerss–Jardine VIII §2。cochain の loop と Tot の比較の Kan な係数。 -/
instance obj_kanComplex {G : Type u} [Group G] (B : Action PointedSimplicialSet.{u} G)
    [KanComplex B.V.right] (j : SimplexCategory) : KanComplex ((obj B).obj j).right := by
  induction j using SimplexCategory.rec with | _ n =>
  let : KanComplex (PointedSimplicialSet.forget.obj
      (PointedWeightedEnd.obj (FreeActionFamily.weight (Fin n → G))
        (FreeActionFamily.pointedCoefficients B))) := FreeActionFamily.pointedEnd_kanComplex _ B
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.kanComplex_of_iso (PointedSimplicialSet.forget.mapIso (freeIso B n).symm)

end

end SerrePositivity.KST.Spectra.PointedActionCochains
