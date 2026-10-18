module

public import SerrePositivity.KST.Spectra.FreePointedFunctionNaturality
public import SerrePositivity.KST.Spectra.WeightedCochainsWeightIso
public import SerrePositivity.KST.Spectra.PointedActionCochains

/-!
概要：群作用の点つき cochain と非斉次関数複体の余単体図式の実際の同型。
方針：EG の重みの自然同型で自由軌道の cochain へ移し、各次数の点つき関数表示を束ねる。
規約：全ての顔・退化に対して自然な点つき同型であり Kan 条件は不要。
使われ方：Goerss–Jardine VIII §2、HA §1.4.2。群 cochain の π_* の余単体構造の座標表示。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory SSet

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace GroupActionCochains

/-- 概要：EG の非斉次座標の自由軌道の単体的な離散重み。
方針：自由軌道の図式を離散単体集合の作用図式へ送る。
規約：各次数の重みは G×(Fin n → G)。
使われ方：Goerss–Jardine VIII §2。非斉次 cochain の end の重み。 -/
def freeUniversalWeight (G : Type u) [Group G] :
    SimplicialObject (AsSmall.{u} (SingleObj G) ⥤ SSet.{u}) :=
  freeUniversalCover G ⋙ actionWeightFunctor G

def universalCoverFreeWeightIso (G : Type u) [Group G] :
    universalCoverWeight G ≅ freeUniversalWeight G :=
  Functor.isoWhiskerRight (universalCoverFreeNatIso G) (actionWeightFunctor G)

/-- 概要：群作用の非斉次関数複体を座標ごとの基点で点つきにした余単体図式。
方針：自由軌道の射の点つき前合成を顔・退化へ用いる。
規約：係数には点つき単体集合の作用を入力する。
使われ方：Goerss–Jardine VIII §2。標準基点を保つ非斉次 cochain。 -/
def pointedFunctionCochains {G : Type u} [Group G] (B : Action PointedSimplicialSet.{u} G) :
    CosimplicialObject PointedSimplicialSet.{u} where
  obj n := SimplicialFunctionComplex.pointedObj (Fin n.len → G) B.V
  map f := FreeActionFamily.pointedFunctionPre ((freeUniversalCover G).map f.op) B
  map_id n := by
    rw [op_id, CategoryTheory.Functor.map_id]
    change FreeActionFamily.pointedFunctionPre
      (𝟙 (Action.leftRegular G ⊗ Action.trivial G (Fin n.len → G))) B = 𝟙 _
    exact FreeActionFamily.pointedFunctionPre_id (Fin n.len → G) B
  map_comp f g := by
    rw [op_comp, CategoryTheory.Functor.map_comp, FreeActionFamily.pointedFunctionPre_comp]

/-- 概要：非斉次自由軌道の cochain と点つき関数複体の余単体図式の同型。
方針：自由作用の点つき end の関数表示を重みへの自然性で束ねる。
規約：全ての顔・退化で厳密に自然。
使われ方：Goerss–Jardine VIII §2。非斉次 cochain の図式の同定。 -/
def freeFunctionNatIso {G : Type u} [Group G] (B : Action PointedSimplicialSet.{u} G) :
    weightedCochains (freeUniversalWeight G) (FreeActionFamily.pointedCoefficients B) ≅
      pointedFunctionCochains B :=
  NatIso.ofComponents (fun n ↦ FreeActionFamily.pointedFunctionIso (Fin n.len → G) B)
    (fun f ↦ FreeActionFamily.pointedFunctionIso_pre ((freeUniversalCover G).map f.op) B)

end GroupActionCochains

/-- 概要：群作用の元の cochain は非斉次座標の点つき関数複体の図式と同型。
方針：EG の座標変更の重みの同型と自由軌道の関数表示を合成する。
規約：対象ごとの同型に加えて全ての余単体構造を保持する。
使われ方：Goerss–Jardine VIII §2、HA §1.4.2。有理 cochain 計算の余単体比較。 -/
def PointedActionCochains.functionNatIso {G : Type u} [Group G]
    (B : Action PointedSimplicialSet.{u} G) :
    obj B ≅ GroupActionCochains.pointedFunctionCochains B :=
  WeightedCochains.weightIso (GroupActionCochains.universalCoverFreeWeightIso G)
      (FreeActionFamily.pointedCoefficients B) ≪≫
    GroupActionCochains.freeFunctionNatIso B

end

end SerrePositivity.KST.Spectra
