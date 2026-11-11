module

public import SerrePositivity.KST.Spectra.FreeActionFunctionIso
public import SerrePositivity.KST.Spectra.PointedWeightedEndBasepoint

/-!
概要：自由作用の点つき end と基点を座標ごとに固定した関数複体の同型。
方針：基点の定数族を軌道代表で評価し、自由軌道の前合成も点つき射へ持ち上げる。
規約：任意の群と添字集合で構成する。
使われ方：Goerss–Jardine VIII §2、HA §1.4.2。群 cochain の顔写像の基点付きの比較。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory SSet


namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：関数複体を全座標の基点の関数で点つきにする。
方針：元の基点の射を各座標に lift する。
規約：基礎単体集合は指定した関数複体そのもの。
使われ方：Goerss–Jardine I §7、VIII §2。基点付きの関数群の単体的な模型。 -/
def SimplicialFunctionComplex.pointedObj (S : Type u) (X : PointedSimplicialSet.{u}) :
    PointedSimplicialSet.{u} := Under.mk (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialFunctionComplex.lift (fun (_ : S) ↦ X.hom))

namespace FreeActionFamily

variable {G : Type u} [Group G]

/-- 概要：自由軌道の射による関数の前合成は係数の基点を座標ごとに保つ。
方針：各座標で係数の群作用の基点保存を使う。
規約：係数の作用は点つき単体集合の作用。
使われ方：Goerss–Jardine VIII §2。群 cochain の点つき顔・退化の式。 -/
def pointedFunctionPre {S T : Type u}
    (θ : (Action.leftRegular G ⊗ Action.trivial G T) ⟶
      (Action.leftRegular G ⊗ Action.trivial G S)) (B : Action PointedSimplicialSet.{u} G) :
    SimplicialFunctionComplex.pointedObj S B.V ⟶ SimplicialFunctionComplex.pointedObj T B.V :=
  Under.homMk (functionPre θ ((PointedSimplicialSet.forget.mapAction G).obj B)) (by
    apply _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialFunctionComplex.hom_ext
    intro t
    let C := (PointedSimplicialSet.forget.mapAction G).obj B
    let p : (𝟙_ SSet.{u}) ⟶ C.V := B.V.hom
    change ((_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialFunctionComplex.lift (fun (_ : S) ↦ p)) ≫ functionPre θ C) ≫
        _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialFunctionComplex.eval T C.V t =
      _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialFunctionComplex.lift (fun (_ : T) ↦ p) ≫ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialFunctionComplex.eval T C.V t
    rw [Category.assoc, functionPre_eval, ← Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialFunctionComplex.lift_eval, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialFunctionComplex.lift_eval]
    exact Under.w (B.ρ (θ.hom ((1 : G), t)).1).asHom)

/-- 概要：自由作用の点つき end は点つき関数複体と同型。
方針：end の忘却の比較と関数表示を合成し、基点の定数族の具体式を使う。
規約：Kan 性を仮定しない実際の点つき同型。
使われ方：Goerss–Jardine VIII §2、HA §1.4.2。基点を保つ非斉次 cochain の表示。 -/
def pointedFunctionIso (S : Type u) (B : Action PointedSimplicialSet.{u} G) :
    PointedWeightedEnd.obj (weight S) (pointedCoefficients B) ≅
      SimplicialFunctionComplex.pointedObj S B.V :=
  Under.isoMk
    (PointedWeightedEnd.underlyingIso (weight S) (pointedCoefficients B) ≪≫
      functionIso S ((PointedSimplicialSet.forget.mapAction G).obj B)) (by
    change (PointedWeightedEnd.obj (weight S) (pointedCoefficients B)).hom ≫
        ((PointedWeightedEnd.underlyingIso (weight S) (pointedCoefficients B)).hom ≫
          (functionIso S ((PointedSimplicialSet.forget.mapAction G).obj B)).hom) = _
    rw [← Category.assoc, PointedWeightedEnd.underlyingIso_basepoint]
    let t : (𝟙_ SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections (weight S)
        (coefficients ((PointedSimplicialSet.forget.mapAction G).obj B)) :=
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeComparison (weight S) (PointedWeightedEnd.basepointCone (pointedCoefficients B))
    change t ≫ (functionIso S ((PointedSimplicialSet.forget.mapAction G).obj B)).hom = _
    rw [comp_functionIso]
    dsimp only [t]
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeComparison, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry_lift]
    rfl)

end FreeActionFamily

end

end SerrePositivity.KST.Spectra
