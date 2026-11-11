module

public import SerrePositivity.KST.Spectra.PointedActionCochainHomotopy
public import SerrePositivity.KST.Spectra.FunctionComplexIsoFormula
public import SerrePositivity.KST.Spectra.PointedWeightedEndBasepoint

/-!
概要：群 cochain の関数複体への比較の基点の具体的な表示。
方針：点つき自由軌道比較の後、end の基点の定数族を自由軌道の第一座標で評価する。
規約：各関数座標の値は元の係数の同じ基点となる。
使われ方：Goerss–Jardine VIII §2、HA §1.4.2。有理 cochain の基点を固定した π_* の表示。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonoidalClosed SSet

open scoped Simplicial

namespace SerrePositivity.KST.Spectra.PointedActionCochains

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：cochain の基点は関数複体の各座標で係数の基点になる。
方針：自由基点の制限、自由作用の end、離散内部 Hom の比較の具体式を合成する。
規約：基点の単位単体集合からの射としての厳密な等式。
使われ方：Goerss–Jardine VIII §2。基点を固定した関数群の π_* への同定。 -/
lemma functionIso_basepoint {G : Type u} [Group G]
    (B : Action PointedSimplicialSet.{u} G) (n : ℕ) :
    ((obj B).obj (SimplexCategory.mk n)).hom ≫ (functionIso B n).hom =
      _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialFunctionComplex.lift (fun (_ : Fin n → G) ↦ B.V.hom) := by
  let S := Fin n → G
  let C := (PointedSimplicialSet.forget.mapAction G).obj B
  let D := FreeActionFamily.pointedCoefficients B
  let W := FreeActionFamily.weight (G := G) S
  change ((obj B).obj (SimplexCategory.mk n)).hom ≫
      ((freeIso B n).hom.right ≫ (PointedWeightedEnd.underlyingIso W D).hom ≫
        (FreeActionFamily.endIso S C).hom ≫ (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.DiscreteInternalHom.iso S B.V.right).hom) = _
  rw [← Category.assoc, Under.w, ← Category.assoc,
    PointedWeightedEnd.underlyingIso_basepoint, ← Category.assoc]
  let t : (𝟙_ SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections (FreeActionFamily.weight (G := G) S)
      (FreeActionFamily.coefficients C) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeComparison W (PointedWeightedEnd.basepointCone D)
  change (t ≫ (FreeActionFamily.endIso S C).hom) ≫ (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.DiscreteInternalHom.iso S C.V).hom = _
  rw [FreeActionFamily.comp_endIso, FreeActionFamily.homEquiv_apply,
    DiscreteInternalHom.comp_iso, uncurry_curry]
  dsimp only [t]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeComparison, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry_lift]
  apply NatTrans.ext
  funext k
  apply ConcreteCategory.hom_ext
  intro a
  rfl

lemma functionIso_basepoint_vertex {G : Type u} [Group G]
    (B : Action PointedSimplicialSet.{u} G) (n : ℕ) :
    (functionIso B n).hom.app _
        (PointedSimplicialSet.basepoint ((obj B).obj (SimplexCategory.mk n))) =
      fun (_ : Fin n → G) ↦ PointedSimplicialSet.basepoint B.V := by
  have h := congr($(NatTrans.congr_app (functionIso_basepoint B n) (Opposite.op ⦋0⦌)) PUnit.unit)
  exact h

/-- 概要：標準基点での群 cochain の正次数ホモトピー群は係数の基点付き群の関数群と同型。
方針：関数複体への同型の基点の式をホモトピー群の同型に用いる。
規約：k は実際の次数 k+1。余単体次数は n。
使われ方：Goerss–Jardine I §7、VIII §2。有理群 cohomology の係数を固定する同定。 -/
def basedHomotopyFunctionEquiv {G : Type u} [Group G]
    (B : Action PointedSimplicialSet.{u} G) [KanComplex B.V.right] (n k : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup ((obj B).obj (SimplexCategory.mk n)).right k
        (PointedSimplicialSet.basepoint ((obj B).obj (SimplexCategory.mk n))) ≃*
      ((Fin n → G) → _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup B.V.right k (PointedSimplicialSet.basepoint B.V)) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfIso k (functionIso B n) (functionIso_basepoint_vertex B n)).trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.homotopyEquiv (Fin n → G) B.V.right k
      (fun _ ↦ PointedSimplicialSet.basepoint B.V))

end

end SerrePositivity.KST.Spectra.PointedActionCochains
