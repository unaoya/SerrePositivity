module
public import SerrePositivity.KST.Fibration.ContractiblePointInclusion
public import SerrePositivity.KST.Comparison.HomotopyPullbackThreeInputs

/-! # 可縮な基底側の実四角形と指定した基点上のホモトピーファイバー -/

@[expose] public section
noncomputable section
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
open SerrePositivity.KST.Comparison
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Fibration

/-- 指定した基点を通る実 cospan の比較。左射影を恒等射のまま保つ。 -/
def pointFiberToContractiblePullback {X Y B : SSet.{u}}
    (f : X ⟶ B) (g : Y ⟶ B) (z : Δ[0] ⟶ Y) :
    homotopyPullbackObject f (z ≫ g) ⟶ homotopyPullbackObject f g :=
  homotopyPullbackMap (𝟙 X) z (𝟙 B) (by simp) (by simp)

/-- 元の一点射の可逆性から、指定した基点上の実 fiber 模型との比較が局所化同型。 -/
theorem pointFiberToContractiblePullback_localized_isIso {X Y B : SSet.{u}}
    (f : X ⟶ B) (g : Y ⟶ B) (z : Δ[0] ⟶ Y)
    (hy : IsIso (AnodyneHomotopy.anodyneQ.map (terminal.from Y))) :
    IsIso (AnodyneHomotopy.anodyneQ.map (pointFiberToContractiblePullback f g z)) :=
  homotopyPullbackMap_localized_isIso (𝟙 X) z (𝟙 B) (by simp) (by simp)
    (by infer_instance) (pointInclusion_localized_isIso z hy) (by infer_instance)

/-- 元の射影は、同じ指定基点の比較の後でも厳密に回収される。 -/
lemma pointFiberToContractiblePullback_fst {X Y B : SSet.{u}}
    (f : X ⟶ B) (g : Y ⟶ B) (z : Δ[0] ⟶ Y) :
    pointFiberToContractiblePullback f g z ≫ pullback.fst f
        (AnodyneKanReplacement.factorization.p.app (Arrow.mk g)) =
      pullback.fst f (AnodyneKanReplacement.factorization.p.app (Arrow.mk (z ≫ g))) := by
  unfold pointFiberToContractiblePullback
  rw [homotopyPullbackMap_fst, Category.comp_id]

/-- 元の homotopy pullback 四角形の頂点は、指定した基点上の fiber と局所化で同型。 -/
def contractibleBaseFiberIso {P X Y B : SSet.{u}}
    {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ B} {g : Y ⟶ B}
    (sq : CommSq a b f g) (hs : IsHomotopyPullback sq)
    (hy : IsIso (AnodyneHomotopy.anodyneQ.map (terminal.from Y))) (z : Δ[0] ⟶ Y) :
    AnodyneHomotopy.anodyneQ.obj P ≅
      AnodyneHomotopy.anodyneQ.obj (homotopyPullbackObject f (z ≫ g)) := by
  have : IsIso (AnodyneHomotopy.anodyneQ.map (homotopyPullbackComparison sq)) := hs
  have := pointFiberToContractiblePullback_localized_isIso f g z hy
  exact asIso (AnodyneHomotopy.anodyneQ.map (homotopyPullbackComparison sq)) ≪≫
    (asIso (AnodyneHomotopy.anodyneQ.map (pointFiberToContractiblePullback f g z))).symm

/-- 指定した fiber との同型は、元の四角形の左上から右上への射そのものを回収する。 -/
theorem contractibleBaseFiberIso_hom_fst {P X Y B : SSet.{u}}
    {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ B} {g : Y ⟶ B}
    (sq : CommSq a b f g) (hs : IsHomotopyPullback sq)
    (hy : IsIso (AnodyneHomotopy.anodyneQ.map (terminal.from Y))) (z : Δ[0] ⟶ Y) :
    (contractibleBaseFiberIso sq hs hy z).hom ≫ AnodyneHomotopy.anodyneQ.map
        (pullback.fst f (AnodyneKanReplacement.factorization.p.app (Arrow.mk (z ≫ g)))) =
      AnodyneHomotopy.anodyneQ.map a := by
  let Q := AnodyneHomotopy.anodyneQ
  let m := pointFiberToContractiblePullback f g z
  let π₀ : homotopyPullbackObject f g ⟶ X :=
    pullback.fst f (AnodyneKanReplacement.factorization.p.app (Arrow.mk g))
  let π₁ : homotopyPullbackObject f (z ≫ g) ⟶ X :=
    pullback.fst f (AnodyneKanReplacement.factorization.p.app (Arrow.mk (z ≫ g)))
  have hm : Q.map m ≫ Q.map π₀ = Q.map π₁ := by
    rw [← Q.map_comp]
    exact congrArg Q.map (pointFiberToContractiblePullback_fst f g z)
  have : IsIso (Q.map m) := pointFiberToContractiblePullback_localized_isIso f g z hy
  change (Q.map (homotopyPullbackComparison sq) ≫ inv (Q.map m)) ≫ Q.map π₁ = Q.map a
  rw [Category.assoc, ← hm, IsIso.inv_hom_id_assoc, ← Q.map_comp]
  exact congrArg Q.map (homotopyPullbackComparison_fst sq)

end SerrePositivity.KST.Fibration
