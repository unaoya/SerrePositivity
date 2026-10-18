module
public import SerrePositivity.InfinityCategories.Stable.LeftFibrationInitialVertexFormula
public import SerrePositivity.InfinityCategories.Stable.LeftFibrationInitialHomComparison

/-! # 始対象の変更と fiber の Hom 表示

概要：始対象を変えた二つの Hom 表示は、底へ送った始対象間の標準同型による前合成で一致する。
方針：各 fiber 頂点で始対象からの一意の射として計算し、その合成則を使う。
規約：比較はホモトピー圏で行う。使われ方：余極限余錐の変更と懸垂の交換作用の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：fiber の頂点に始対象から向かう一意の射を底へ送る。
方針：ホモトピー圏の始対象からの射と終点の等号輸送を合成する。
規約：全空間の quasicategory 性を明示する。使われ方：Hom 表示の代表元の計算。 -/
def leftFibrationInitialVertexHom {E B : SSet.{u}} [Quasicategory E]
    (p : E ⟶ B) (c : E _⦋0⦌) (hc : IsInitialVertex c) (y : B _⦋0⦌)
    (s : (vertexFiber p y) _⦋0⦌) :
    (SSet.HomotopyCategory.mk (p.app (Opposite.op ⦋0⦌) c) : hoFunctor.obj B) ⟶
      SSet.HomotopyCategory.mk y :=
  (hoFunctor.map p).toFunctor.map (hc.isInitialHo.to (SSet.HomotopyCategory.mk s.val)) ≫
    eqToHom (congrArg (fun x => (SSet.HomotopyCategory.mk x : hoFunctor.obj B))
      (s.property.trans (pinchedConstant_zero y)))

/-- 概要：fiber の Hom 同値は各頂点で始対象からの一意の射による公式に一致する。
方針：終点評価の切断で中間空間へ持ち上げ、そこでの代表元の公式を適用する。
規約：底と全空間は quasicategory。使われ方：始対象変更の比較。 -/
lemma leftFibrationInitialFiberPiZeroEquiv_mk {E B : SSet.{u}}
    [Quasicategory E] [Quasicategory B] (p : E ⟶ B) [LeftFibration p]
    (c : E _⦋0⦌) (hc : IsInitialVertex c) (y : B _⦋0⦌)
    (s : (vertexFiber p y) _⦋0⦌) :
    leftFibrationInitialFiberPiZeroEquiv p c hc y (SSet.π₀.mk s) =
      leftFibrationInitialVertexHom p c hc y s := by
  let t := (leftFibrationInitialSection p c hc y).app (Opposite.op ⦋0⦌) s
  have ht : (leftFibrationInitialEvaluation p c y).app (Opposite.op ⦋0⦌) t = s :=
    ConcreteCategory.congr_hom (NatTrans.congr_app
      (leftFibrationInitialSection_evaluation p c hc y) (Opposite.op ⦋0⦌)) s
  have h := leftFibrationInitialFiberPiZeroEquiv_total_initialHom p c hc y t
  change leftFibrationInitialFiberPiZeroEquiv p c hc y
    (SSet.π₀.mk ((leftFibrationInitialEvaluation p c y).app (Opposite.op ⦋0⦌) t)) =
    leftFibrationInitialVertexHom p c hc y
      ((leftFibrationInitialEvaluation p c y).app (Opposite.op ⦋0⦌) t) at h
  rwa [ht] at h

/-- 概要：二つの始対象による fiber の Hom 表示は標準同型による前合成で一致する。
方針：連結成分の代表頂点を取り、始対象からの一意の射の合成を計算する。
規約：始対象間の同型は Core の標準選択。使われ方：余極限の選択変更の Hom 表示。 -/
lemma leftFibrationInitialFiberPiZeroEquiv_change_initial {E B : SSet.{u}}
    [Quasicategory E] [Quasicategory B] (p : E ⟶ B) [LeftFibration p]
    (c d : E _⦋0⦌) (hc : IsInitialVertex c) (hd : IsInitialVertex d) (y : B _⦋0⦌)
    (a : SSet.π₀ (vertexFiber p y)) :
    (hoFunctor.map p).toFunctor.map (initialVertexIso hc hd).hom ≫
      leftFibrationInitialFiberPiZeroEquiv p d hd y a =
    leftFibrationInitialFiberPiZeroEquiv p c hc y a := by
  obtain ⟨s, rfl⟩ := SSet.π₀.mk_surjective a
  rw [leftFibrationInitialFiberPiZeroEquiv_mk, leftFibrationInitialFiberPiZeroEquiv_mk]
  dsimp only [leftFibrationInitialVertexHom]
  rw [← Category.assoc, ← Functor.map_comp]
  have h : (initialVertexIso hc hd).hom ≫
      hd.isInitialHo.to (SSet.HomotopyCategory.mk s.val) =
    hc.isInitialHo.to (SSet.HomotopyCategory.mk s.val) := hc.isInitialHo.hom_ext _ _
  rw [h]

end SerrePositivity.InfinityCategories
