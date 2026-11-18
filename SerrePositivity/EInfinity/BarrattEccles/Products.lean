module

public import SerrePositivity.EInfinity.BarrattEccles.DiagramModel
public import SerrePositivity.HomotopicalAlgebra.Quillen.DerivedFunctor
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
# 小さい E 代数の積は homotopy 積を計算する

概要：BM 命題 4.1 のモデルで任意の小さい積を右導来極限として構成する。
方針：離散図式の二つの右類と積での安定性、全図式の fibrancy を使う。
規約：空積も含む。一般の非離散図式の通常の極限へは拡張しない。
使われ方：E2a-4 の一般 homotopy 極限を構成するための積。
-/

@[expose] public section

noncomputable section

universe u v w v' w'

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory Limits HomotopicalAlgebra

variable (A : Type u) [CommRing A] (ι : Type u)

set_option synthInstance.maxHeartbeats 40000
set_option maxHeartbeats 400000
/-- 概要：離散 E 代数図式の極限関手（BM §1）。
方針：通常の小積を取る。
規約：離散図式そのものを始域に使い、空の添字も許す。
使われ方：homotopy 積の右導来関手の元の関手。 -/
def productFunctor : (Discrete ι ⥤ (operad A).Algebra) ⥤ (operad A).Algebra :=
  letI : HasLimitsOfSize.{u, u} (DifferentialGraded.Complex A) := ⟨fun _ _ => inferInstance⟩
  lim

/-- 概要：小積は離散図式の具体的なモデルに対して右 Quillen（BM 命題 4.1）。
方針：fibration と trivial fibration の積での安定性を使う。
規約：両モデルは具体的なものを局所的に選ぶ。
使われ方：小積の右導来関手の存在と計算。 -/
lemma productFunctor_isRightQuillen :
    let := modelCategory A
    let := Diagram.projectiveModelCategory A (Discrete ι)
    SerrePositivity.Quillen.IsRightQuillen (productFunctor A ι) := by
  let := modelCategory A
  let := Diagram.projectiveModelCategory A (Discrete ι)
  constructor
  · intro F G f hf
    exact (fibrations (operad A).Algebra).limMap f hf
  · intro F G f hf
    exact (trivialFibrations (operad A).Algebra).limMap f
      (fun k => ⟨hf.1 k, hf.2 k⟩)

/-- 概要：小積は各頂点の擬同型を弱同値へ移す（BM 命題 4.1、Hovey §1.3）。
方針：全図式の fibrancy と右 Quillen 関手の Brown 補題を使う。
規約：有限性・始域の cofibrancy は仮定しない。
使われ方：通常の小積による homotopy 積のホモトピー不変性。 -/
lemma product_map_weakEquivalence {F G : Discrete ι ⥤ (operad A).Algebra}
    (f : F ⟶ G) (hf : ∀ k, QuasiIso (f.app k).hom) :
    let := modelCategory A
    WeakEquivalence ((productFunctor A ι).map f) := by
  let := modelCategory A
  let := Diagram.projectiveModelCategory A (Discrete ι)
  have := productFunctor_isRightQuillen A ι
  have := Diagram.isFibrant A (Discrete ι) F
  have := Diagram.isFibrant A (Discrete ι) G
  have : WeakEquivalence f := (Diagram.weakEquivalence_iff A (Discrete ι) f).mpr hf
  exact SerrePositivity.Quillen.map_weakEquivalence_of_fibrant (productFunctor A ι) f

/-- 概要：E 代数の小積の点ごとの右導来関手は存在する（Hovey §1.3）。
方針：証明済みの右 Quillen 性から fibrant 置換による導来構成を使う。
規約：値の局所化は任意、モデル構造の入力仮定なし。
使われ方：小さい homotopy 積の普遍的な導来関手。 -/
lemma productFunctor_hasPointwiseRightDerivedFunctor
    {H : Type w} [Category.{v} H] (Q : (operad A).Algebra ⥤ H) :
    let := modelCategory A
    let := Diagram.projectiveModelCategory A (Discrete ι)
    Q.IsLocalization (weakEquivalences (operad A).Algebra) →
      (productFunctor A ι ⋙ Q).HasPointwiseRightDerivedFunctor
        (weakEquivalences (Discrete ι ⥤ (operad A).Algebra)) := by
  let := modelCategory A
  let := Diagram.projectiveModelCategory A (Discrete ι)
  change Q.IsLocalization (weakEquivalences (operad A).Algebra) → _
  intro hQ
  have := hQ
  have := productFunctor_isRightQuillen A ι
  infer_instance

/-- 概要：通常の小積は元の図式で右導来積を計算する（Hovey §1.3）。
方針：全離散図式の fibrancy と fibrant 点での導来比較を使う。
規約：局所化と右導来関手の選択は任意、図式の置換は不要。
使われ方：任意の小さい homotopy 積の実際の値。 -/
def productDerivedIso (X : ι → (operad A).Algebra)
    {H : Type w} [Category.{v} H] {D : Type w'} [Category.{v'} D]
    (Q : (operad A).Algebra ⥤ H) (L : (Discrete ι ⥤ (operad A).Algebra) ⥤ D)
    (RF : D ⥤ H) (β : productFunctor A ι ⋙ Q ⟶ L ⋙ RF) :
    let := modelCategory A
    letI : HasLimitsOfSize.{u, u} (DifferentialGraded.Complex A) := ⟨fun _ _ => inferInstance⟩
    let := Diagram.projectiveModelCategory A (Discrete ι)
    ∀ [Q.IsLocalization (weakEquivalences (operad A).Algebra)]
      [L.IsLocalization (weakEquivalences (Discrete ι ⥤ (operad A).Algebra))],
      RF.IsRightDerivedFunctor β (weakEquivalences (Discrete ι ⥤ (operad A).Algebra)) →
      (Q.obj (∏ᶜ X) ≅ RF.obj (L.obj (Discrete.functor X))) := by
  let := modelCategory A
  letI : HasLimitsOfSize.{u, u} (DifferentialGraded.Complex A) := ⟨fun _ _ => inferInstance⟩
  let := Diagram.projectiveModelCategory A (Discrete ι)
  dsimp only
  intro hQ hL hRF
  have := hQ
  have := hL
  have := hRF
  have := productFunctor_isRightQuillen A ι
  have := Diagram.isFibrant A (Discrete ι) (Discrete.functor X)
  have : IsIso (β.app (Discrete.functor X)) :=
    SerrePositivity.Quillen.rightComparison_isIso Q L β (Discrete.functor X)
  exact @asIso H _ _ _ (β.app (Discrete.functor X)) this

/-- 概要：小さい E 代数の積の底は同じ複体の積（BM §1）。
方針：代数の忘却が極限を作ることから積の保存同型を使う。
規約：元の図式と元の作用を使い、空積も含む。
使われ方：homotopy 積の底の複体を実際に記述する。 -/
def productCarrierIso (X : ι → (operad A).Algebra) :
    (∏ᶜ X).carrier ≅ ∏ᶜ (fun i => (X i).carrier) :=
  PreservesProduct.iso (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget (operad A)) X

end SerrePositivity.EInfinity.BarrattEccles
