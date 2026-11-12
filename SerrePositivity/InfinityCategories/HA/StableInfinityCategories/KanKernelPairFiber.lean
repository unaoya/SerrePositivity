module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.KanKernelPairLoops
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.LeftFibrationInitialChoice

/-! # 自己引き戻しの固定 fiber からの包含

概要：元の fibration の基点上の fiber を自己引き戻しに含め、ループ比較を頂点で計算する。
方針：引き戻しの fiber の標準同型と既存の固定 fiber 上の公式を合成する。
規約：第二成分を指定基点に固定する。使われ方：成分交換とループの逆射の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：基点の像の上の fiber を第二成分が基点である自己引き戻しに含める。
方針：引き戻しの fiber の標準同型の逆と fiber 包含を合成する。
規約：充填性の仮定は不要。使われ方：ループの代表元を固定 fiber で選ぶ。 -/
def kanKernelPairFiberInclusion {E B : SSet.{u}} (r : E ⟶ B) (e : E _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber r (r.app (Opposite.op ⦋0⦌) e) ⟶ pullback r r :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.vertexFiberPullbackIso r r e).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (pullback.snd r r) e

/-- 概要：固定 fiber の包含の第一成分は元の fiber 包含。
方針：標準同型の第一射影の式を逆射と合成する。
規約：射の等号。使われ方：代表頂点の第一成分の計算。 -/
lemma kanKernelPairFiberInclusion_fst {E B : SSet.{u}} (r : E ⟶ B) (e : E _⦋0⦌) :
    kanKernelPairFiberInclusion r e ≫ pullback.fst r r =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι r (r.app (Opposite.op ⦋0⦌) e) := by
  rw [kanKernelPairFiberInclusion, Category.assoc,
    ← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.vertexFiberPullbackIso_hom_ι, Iso.inv_hom_id_assoc]

/-- 概要：固定 fiber の包含の第二成分は基点への定値写像。
方針：fiber 包含の定義式と定値写像への合成則を使う。
規約：射の等号。使われ方：交換された代表頂点の計算。 -/
lemma kanKernelPairFiberInclusion_snd {E B : SSet.{u}} (r : E ⟶ B) (e : E _⦋0⦌) :
    kanKernelPairFiberInclusion r e ≫ pullback.snd r r = SSet.const e := by
  rw [kanKernelPairFiberInclusion, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp, SSet.comp_const]

/-- 概要：可縮な全空間では固定 fiber の包含は連結成分で全単射。
方針：fiber の標準同型と可縮な底上の fiber 包含の二つの全単射を合成する。
規約：底 B の Kan 性は不要。使われ方：全ての成分を固定 fiber で代表する。 -/
lemma kanKernelPairFiberInclusion_piZero_bijective {E B : SSet.{u}} [KanComplex E]
    (r : E ⟶ B) [Fibration r] (hE : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan E) (e : E _⦋0⦌) :
    Function.Bijective (SSet.mapπ₀ (kanKernelPairFiberInclusion r e)) := by
  have h₁ := (SSet.π₀Functor.mapIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.vertexFiberPullbackIso r r e).symm).toEquiv.bijective
  have h₂ := (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.vertexFiberι_homotopyEquivalence_of_contractible_base
    (pullback.snd r r) hE e).mapPiZero_bijective
  have h : SSet.mapπ₀ (kanKernelPairFiberInclusion r e) =
      SSet.mapπ₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (pullback.snd r r) e) ∘
        (SSet.π₀Functor.mapIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.vertexFiberPullbackIso r r e).symm).toEquiv := by
    funext a
    exact SSet.mapπ₀_comp_apply _ _ a
  rw [h]
  exact h₂.comp h₁

/-- 概要：ループ比較は元の固定 fiber の頂点で始対象からの一意の射を底に送る公式になる。
方針：引き戻しの fiber の標準同型の逆性を使い、既存の代表頂点公式を適用する。
規約：E と B は Kan、E は可縮。使われ方：交換による逆射を代表辺で検証する。 -/
lemma kanKernelPairPiZeroLoopEquiv_fiber_mk {E B : SSet.{u}} [KanComplex E] [KanComplex B]
    (r : E ⟶ B) [Fibration r] (hE : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan E) (e : E _⦋0⦌)
    (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber r (r.app (Opposite.op ⦋0⦌) e)) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.kanKernelPairPiZeroLoopEquiv r hE e
      (SSet.mapπ₀ (kanKernelPairFiberInclusion r e) (SSet.π₀.mk s)) =
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.leftFibrationInitialVertexHom r e (hE.isInitialVertex e)
      (r.app (Opposite.op ⦋0⦌) e) s := by
  rw [kanKernelPairFiberInclusion, SSet.mapπ₀_comp_apply,
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.kanKernelPairPiZeroLoopEquiv_fiber, ← SSet.mapπ₀_comp_apply, Iso.inv_hom_id,
    SSet.mapπ₀_id_apply, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.leftFibrationInitialFiberPiZeroEquiv_mk]

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
