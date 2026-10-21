module

public import SerrePositivity.InfinityCategories.F1.CocartesianIntervalMappingFiber
public import SerrePositivity.InfinityCategories.F1.CocartesianHomComponentPullback
public import SerrePositivity.InfinityCategories.F1.UniverseFiber
public import SerrePositivity.InfinityCategories.F1.LeftFiberKan

/-!
概要：元の後合成 fiber を、実際の source の固定成分 fiber と同じ宇宙で同定する。
方針：検証済みの一次元の fiber 同型と、fiber の宇宙持ち上げの同型を合成する。
規約：元の零成分の全次数の評価を保持する。
使われ方：後合成 fiber から同じ指定外ホーン fiber への実際の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

variable (F G : CocartesianTransportDiagramCategory (ULift.{u} (Fin 2)))
variable (b : ((SSet.uliftFunctor.{u + 1, u}).obj
  (SimplicialCategory.sHom (cocartesianTransportDiagramValue F (ULift.up 1))
    (cocartesianTransportDiagramValue G (ULift.up 1)))) _⦋0⦌)
local notation "p" => quasicategoryCoreMap (CategoryTheory.Functor.map
  (ihom (F.val.obj (ULift.up 0))) (G.val.map strictIntervalIndexArrow))
local notation "q" => quasicategoryCoreMap (NatTrans.app (pre (F.val.map strictIntervalIndexArrow))
  (G.val.obj (ULift.up 1)))
local notation "e₁" => quasicategoryCoreMap
  (strictDiagramMappingComponent F.val G.val (ULift.up 1))

/-- 元の後合成の、同じ固定成分を前合成した頂点上の fiber。 -/
def cocartesianIntervalPostcompositionFiber : SSet.{u} :=
  vertexFiber p (NatTrans.app q (Opposite.op ⦋0⦌) b.down)

/-- 元の後合成 fiber は、元の輸送射の Kan 性から Kan 複体になる。 -/
lemma cocartesianIntervalPostcompositionFiber_kanComplex :
    KanComplex (cocartesianIntervalPostcompositionFiber F G b) := by
  letI := core_cocartesianIntervalPostHom_fibration G (F.val.obj (ULift.up 0))
  exact vertexFiber_kanComplex_of_leftFibration _ _

/-- 実際の source の固定成分 fiber と、元の後合成 fiber の同じ宇宙での厳密な同型。 -/
def cocartesianHomSourcePostcompositionFiberIso :
    vertexFiber (cocartesianHomSourceComponent F G (ULift.up 1)) b ≅
      (SSet.uliftFunctor.{u + 1, u}).obj (cocartesianIntervalPostcompositionFiber F G b) :=
  (uliftVertexFiberIso.{u, u + 1} e₁ b.down).symm ≪≫
    (SSet.uliftFunctor.{u + 1, u}).mapIso (cocartesianIntervalMappingFiberIso F G b.down)

/-- 同じ同型の後合成 fiber への包含は、元の零成分評価の宇宙持ち上げ。 -/
lemma cocartesianHomSourcePostcompositionFiberIso_hom_ι :
    (cocartesianHomSourcePostcompositionFiberIso F G b).hom ≫
        (SSet.uliftFunctor.{u + 1, u}).map
          (vertexFiberι p (NatTrans.app q (Opposite.op ⦋0⦌) b.down)) =
      vertexFiberι (cocartesianHomSourceComponent F G (ULift.up 1)) b ≫
        (SSet.uliftFunctor.{u + 1, u}).map
          (quasicategoryCoreMap (strictDiagramMappingComponent F.val G.val (ULift.up 0))) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro x
  rfl

/-- 同じ同型の逆の後の零成分評価は、元の後合成 fiber の包含そのもの。 -/
lemma cocartesianHomSourcePostcompositionFiberIso_inv_component_zero :
    (cocartesianHomSourcePostcompositionFiberIso F G b).inv ≫
        vertexFiberι (cocartesianHomSourceComponent F G (ULift.up 1)) b ≫
        (SSet.uliftFunctor.{u + 1, u}).map
          (quasicategoryCoreMap (strictDiagramMappingComponent F.val G.val (ULift.up 0))) =
      (SSet.uliftFunctor.{u + 1, u}).map
        (vertexFiberι p (NatTrans.app q (Opposite.op ⦋0⦌) b.down)) := by
  rw [← cocartesianHomSourcePostcompositionFiberIso_hom_ι, ← Category.assoc,
    Iso.inv_hom_id, Category.id_comp]

end SerrePositivity.InfinityCategories
