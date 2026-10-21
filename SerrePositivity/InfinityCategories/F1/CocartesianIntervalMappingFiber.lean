module

public import SerrePositivity.InfinityCategories.F1.CocartesianIntervalMappingCorePullback
public import SerrePositivity.InfinityCategories.F1.PullbackFiber

/-!
概要：一成分を固定した元の一次元 Hom の core を、同じ後合成の fiber と同定する。
方針：元の pullback の普遍性で、両方向の fiber の射を構成する。
規約：成分の頂点と全高次の零成分評価を厳密に保持する。
使われ方：実際の一次元 Hom 比較の、成分固定での局所比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

variable (F G : CocartesianTransportDiagramCategory (ULift.{u} (Fin 2)))
local notation "p" => (quasicategoryCoreMap
  (CategoryTheory.Functor.map (ihom (F.val.obj (ULift.up 0)))
  (G.val.map strictIntervalIndexArrow)))
local notation "q" => (quasicategoryCoreMap (NatTrans.app (pre (F.val.map strictIntervalIndexArrow))
  (G.val.obj (ULift.up 1))))
local notation "e₀" => quasicategoryCoreMap
  (strictDiagramMappingComponent F.val G.val (ULift.up 0))
local notation "e₁" => quasicategoryCoreMap
  (strictDiagramMappingComponent F.val G.val (ULift.up 1))

/-- 一成分を固定した元の Hom の core は、同じ後合成の指定された頂点上の fiber。 -/
def cocartesianIntervalMappingFiberIso
    (b : (quasicategoryCore ((ihom (F.val.obj (ULift.up 1))).obj
      (G.val.obj (ULift.up 1)))) _⦋0⦌) :
    vertexFiber e₁ b ≅ vertexFiber p ((q).app (Opposite.op ⦋0⦌) b) :=
by
  let hp := cocartesianIntervalMappingCore_isPullback F G
  let ι := vertexFiberι e₁ b
  let ι' := vertexFiberι p ((q).app (Opposite.op ⦋0⦌) b)
  have hh : (ι ≫ e₀) ≫ p = SSet.const ((q).app (Opposite.op ⦋0⦌) b) := by
    rw [Category.assoc, hp.w, ← Category.assoc, vertexFiberι_comp, SSet.const_comp]
  let H := vertexFiberLift p ((q).app (Opposite.op ⦋0⦌) b) (ι ≫ e₀) hh
  let L := hp.lift ι' (SSet.const b) (by rw [vertexFiberι_comp, SSet.const_comp])
  let V := vertexFiberLift e₁ b L (hp.lift_snd _ _ _)
  have hH : H ≫ ι' = ι ≫ e₀ := vertexFiberLift_ι _ _ _ _
  have hV : V ≫ ι = L := vertexFiberLift_ι _ _ _ _
  refine ⟨H, V, ?_, ?_⟩
  · apply vertexFiber_hom_ext e₁ b
    change (H ≫ V) ≫ ι = (𝟙 _) ≫ ι
    rw [Category.assoc, hV, Category.id_comp]
    apply hp.hom_ext
    · rw [Category.assoc, hp.lift_fst, hH]
    · rw [Category.assoc, hp.lift_snd, SSet.comp_const, vertexFiberι_comp]
  · apply vertexFiber_hom_ext p ((q).app (Opposite.op ⦋0⦌) b)
    change (V ≫ H) ≫ ι' = (𝟙 _) ≫ ι'
    rw [Category.assoc, hH, ← Category.assoc, hV, Category.id_comp]
    exact hp.lift_fst _ _ _

/-- 同じ fiber 同型の全次数での値は、元の零成分の評価そのもの。 -/
lemma cocartesianIntervalMappingFiberIso_hom_app_val
    (b : (quasicategoryCore ((ihom (F.val.obj (ULift.up 1))).obj
      (G.val.obj (ULift.up 1)))) _⦋0⦌) (n : SimplexCategoryᵒᵖ)
    (x : (vertexFiber e₁ b).obj n) :
    (((cocartesianIntervalMappingFiberIso F G b).hom.app n) x).val =
      (e₀).app n x.val := rfl

end SerrePositivity.InfinityCategories
