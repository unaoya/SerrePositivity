module
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativeTriangleFinalFiberOutput
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PrismDirectFiberComparison
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.DownVertexIsoComparison
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.TriangleLongPrismRestriction
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativeExtensionBaseIso

/-!
概要：全三角形の図式辺の終点評価を、共通長辺 prism の直接 fiber 評価へ同定する。
方針：同じ全延長を長辺へ制限し、底の等式移送が全座標を保つことを使う。
規約：全延長空間からの厳密な写像等式。使われ方：native 切断と旧模型の指定像の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}}
  (F J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) (b : B _⦋0⦌)
  (D : (Δ[2] : SSet.{u + 1}) ⟶ SpaceInfinity.{u})
local notation "a" => coherentNativeTriangleFiberParameters F b
local notation "s" => coherentCospanFiberPointedSource F b
local notation "i" => scaffoldFirstVertex 2 ▷ a
local notation "v" => snd Δ[0] a ≫ s
local notation "d" => fst Δ[2] a ≫ D
local notation "j" => stdSimplex.δ (1 : Fin 3) ▷ a
variable
  (hv : (snd Δ[0] (coherentNativeTriangleFiberParameters F b) ≫
      coherentCospanFiberPointedSource F b) ≫ pointedSpaceProjection =
    (scaffoldFirstVertex 2 ▷ coherentNativeTriangleFiberParameters F b) ≫
      (fst Δ[2] (coherentNativeTriangleFiberParameters F b) ≫ D))
  (q : (Δ[1] : SSet.{u + 1}) ⊗ coherentNativeTriangleFiberParameters F b ⟶ SpaceInfinity.{u})
  (hq₀ : coherentCospanFiberPointedSource F b ≫ pointedSpaceProjection =
    prismEndpoint 0 (coherentNativeTriangleFiberParameters F b) ≫ q)
  (hq₁ : prismEndpoint 1 (coherentNativeTriangleFiberParameters F b) ≫ q =
    ((smallUnstraighteningSourceRestriction F
      (vertexFiberι (smallLeftUnstraighteningProjection F) b)).left ≫
        leftUnstraighteningProjection F) ≫ J)
  (he : (stdSimplex.δ (1 : Fin 3) ▷ coherentNativeTriangleFiberParameters F b) ≫
    (fst Δ[2] (coherentNativeTriangleFiberParameters F b) ≫ D) = q)
local notation "R" => triangleLongPrismExtensionRestriction pointedSpaceProjection d v hv
local notation "h₀" => triangleLongPrism_initial pointedSpaceProjection d v hv
local notation "E" => relativeExtensionBaseIso pointedSpaceProjection (j ≫ d) q
  (prismEndpoint 0 a) s h₀ hq₀ he

/-- 全三角形から共通長辺へ制限し、同じ底へ移して直接終点を評価する写像。 -/
def trianglePrismDirectFiberOutput :=
  R ≫ (E).hom ≫ coherentPrismDirectFiberOutput F J b q hq₀ hq₁

/-- 図式辺の終点評価と共通長辺 prism の直接評価は、同じ全延長の同じ最終頂点。 -/
lemma relativeTriangleFinalFiberOutput_eq_prism
    (hfinal : (stdSimplex.δ (0 : Fin 3) ≫ D).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm 1) = J.app _ (ULift.up b)) :
    relativeTriangleFinalFiberOutput J b D i v hv 0 hfinal =
      trianglePrismDirectFiberOutput F J b D hv q hq₀ hq₁ he := by
  apply uncurry_injective
  have : Mono (coherentCospanFiberPointedSource J b) := by
    rw [← coherentFiberPointedSourceIso_hom_ι J b]
    infer_instance
  apply (cancel_mono (coherentCospanFiberPointedSource J b)).1
  unfold relativeTriangleFinalFiberOutput trianglePrismDirectFiberOutput
  rw [relativeExtensionCurryRestriction_target_pointed, trianglePrismFinalVertex_eq]
  simp only [uncurry_natural_left, Category.assoc]
  rw [coherentPrismDirectFiberOutput_pointed]
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨x, h⟩
  rfl
local notation "U" => uliftFunctorSpaceIso
  (vertexFiber (smallLeftUnstraighteningProjection F) b)
  (vertexFiber (smallLeftUnstraighteningProjection J) b)
local instance : KanComplex (vertexFiber (smallLeftUnstraighteningProjection J) b) :=
  vertexFiber_kanComplex_of_leftFibration _ _

/-- 同じ全三角形比較の旧長辺出力は、図式辺の直接終点像を下降した指定値。 -/
lemma trianglePrismFiberFunctor_heq_final
    (hfinal : (stdSimplex.δ (0 : Fin 3) ≫ D).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm 1) = J.app _ (ULift.up b))
    {x y : (relativeFunctorExtensionSpace pointedSpaceProjection d i v hv) _⦋0⦌}
    (e : VertexIso x y) :
    HEq ((coherentPrismFiberFunctor F J b q hq₀ hq₁).mapIso
      (VertexIso.map e (R ≫ (E).hom)))
      (downVertexIso (VertexIso.map (VertexIso.map e
        (relativeTriangleFinalFiberOutput J b D i v hv 0 hfinal)) (U).inv)) := by
  let M := R ≫ (E).hom
  let P := coherentPrismDirectFiberOutput F J b q hq₀ hq₁
  have h := coherentPrismFiberFunctor_heq_direct F J b q hq₀ hq₁ (VertexIso.map e M)
  have hc := downVertexIso_map_comp_heq e M (P ≫ (U).inv)
    (relativeTriangleFinalFiberOutput J b D i v hv 0 hfinal) (U).inv
    (congrArg (fun k => k ≫ (U).inv)
      (relativeTriangleFinalFiberOutput_eq_prism F J b D hv q hq₀ hq₁ he hfinal).symm)
  exact h.trans ((heq_of_eq (congrArg (fun z => downVertexIso z)
    (vertexIso_map_comp (VertexIso.map e M) P (U).inv))).trans hc)

end SerrePositivity.InfinityCategories.F2
