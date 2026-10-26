module

public import SerrePositivity.InfinityCategories.Core.FullSubcomplexFibration
public import SerrePositivity.InfinityCategories.Core.VertexFiber
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.FunctorFiber

/-!
概要：頂点条件への制限と、同じ指定頂点上の実 fiber の操作を交換する。
方針：両方の元の包含を保持した二方向の実持ち上げを構成する。
規約：全次数の厳密同型であり、quasicategory 性を要求しない。
使われ方：元の固定端点 marked span を、全錐族の全部分複体として比較する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
variable {X Y : SSet.{u}} (P : X _⦋0⦌ → Prop) (f : X ⟶ Y)
  (fp : (fullSubcomplexOnVertices X P : SSet.{u}) ⟶ Y)
  (hf : fp = (fullSubcomplexOnVertices X P).ι ≫ f) (y : Y _⦋0⦌)

/-- 元の fiber の中で、同じ周囲の頂点条件を課す全部分複体。 -/
def fullSubcomplexFiber : (vertexFiber f y).Subcomplex :=
  fullSubcomplexOnVertices _ (fun v => P ((vertexFiberι f y).app (Opposite.op ⦋0⦌) v))

def fullSubcomplexFiberMap : vertexFiber fp y ⟶ (fullSubcomplexFiber P f y : SSet.{u}) := by
  let L := vertexFiberLift f y
    (vertexFiberι fp y ≫ (fullSubcomplexOnVertices X P).ι) (by
      rw [Category.assoc, ← hf, vertexFiberι_comp])
  exact fullSubcomplexLift _ L (fun v => fullSubcomplexOnVertices_vertex v.val)

lemma fullSubcomplexFiberMap_ambient :
    fullSubcomplexFiberMap P f fp hf y ≫ (fullSubcomplexFiber P f y).ι ≫ vertexFiberι f y =
      vertexFiberι fp y ≫ (fullSubcomplexOnVertices X P).ι := by
  dsimp only [fullSubcomplexFiber]
  rw [fullSubcomplexFiberMap, ← Category.assoc, fullSubcomplexLift_ι, vertexFiberLift_ι]

def fullSubcomplexFiberInverse : (fullSubcomplexFiber P f y : SSet.{u}) ⟶ vertexFiber fp y := by
  let L := fullSubcomplexLift P ((fullSubcomplexFiber P f y).ι ≫ vertexFiberι f y)
    (fun v => fullSubcomplexOnVertices_vertex v)
  exact vertexFiberLift fp y L (by
    rw [hf, ← Category.assoc, fullSubcomplexLift_ι, Category.assoc,
      vertexFiberι_comp, SSet.comp_const])

lemma fullSubcomplexFiberInverse_ambient :
    fullSubcomplexFiberInverse P f fp hf y ≫ vertexFiberι fp y ≫
      (fullSubcomplexOnVertices X P).ι = (fullSubcomplexFiber P f y).ι ≫ vertexFiberι f y := by
  rw [fullSubcomplexFiberInverse, ← Category.assoc, vertexFiberLift_ι, fullSubcomplexLift_ι]

/-- 制限後の元の fiber と、元の fiber の同じ全部分複体の厳密同型。 -/
def fullSubcomplexFiberIso : vertexFiber fp y ≅ (fullSubcomplexFiber P f y : SSet.{u}) where
  hom := fullSubcomplexFiberMap P f fp hf y
  inv := fullSubcomplexFiberInverse P f fp hf y
  hom_inv_id := by
    apply (cancel_mono (vertexFiberι fp y ≫ (fullSubcomplexOnVertices X P).ι)).mp
    calc
      (fullSubcomplexFiberMap P f fp hf y ≫ fullSubcomplexFiberInverse P f fp hf y) ≫
          (vertexFiberι fp y ≫ (fullSubcomplexOnVertices X P).ι) =
        fullSubcomplexFiberMap P f fp hf y ≫
          (fullSubcomplexFiberInverse P f fp hf y ≫ vertexFiberι fp y ≫
            (fullSubcomplexOnVertices X P).ι) := by simp only [Category.assoc]
      _ = fullSubcomplexFiberMap P f fp hf y ≫
          ((fullSubcomplexFiber P f y).ι ≫ vertexFiberι f y) := by
        rw [fullSubcomplexFiberInverse_ambient]
      _ = vertexFiberι fp y ≫ (fullSubcomplexOnVertices X P).ι :=
        fullSubcomplexFiberMap_ambient P f fp hf y
      _ = _ := (Category.id_comp _).symm
  inv_hom_id := by
    apply (cancel_mono ((fullSubcomplexFiber P f y).ι ≫ vertexFiberι f y)).mp
    calc
      (fullSubcomplexFiberInverse P f fp hf y ≫ fullSubcomplexFiberMap P f fp hf y) ≫
          ((fullSubcomplexFiber P f y).ι ≫ vertexFiberι f y) =
        fullSubcomplexFiberInverse P f fp hf y ≫
          (fullSubcomplexFiberMap P f fp hf y ≫ (fullSubcomplexFiber P f y).ι ≫
            vertexFiberι f y) := by simp only [Category.assoc]
      _ = fullSubcomplexFiberInverse P f fp hf y ≫
          (vertexFiberι fp y ≫ (fullSubcomplexOnVertices X P).ι) := by
        rw [fullSubcomplexFiberMap_ambient]
      _ = (fullSubcomplexFiber P f y).ι ≫ vertexFiberι f y :=
        fullSubcomplexFiberInverse_ambient P f fp hf y
      _ = _ := (Category.id_comp _).symm

end SerrePositivity.KST.LocalizingInvariants
