module

public import
SerrePositivity.InfinityCategories.F2.FilteredExchange.RelativeExtensionFiberEndpointPost
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.ContractibleVertexIsoNaturality

/-!
概要：元の可縮な延長空間の指定比較は、全空間の後合成で値まで保持される。
方針：終点評価の厳密可換式と、像の可縮な延長空間の同型の一意性を合成する。
規約：元の比較の像を照合。使われ方：指定輸送比較の後合成自然性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {A D C E F B : SSet.{u}}
  (p : E ⟶ B) (q : F ⟶ B) [LeftFibration p] [LeftFibration q]
  (f : E ⟶ F) (hf : f ≫ q = p) (b : A ⟶ B) (i : D ⟶ A)
  (hi : leftAnodyneExtensions i) (v : D ⟶ E) (hv : v ≫ p = i ≫ b)
  (j : C ⟶ A) (z : B _⦋0⦌) (hj : j ≫ b = SSet.const z)
local notation "R" => relativeExtensionPost p q f hf b i v hv
local notation "hK" => relativeFunctorExtensionSpace_isContractibleKan p b i hi v hv
local notation "hL" => relativeFunctorExtensionSpace_isContractibleKan q b i hi (v ≫ f)
  (relativeExtensionPost_initial_base p q f hf b i v hv)
local notation "P" => relativeExtensionFiberEndpoint p b i v hv j z hj
local notation "Q" => relativeExtensionFiberEndpoint q b i (v ≫ f)
  (relativeExtensionPost_initial_base p q f hf b i v hv) j z hj
local notation "k" => CategoryTheory.Functor.map (ihom C) (vertexFiberMap p q f hf z)

/-- 同じ指定比較を終点の fiber 写像へ送った値は、像の延長の指定比較の値に等しい。 -/
lemma relativeExtensionFiberComparison_post
    (x y : (relativeFunctorExtensionSpace p b i v hv) _⦋0⦌) :
    HEq (VertexIso.map (VertexIso.map ((hK).vertexIso x y) P) k)
      (VertexIso.map ((hL).vertexIso ((R).app (Opposite.op ⦋0⦌) x)
        ((R).app (Opposite.op ⦋0⦌) y)) Q) := by
  have hr := relativeExtensionFiberEndpoint_post p q f hf b i v hv j z hj
  refine (heq_of_eq (vertexIso_map_comp ((hK).vertexIso x y) P k)).trans ?_
  refine (vertexIso_map_heq ((hK).vertexIso x y) hr.symm).trans ?_
  refine (heq_of_eq (vertexIso_map_comp ((hK).vertexIso x y) R Q)).symm.trans ?_
  exact heq_of_eq (congrArg (fun e => VertexIso.map e Q)
    (contractibleVertexIso_map hK hL R x y))

end SerrePositivity.InfinityCategories.F2
