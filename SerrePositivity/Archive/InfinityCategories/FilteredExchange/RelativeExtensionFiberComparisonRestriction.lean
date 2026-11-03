module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativeExtensionFiberEndpointRestriction
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.ContractibleVertexIsoNaturality

/-!
概要：元の可縮な全延長空間の指定比較は、同じ実終点を保つ制限で値まで保持される。
方針：全終点の厳密な自然性と制限先の指定同型の一意性を合成する。
規約：元の二延長・指定比較を保持。使われ方：prism の二つの表示の比較を照合する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
/-- 制限した元の初期値は、同じ制限した底を厳密に被覆する。 -/
lemma relativeExtensionRestriction_initial_base {A D A' D' E B : SSet.{u}}
    (p : E ⟶ B) (b : A ⟶ B) (i : D ⟶ A) (v : D ⟶ E)
    (hv : v ≫ p = i ≫ b) (h : A' ⟶ A) (k : D' ⟶ D) (i' : D' ⟶ A')
    (hs : i' ≫ h = k ≫ i) : (k ≫ v) ≫ p = i' ≫ h ≫ b := by
  rw [Category.assoc, hv, ← Category.assoc, ← hs, Category.assoc]

/-- 同じ実終点の正方形から、制限後の底も同じ一点であることを回収する。 -/
lemma relativeExtensionRestriction_endpoint_base {A A' C B : SSet.{u}}
    (b : A ⟶ B) (h : A' ⟶ A) (j : C ⟶ A) (j' : C ⟶ A') (hsj : j' ≫ h = j)
    (z : B _⦋0⦌) (hj : j ≫ b = SSet.const z) : j' ≫ h ≫ b = SSet.const z := by
  rw [← Category.assoc, hsj, hj]

variable {A D A' D' C E B : SSet.{u}}
  (p : E ⟶ B) [LeftFibration p] (b : A ⟶ B) (i : D ⟶ A) (hi : leftAnodyneExtensions i)
  (v : D ⟶ E) (hv : v ≫ p = i ≫ b) (h : A' ⟶ A) (k : D' ⟶ D)
  (i' : D' ⟶ A') (hi' : leftAnodyneExtensions i') (hs : i' ≫ h = k ≫ i)
  (j : C ⟶ A) (j' : C ⟶ A') (hsj : j' ≫ h = j)
  (z : B _⦋0⦌) (hj : j ≫ b = SSet.const z)
local notation "R" => relativeExtensionRestriction p b i v hv h k i' hs
local notation "hK" => relativeFunctorExtensionSpace_isContractibleKan p b i hi v hv
local notation "hK'" => relativeFunctorExtensionSpace_isContractibleKan p (h ≫ b) i' hi' (k ≫ v)
  (relativeExtensionRestriction_initial_base p b i v hv h k i' hs)
local notation "Q" => relativeExtensionFiberEndpoint p (h ≫ b) i' (k ≫ v)
  (relativeExtensionRestriction_initial_base p b i v hv h k i' hs) j' z
  (relativeExtensionRestriction_endpoint_base b h j j' hsj z hj)

/-- 元の二延長の指定比較の終点像は、制限先の同じ指定比較の終点像と値まで一致。 -/
lemma relativeExtensionFiberComparison_restriction
    (x y : (relativeFunctorExtensionSpace p b i v hv) _⦋0⦌) :
    HEq (VertexIso.map ((hK).vertexIso x y) (relativeExtensionFiberEndpoint p b i v hv j z hj))
      (VertexIso.map ((hK').vertexIso ((R).app (Opposite.op ⦋0⦌) x)
        ((R).app (Opposite.op ⦋0⦌) y)) Q) := by
  have hr := relativeExtensionFiberEndpoint_restriction p b i v hv h k i' hs j j' hsj z hj
  refine (vertexIso_map_heq ((hK).vertexIso x y) hr.symm).trans ?_
  refine (heq_of_eq (vertexIso_map_comp ((hK).vertexIso x y) R Q)).symm.trans ?_
  exact heq_of_eq (congrArg (fun e => VertexIso.map e Q)
    (contractibleVertexIso_map hK hK' R x y))

end SerrePositivity.InfinityCategories.F2
