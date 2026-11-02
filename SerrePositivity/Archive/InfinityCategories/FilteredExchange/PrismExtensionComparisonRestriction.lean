module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PrismExtensionEndpointRestriction

/-!
概要：全 prism の元の指定比較と各点の指定比較は終点の相対写像空間で一致する。
方針：終点評価の可換性と可縮な延長空間の指定同型の自然性を合成する。
規約：同型の存在でなく指定値の等式。使われ方：全空間と各点の可換 path 類の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {A C E B K : SSet.{u}} (p : E ⟶ B) [LeftFibration p]
  (b : ((Δ[1] : SSet.{u}) ⊗ A) ⊗ K ⟶ B) (v : A ⊗ K ⟶ E)
  (hv : v ≫ p = (prismEndpoint 0 A ▷ K) ≫ b) (s : C ⟶ A ⊗ K)
local notation "i" => prismEndpoint 0 A ▷ K
local notation "h" => prismParameterRestriction s

set_option maxHeartbeats 800000 in
-- 二重の相対 fiber とホモトピー圏の指定同型の端点の型照合に必要。
/-- 概要：元の二つの延長の終点の指定比較は制限後の同じ比較と厳密に一致する。
方針：全延長空間の制限と終点評価を交換し、可縮性で同型の値を同定する。
規約：元の二延長の頂点を固定。使われ方：各点の元の錐への指定 path の移送。 -/
lemma prismExtensionComparison_restrict
    (x y : (relativeFunctorExtensionSpace p b i v hv) _⦋0⦌) :
    VertexIso.map
      (VertexIso.map
        ((relativeFunctorExtensionSpace_isContractibleKan p b i
          (leftAnodyneExtensions_whiskerRight _ (prismEndpoint_zero_leftAnodyne A) K)
          v hv).vertexIso x y)
        (prismExtensionEndpoint p b v hv))
      (relativeFunctorPre p ((prismEndpoint 1 A ▷ K) ≫ b) s) =
        VertexIso.map
          ((relativeFunctorExtensionSpace_isContractibleKan p (h ≫ b) (prismEndpoint 0 C)
            (prismEndpoint_zero_leftAnodyne C) (s ≫ v)
            (by rw [Category.assoc, hv]; rfl)).vertexIso
              ((prismExtensionRestriction p b v hv s).app (Opposite.op ⦋0⦌) x)
              ((prismExtensionRestriction p b v hv s).app (Opposite.op ⦋0⦌) y))
          (relativeFunctorExtensionSpaceι p (h ≫ b) (prismEndpoint 0 C) (s ≫ v)
            (by rw [Category.assoc, hv]; rfl) ≫
              relativeFunctorPre p (h ≫ b) (prismEndpoint 1 C)) := by
  let e := (relativeFunctorExtensionSpace_isContractibleKan p b i
    (leftAnodyneExtensions_whiskerRight _ (prismEndpoint_zero_leftAnodyne A) K) v hv).vertexIso x y
  let r := prismExtensionRestriction p b v hv s
  let q := relativeFunctorExtensionSpaceι p (h ≫ b) (prismEndpoint 0 C) (s ≫ v)
    (by rw [Category.assoc, hv]; rfl) ≫
      relativeFunctorPre p (h ≫ b) (prismEndpoint 1 C)
  have he := prismExtensionRestriction_vertexIso p b v hv s x y
  have hq := congrArg (fun z : VertexIso (r.app (Opposite.op ⦋0⦌) x)
    (r.app (Opposite.op ⦋0⦌) y) => VertexIso.map z q) he
  exact eq_of_heq ((heq_of_eq (vertexIso_map_comp e (prismExtensionEndpoint p b v hv)
    (relativeFunctorPre p ((prismEndpoint 1 A ▷ K) ≫ b) s))).trans
      ((vertexIso_map_heq e (prismExtensionEndpoint_restrict p b v hv s)).trans
        ((heq_of_eq (vertexIso_map_comp e r q)).symm.trans (heq_of_eq hq))))

end SerrePositivity.InfinityCategories.F2
