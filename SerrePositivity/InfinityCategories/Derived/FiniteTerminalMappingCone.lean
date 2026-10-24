module
public import SerrePositivity.InfinityCategories.Derived.FiniteMappingCylinder
public import SerrePositivity.InfinityCategories.F1B.Cofinality.InitialTerminalWeakContractibility

/-! # 終対象への有限写像錐

概要：任意の図式を終対象の方向へ収縮し、写像円柱型の錐全体へ延長する。
方針：定値終対象関手の終対象性から実ホモトピーを取り、終端を一点へ貼る。
規約：始点の指定図式を厳密に保持する。使われ方：有限対充填による slice 引き戻しの収縮。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial

/-- 一点への定値射は有限写像錐の貼り合わせ射になる。 -/
def finiteConeMap (K : SSet.{u}) : K ⟶ (Δ[0] : SSet.{u}) :=
  SSet.const (stdSimplex.obj₀Equiv.symm 0)

/-- 任意の図式は終対象の方向の写像錐へ延長できる。 -/
lemma IsTerminalVertex.finiteCone_extension {X : SSet.{u}} {x : X _⦋0⦌}
    (hx : IsTerminalVertex x) {K : SSet.{u}} (b : K ⟶ X) :
    ∃ G : finiteMappingCylinder (finiteConeMap K) ⟶ X,
      finiteMappingCylinderSource (finiteConeMap K) ≫ G = b := by
  have ht : IsTerminalVertex (functorVertex (SSet.const x : K ⟶ X)) :=
    isTerminalVertex_functorVertex_of_pointwise _ (fun _ => by
      change IsTerminalVertex (PinchedHom.constant x 0)
      rw [pinchedConstant_zero]
      exact hx)
  obtain ⟨e⟩ := ht.nonempty_edge (functorVertex b)
  let H := simplicialHomotopyOfFunctorEdge e
  let G : finiteMappingCylinder (finiteConeMap K) ⟶ X :=
    pushout.desc ((β_ (Δ[1] : SSet.{u}) K).hom ≫ H.h) (SSet.const x) (by
      rw [← Category.assoc, prismEndpoint_one_braiding, H.h₁, SSet.comp_const])
  refine ⟨G, ?_⟩
  change (prismEndpoint 0 K ≫ pushout.inl _ _) ≫ G = b
  rw [Category.assoc, pushout.inl_desc, ← Category.assoc, prismEndpoint_zero_braiding]
  exact H.h₀

end SerrePositivity.InfinityCategories
