module

public import SerrePositivity.InfinityCategories.F2.Ind.FixedCoconeBoundary

/-!
概要：同じ底と終点を固定した全余錐の fiber を、標的の関手で移す。
方針：全内部 Hom の後合成の自然性で両固定条件を運ぶ。
規約：元の全余錐と全パラメーターを保持。使われ方：区間の宇宙同型の正規化。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {A X Y : SSet.{u}} (p : (Δ[0] : SSet.{u}) ⟶ X) (b : A ⟶ X)

/-- 同じ両固定境界の fiber から元の全関手空間への包含。 -/
def fixedCoconeBoundaryInclusion : fixedCoconeBoundary p b ⟶
    (ihom (join A (Δ[0] : SSet.{u}))).obj X :=
  vertexFiberι (coconeBoundaryPairRestriction A X) (functorVertex b, functorVertex p)

/-- 元の底図式の固定条件。 -/
lemma fixedCoconeBoundaryInclusion_old : fixedCoconeBoundaryInclusion p b ≫
    (pre (joinInl A (Δ[0] : SSet.{u}))).app X = SSet.const (functorVertex b) := by
  have h := congrArg (fun f ↦ f ≫ fst _ _) (vertexFiberι_comp
    (coconeBoundaryPairRestriction A X) (functorVertex b, functorVertex p))
  simp only [Category.assoc, coconeBoundaryPairRestriction, lift_fst, SSet.const_comp] at h
  exact h

/-- 元の指定終点の固定条件。 -/
lemma fixedCoconeBoundaryInclusion_tip : fixedCoconeBoundaryInclusion p b ≫
    (pre (joinInr A (Δ[0] : SSet.{u}))).app X = SSet.const (functorVertex p) := by
  have h := congrArg (fun f ↦ f ≫ snd _ _) (vertexFiberι_comp
    (coconeBoundaryPairRestriction A X) (functorVertex b, functorVertex p))
  simp only [Category.assoc, coconeBoundaryPairRestriction, lift_snd, SSet.const_comp] at h
  exact h

/-- 両固定境界を保った、同じ全余錐の後合成。 -/
def fixedCoconeBoundaryPost (h : X ⟶ Y) : fixedCoconeBoundary p b ⟶
    fixedCoconeBoundary (p ≫ h) (b ≫ h) :=
  vertexFiberLift _ _ (fixedCoconeBoundaryInclusion p b ≫
    (ihom (join A (Δ[0] : SSet.{u}))).map h) (by
      apply CartesianMonoidalCategory.hom_ext
      · simp only [Category.assoc, coconeBoundaryPairRestriction, lift_fst, SSet.const_comp]
        change fixedCoconeBoundaryInclusion p b ≫ (ihom (join A Δ[0])).map h ≫
          (pre (joinInl A Δ[0])).app Y = SSet.const (functorVertex (b ≫ h))
        rw [(pre (joinInl A (Δ[0] : SSet.{u}))).naturality h, ← Category.assoc,
          fixedCoconeBoundaryInclusion_old, SSet.const_comp]
        rfl
      · simp only [Category.assoc, coconeBoundaryPairRestriction, lift_snd, SSet.const_comp]
        change fixedCoconeBoundaryInclusion p b ≫ (ihom (join A Δ[0])).map h ≫
          (pre (joinInr A Δ[0])).app Y = SSet.const (functorVertex (p ≫ h))
        rw [(pre (joinInr A (Δ[0] : SSet.{u}))).naturality h, ← Category.assoc,
          fixedCoconeBoundaryInclusion_tip, SSet.const_comp]
        rfl)

/-- 元の余錐の頂点は、同じ全後合成の頂点へ送られる。 -/
lemma fixedCoconeBoundaryPost_vertex_val (h : X ⟶ Y)
    (v : (fixedCoconeBoundary p b) _⦋0⦌) (c : join A Δ[0] ⟶ X)
    (hv : v.val = functorVertex c) :
    ((fixedCoconeBoundaryPost p b h).app (Opposite.op ⦋0⦌) v).val =
      functorVertex (c ≫ h) := by
  change ((ihom (join A Δ[0])).map h).app _ v.val = _
  rw [hv]
  rfl

end SerrePositivity.InfinityCategories.F2.Ind
