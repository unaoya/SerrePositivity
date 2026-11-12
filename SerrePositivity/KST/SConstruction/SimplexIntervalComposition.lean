module
public import SerrePositivity.KST.SConstruction.SimplexIntervalCubicalMapping
public import SerrePositivity.KST.SConstruction.NecklaceCubicalComposition

/-! # 元の標準単体の区間 Hom 比較と合成
概要：元の二区間の Hom 合成を、共有端点で貼った bead の元の cube 射で回収する。
方針：像区間 bead への元の終対象射と、元の全生成射上の合成の式を使う。
規約：一点区間も同じ合成に含む。使われ方：native HA 方程式の分割合成項。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Simplicial SSet

/-- 元の二区間 bead の連結を、同じ全区間 bead へ送る実 necklace 射。 -/
def simplexIntervalComposeBeadHom {n : ℕ} (a b c : Fin (n + 1))
    (hab : a ≤ b) (hbc : b ≤ c) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedge (necklaceBead.{u} (b.val - a.val)) (necklaceBead (c.val - b.val)) ⟶
      necklaceBead (c.val - a.val) :=
  (necklaceInToSimplexInterval a c (hab.trans hbc)
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedge (necklaceInSimplexInterval a b hab)
      (necklaceInSimplexInterval b c hbc))).necklaceHom

/-- 元の連結の cube 射の元になる necklace 射は、同じ augmentation の可換三角形。 -/
lemma simplexIntervalComposeBeadHom_triangle {n : ℕ} (a b c : Fin (n + 1))
    (hab : a ≤ b) (hbc : b ≤ c) :
    (simplexIntervalComposeBeadHom.{u} a b c hab hbc).map ≫
        (necklaceInSimplexInterval a c (hab.trans hbc)).map =
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedge (necklaceInSimplexInterval a b hab)
        (necklaceInSimplexInterval b c hbc)).map :=
  (necklaceInToSimplexInterval a c (hab.trans hbc)
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedge (necklaceInSimplexInterval a b hab)
      (necklaceInSimplexInterval b c hbc))).w

/-- 元の区間 Hom 比較は、元の Day 合成を連結から全区間への同じ実 cube 射で回収する。 -/
lemma simplexIntervalCubicalCoreIso_comp {n : ℕ} (a b c : Fin (n + 1))
    (hab : a ≤ b) (hbc : b ≤ c) :
    cubicalDayTensorMap (simplexIntervalCubicalCoreIso.{u} a b hab).hom
        (simplexIntervalCubicalCoreIso b c hbc).hom ≫
      necklaceCubicalCompose (Δ[n] : SSet.{u})
        (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex b) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex c) =
    (necklaceCubicalTensorIso (necklaceBead (b.val - a.val))
      (necklaceBead (c.val - b.val))).hom ≫
        necklaceCubicalSet.map (simplexIntervalComposeBeadHom.{u} a b c hab hbc) ≫
          (simplexIntervalCubicalCoreIso a c (hab.trans hbc)).hom := by
  have h := simplexIntervalCubicalCoreIso_cell a c (hab.trans hbc)
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedge (necklaceInSimplexInterval a b hab) (necklaceInSimplexInterval b c hbc))
  exact (necklaceCubicalCompose_cell (Δ[n] : SSet.{u})
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex b) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex c)
    (necklaceInSimplexInterval a b hab) (necklaceInSimplexInterval b c hbc)).trans
      (congrArg (fun f => (necklaceCubicalTensorIso
        (necklaceBead (b.val - a.val)) (necklaceBead (c.val - b.val))).hom ≫ f) h.symm)

end SerrePositivity.KST.SConstruction
