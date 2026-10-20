module

public import SerrePositivity.InfinityCategories.F2.PrismExtensionPullbackRestriction
public import SerrePositivity.InfinityCategories.F2.PrismExtensionComparisonRestriction

/-!
概要：引き戻しに表示した prism 終点の指定比較を、同じ比較の始域制限へ移す。
方針：終点の厳密な交換式と可縮延長空間の指定比較の自然性を合成する。
規約：指定頂点同型を保持。使われ方：元の三角形比較の各点への移送。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {A C E B K D : SSet.{u}} (p : E ⟶ B) [LeftFibration p]
  (d : ((Δ[1] : SSet.{u}) ⊗ A) ⊗ K ⟶ B) (v : A ⊗ K ⟶ E)
  (hv : v ≫ p = (prismEndpoint 0 A ▷ K) ≫ d) (s : C ⟶ A ⊗ K)
  (q : D ⟶ B) (a : A ⊗ K ⟶ D) (hj : (prismEndpoint 1 A ▷ K) ≫ d = a ≫ q)
local notation "i" => prismEndpoint 0 A ▷ K
local notation "r" => prismExtensionRestriction p d v hv s
local notation "e₁" => relativeFunctorExtensionEndpoint p d i v hv
  (prismEndpoint 1 A ▷ K) q a hj
local notation "e₂" => relativeFunctorExtensionEndpoint p (prismParameterRestriction s ≫ d)
  (prismEndpoint 0 C) (s ≫ v)
  (Eq.trans (Category.assoc s v p) (congrArg (fun f => s ≫ f) hv))
  (prismEndpoint 1 C) q (s ≫ a) (prismExtensionPullbackRestriction_endpoint d s q a hj)

/-- 底変換の逆まで含む指定終点比較は、制限後の同じ指定比較を与える。 -/
lemma prismExtensionPullbackComparison_restrict
    (x y : (relativeFunctorExtensionSpace p d i v hv) _⦋0⦌) :
    HEq
      (VertexIso.map
        (VertexIso.map
          ((relativeFunctorExtensionSpace_isContractibleKan p d i
            (leftAnodyneExtensions_whiskerRight _ (prismEndpoint_zero_leftAnodyne A) K)
            v hv).vertexIso x y) e₁)
        (relativeFunctorOverPre (pullback.snd p q)
          (Over.homMk (U := Over.mk (s ≫ a)) (V := Over.mk a) s rfl)))
      (VertexIso.map
        ((relativeFunctorExtensionSpace_isContractibleKan p (prismParameterRestriction s ≫ d)
          (prismEndpoint 0 C) (prismEndpoint_zero_leftAnodyne C) (s ≫ v)
          (by rw [Category.assoc, hv]; rfl)).vertexIso
            ((r).app (Opposite.op ⦋0⦌) x) ((r).app (Opposite.op ⦋0⦌) y)) e₂) := by
  let e := (relativeFunctorExtensionSpace_isContractibleKan p d i
    (leftAnodyneExtensions_whiskerRight _ (prismEndpoint_zero_leftAnodyne A) K)
    v hv).vertexIso x y
  have h := prismExtensionPullbackEndpoint_restrict p d v hv s q a hj
  have he := prismExtensionRestriction_vertexIso p d v hv s x y
  exact (heq_of_eq (vertexIso_map_comp e e₁
    (relativeFunctorOverPre (pullback.snd p q)
      (Over.homMk (U := Over.mk (s ≫ a)) (V := Over.mk a) s rfl)))).trans
      ((vertexIso_map_heq e h).trans
        ((heq_of_eq (vertexIso_map_comp e r e₂)).symm.trans
          (heq_of_eq (congrArg (fun z => VertexIso.map z e₂) he))))

end SerrePositivity.InfinityCategories.F2
