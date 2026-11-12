module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativeExtensionWitnessComparison
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.RelativeFunctorCurryIsoPresentation
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PrismExtensionPullbackComparisonRestriction

/-!
概要：既存の具体的 prism 終点比較を元の二延長を保って始域へ制限する。
方針：具体的終点表示の比較を外し、同じ延長空間の指定同型の制限等式を使う。
規約：元の二つの実 prism と指定同型を保持。使われ方：元の三角形比較の fiber 制限。
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
  (W W' : (Δ[1] ⊗ A) ⊗ K ⟶ E) (hW : W ≫ p = d) (hW' : W' ≫ p = d)
  (hWi : (prismEndpoint 0 A ▷ K) ≫ W = v) (hWi' : (prismEndpoint 0 A ▷ K) ≫ W' = v)
  (g g' : A ⊗ K ⟶ pullback p q) (hg : g ≫ pullback.snd p q = a)
  (hg' : g' ≫ pullback.snd p q = a)
  (hWj : (prismEndpoint 1 A ▷ K) ≫ W = g ≫ pullback.fst p q)
  (hWj' : (prismEndpoint 1 A ▷ K) ≫ W' = g' ≫ pullback.fst p q)
local notation "i" => prismEndpoint 0 A ▷ K
local notation "hi" => leftAnodyneExtensions_whiskerRight _ (prismEndpoint_zero_leftAnodyne A) K
local notation "j" => prismEndpoint 1 A ▷ K
local notation "x" => relativeFunctorExtensionSpaceVertexEquiv p d i v hv
  (Subtype.mk W (And.intro hW hWi))
local notation "y" => relativeFunctorExtensionSpaceVertexEquiv p d i v hv
  (Subtype.mk W' (And.intro hW' hWi'))
local notation "r" => prismExtensionRestriction p d v hv s
local notation "e₁" => relativeFunctorExtensionEndpoint p d i v hv j q a hj
local notation "η" => relativeFunctorExtensionEndpoint_witnessIso p d i hi v hv j q a hj
  W W' hW hW' hWi hWi' g g' hg hg' hWj hWj'
local notation "e₂" => relativeFunctorExtensionEndpoint p (prismParameterRestriction s ≫ d)
  (prismEndpoint 0 C) (s ≫ v)
  (Eq.trans (Category.assoc s v p) (congrArg (fun f => s ≫ f) hv))
  (prismEndpoint 1 C) q (s ≫ a) (prismExtensionPullbackRestriction_endpoint d s q a hj)

/-- 既存の具体的終点比較を制限しても元の二 prism の制限の同じ指定比較になる。 -/
lemma prismExtensionWitnessIso_restrict :
    HEq (VertexIso.map η
      (relativeFunctorOverPre (pullback.snd p q)
        (Over.homMk (U := Over.mk (s ≫ a)) (V := Over.mk a) s rfl)))
      (VertexIso.map
        ((relativeFunctorExtensionSpace_isContractibleKan p (prismParameterRestriction s ≫ d)
          (prismEndpoint 0 C) (prismEndpoint_zero_leftAnodyne C) (s ≫ v)
          (by rw [Category.assoc, hv]; rfl)).vertexIso
            ((r).app (Opposite.op ⦋0⦌) x) ((r).app (Opposite.op ⦋0⦌) y)) e₂) := by
  let e := VertexIso.map
    ((relativeFunctorExtensionSpace_isContractibleKan p d i hi v hv).vertexIso x y) e₁
  have he := relativeExtensionEndpoint_witnessIso_heq_map p d i hi v hv j q a hj
    W W' hW hW' hWi hWi' g g' hg hg' hWj hWj'
  have hs := relativeFunctorExtensionEndpoint_vertex p d i v hv j q a hj W hW hWi g hg hWj
  have ht := relativeFunctorExtensionEndpoint_vertex p d i v hv j q a hj W' hW' hWi' g' hg' hWj'
  have hm := vertexIso_map_heq_of_heq η e hs.symm ht.symm he
    (relativeFunctorOverPre (pullback.snd p q)
      (Over.homMk (U := Over.mk (s ≫ a)) (V := Over.mk a) s rfl))
  exact hm.trans (prismExtensionPullbackComparison_restrict p d v hv s q a hj x y)

end SerrePositivity.InfinityCategories.F2
