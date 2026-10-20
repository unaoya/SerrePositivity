module

public import SerrePositivity.InfinityCategories.F2.PrismExtensionWitnessRestriction
public import SerrePositivity.InfinityCategories.F2.RelativeExtensionCurryPointComparison

/-!
概要：既存の prism の指定 curry 比較の各点成分を元の延長空間へ制限する。
方針：curry 成分の直接制限と、具体的終点比較の始域制限を合成する。
規約：元の二つの実 prism と指定同型を保持。使われ方：元の三角形比較の fiber 制限。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {A C E B K D : SSet.{u}} [Quasicategory K] (p : E ⟶ B) [LeftFibration p]
  (d : ((Δ[1] : SSet.{u}) ⊗ A) ⊗ K ⟶ B) (v : A ⊗ K ⟶ E)
  (hv : v ≫ p = (prismEndpoint 0 A ▷ K) ≫ d) (l : K _⦋0⦌) (s₀ : C ⟶ A)
  (q : D ⟶ B) (a₀ : A ⟶ D) (hj : (prismEndpoint 1 A ▷ K) ≫ d = (fst A K ≫ a₀) ≫ q)
  (W W' : (Δ[1] ⊗ A) ⊗ K ⟶ E) (hW : W ≫ p = d) (hW' : W' ≫ p = d)
  (hWi : (prismEndpoint 0 A ▷ K) ≫ W = v) (hWi' : (prismEndpoint 0 A ▷ K) ≫ W' = v)
  (g g' : A ⊗ K ⟶ pullback p q) (hg : g ≫ pullback.snd p q = fst A K ≫ a₀)
  (hg' : g' ≫ pullback.snd p q = fst A K ≫ a₀)
  (hWj : (prismEndpoint 1 A ▷ K) ≫ W = g ≫ pullback.fst p q)
  (hWj' : (prismEndpoint 1 A ▷ K) ≫ W' = g' ≫ pullback.fst p q)
local notation "s" => s₀ ≫ lift (𝟙 A) (SSet.const l)
local notation "i" => prismEndpoint 0 A ▷ K
local notation "hi" => leftAnodyneExtensions_whiskerRight _ (prismEndpoint_zero_leftAnodyne A) K
local notation "j" => prismEndpoint 1 A ▷ K
local notation "x" => relativeFunctorExtensionSpaceVertexEquiv p d i v hv
  (Subtype.mk W (And.intro hW hWi))
local notation "y" => relativeFunctorExtensionSpaceVertexEquiv p d i v hv
  (Subtype.mk W' (And.intro hW' hWi'))
local notation "r" => prismExtensionRestriction p d v hv s
local notation "e₂" => relativeFunctorExtensionEndpoint p (prismParameterRestriction s ≫ d)
  (prismEndpoint 0 C) (s ≫ v)
  (Eq.trans (Category.assoc s v p) (congrArg (fun f => s ≫ f) hv))
  (prismEndpoint 1 C) q (s ≫ (fst A K ≫ a₀))
  (prismExtensionPullbackRestriction_endpoint d s q (fst A K ≫ a₀) hj)

/-- 元の具体的 curry 比較の各点成分は同じ二延長の制限の指定比較となる。 -/
lemma prismExtensionCurryWitnessIso_restrict :
    HEq
      (VertexIso.map
        ((relativeFunctorExtensionEndpoint_curryIso p d i hi v hv j q a₀ hj
          W W' hW hW' hWi hWi' g g' hg hg' hWj hWj').app l)
        (relativeFunctorPre (pullback.snd p q) a₀ s₀))
      (VertexIso.map
        ((relativeFunctorExtensionSpace_isContractibleKan p (prismParameterRestriction s ≫ d)
          (prismEndpoint 0 C) (prismEndpoint_zero_leftAnodyne C) (s ≫ v)
          (by rw [Category.assoc, hv]; rfl)).vertexIso
            ((r).app (Opposite.op ⦋0⦌) x) ((r).app (Opposite.op ⦋0⦌) y)) e₂) := by
  have h := relativeExtensionEndpoint_curryIso_app_pre p d i hi v hv j q a₀ hj
    W W' hW hW' hWi hWi' g g' hg hg' hWj hWj' l s₀
  exact h.trans (prismExtensionWitnessIso_restrict p d v hv s q (fst A K ≫ a₀) hj
    W W' hW hW' hWi hWi' g g' hg hg' hWj hWj')

end SerrePositivity.InfinityCategories.F2
