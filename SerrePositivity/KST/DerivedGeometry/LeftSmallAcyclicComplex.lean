module

public import SerrePositivity.KST.DerivedGeometry.DescFromExtendedComplex
public import SerrePositivity.KST.DerivedGeometry.LeftRestrictionAcyclic
public import SerrePositivity.KST.DerivedGeometry.SmallAcyclicChainBounds
public import SerrePositivity.KST.DerivedGeometry.ExtendedAcyclicBounds
public import Mathlib.Algebra.Homology.Embedding.CochainComplex

/-!
概要：整数非輪状複体の左半分に、小さい非輪状部分複体を構成する。
方針：像の初期窓から小さい鎖複体を作り、境界の微分が零となることを示して零延長する。
規約：各項の統一した上界は生成対象だけに依存する。
使われ方：Stacks Lemma 19.12.2、TT §3・§8、Toën §3.2 の小さい試験族による判定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe w u
open CategoryTheory Limits
namespace SerrePositivity.KST.DerivedGeometry
variable {C : Type u} [Category.{w} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  (G : C) (hG : IsSeparator G) (M : CochainComplex C ℤ) (hM : M.Acyclic) (top : ℤ)
  (ψ : G ⟶ (M.restriction (ComplexShape.embeddingUpIntLE top)).X 1)

/--
概要：左制限に対して構成した小さい非輪状鎖複体。
方針：指定した射の初期像窓から完全な小さい先行項を順に加える。
規約：零次数の完全性は初期像微分の全射性から得る。
使われ方：Stacks 19.12.2、TT §3 の自然数方向の模型。
-/
def leftSmallAcyclicChain : ChainComplex C ℕ :=
  smallExactChainTail G hG (initialImageChainWindow (M.restriction
    (ComplexShape.embeddingUpIntLE top)) ψ) (leftRestriction_exactAt_succ M hM top)

/--
概要：左制限への小さい鎖複体の包含。
方針：構成した窓の包含を使う。
規約：零次数は指定した射の微分の像。
使われ方：Stacks 19.12.2、TT §3 の整数部分複体の包含の入力。
-/
def leftSmallAcyclicChainInclusion : leftSmallAcyclicChain G hG M hM top ψ ⟶
    M.restriction (ComplexShape.embeddingUpIntLE top) :=
  smallExactChainInclusion G hG (initialImageChainWindow (M.restriction
    (ComplexShape.embeddingUpIntLE top)) ψ) (leftRestriction_exactAt_succ M hM top)

/--
概要：小さい鎖複体の包含は、切断位置を越える微分で零になる。
方針：外へ出る微分がある次数は零次数だけであり、その項は既に微分の像。
規約：二乗零を使い、元の複体自体が上に有界とは仮定しない。
使われ方：Stacks 19.12.2、TT §3 の零延長から元の複体への包含。
-/
lemma leftSmallAcyclicChainInclusion_boundary (i : ℕ) (j : ℤ)
    (hj : ∀ n, (ComplexShape.embeddingUpIntLE top).f n ≠ j)
    (hij : (ComplexShape.up ℤ).Rel ((ComplexShape.embeddingUpIntLE top).f i) j) :
    (leftSmallAcyclicChainInclusion G hG M hM top ψ).f i ≫
      M.d ((ComplexShape.embeddingUpIntLE top).f i) j = 0 := by
  have hj' : top < j := (ComplexShape.notMem_range_embeddingUpIntLE_iff top j).mp hj
  have hi : i = 0 := by
    change top - (i : ℤ) + 1 = j at hij
    omega
  subst i
  apply (cancel_epi (factorThruImage (ψ ≫
    (M.restriction (ComplexShape.embeddingUpIntLE top)).d 1 0))).mp
  rw [comp_zero, ← Category.assoc]
  change (factorThruImage _ ≫ image.ι _) ≫ _ = 0
  rw [image.fac, Category.assoc]
  change ψ ≫ M.d _ _ ≫ M.d _ j = 0
  simp only [M.d_comp_d, comp_zero]

/--
概要：整数複体の左側に構成した小さい非輪状複体。
方針：構成した鎖複体を指定した上端まで零延長する。
規約：上端 top を越える項は零。
使われ方：Stacks 19.12.2、TT §3 の小さい整数次数試験族。
-/
def leftSmallAcyclicComplex : CochainComplex C ℤ :=
  (leftSmallAcyclicChain G hG M hM top ψ).extend (ComplexShape.embeddingUpIntLE top)

/--
概要：零延長した小さい複体から元の整数複体への包含。
方針：証明済みの境界零性を零延長の射の構成へ渡す。
規約：元の複体の圏の実際の鎖写像。
使われ方：Stacks 19.12.2、TT §3 の非輪状部分複体。
-/
def leftSmallAcyclicComplexInclusion : leftSmallAcyclicComplex G hG M hM top ψ ⟶ M :=
  descFromExtendedComplex (ComplexShape.embeddingUpIntLE top)
    (leftSmallAcyclicChainInclusion G hG M hM top ψ)
    (leftSmallAcyclicChainInclusion_boundary G hG M hM top ψ)

end SerrePositivity.KST.DerivedGeometry
