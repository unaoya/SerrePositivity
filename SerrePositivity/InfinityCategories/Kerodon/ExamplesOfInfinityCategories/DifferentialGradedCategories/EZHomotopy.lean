module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.EZUniversalHomotopyChain

/-!
# AW→shuffle と恒等の標準鎖ホモトピー

概要：普遍模型で再帰的に充填した鎖を評価し、標準比較の実鎖ホモトピーを構成する。
方針：充填の境界公式を普遍作用素で評価して全次数のホモトピー等式を得る。
規約：KST Construction A.5、実 AW と実 shuffle を用い追加の比較仮定を置かない。
使われ方：正規化した差のテンソルの消滅を対角の低次ホモトピーへ移す。

対応節は Kerodon 2.5（Tag 00ND）。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open CategoryTheory Opposite AlgebraicTopology
open scoped Simplicial
variable (C D : SimplicialObject (ModuleCat.{u} ℤ))

/-- 概要：標準比較ホモトピーの一段次数を上げる実線形成分。
方針：普遍ホモトピー鎖を任意の二つの入力のテンソル作用素として評価する。
規約：KST A.5、任意の加群の宇宙で全次数に定義する。
使われ方：AW→shuffle と恒等の鎖ホモトピー。 -/
def ezHomotopyApp (n : ℕ) :
    ((alternatingFaceMapComplex _).obj (simplicialIntegerTensor C D)).X n ⟶
      ((alternatingFaceMapComplex _).obj (simplicialIntegerTensor C D)).X (n + 1) :=
  simplexPairOperation C D (op ⦋n + 1⦌) (ezUniversalHomotopyChain n)

/-- 概要：標準比較ホモトピーの零次の境界等式。
方針：普遍鎖の零次の境界を実作用素へ評価する。
規約：KST A.5、非被約な零次を含む。
使われ方：鎖ホモトピーの零次条件。 -/
lemma ezHomotopyApp_boundary_zero :
    ezHomotopyApp C D 0 ≫
      ((alternatingFaceMapComplex _).obj (simplicialIntegerTensor C D)).d 1 0 =
    𝟙 _ - alexanderWhitneyApp C D 0 ≫ shuffleApp C D 0 := by
  have he := congrArg (simplexPairOperation C D (op ⦋0⦌))
    ezUniversalHomotopyChain_boundary_zero
  rw [simplexPairOperation_boundary, simplexPairOperation_ezDifference] at he
  exact he

/-- 概要：標準比較ホモトピーの正次数の境界等式。
方針：普遍充填の境界を評価し、低次の面移送を対角微分へ移す。
規約：KST Construction A.5、全次数で実際の写像の等式。
使われ方：鎖ホモトピーの正次数条件。 -/
lemma ezHomotopyApp_boundary_succ (n : ℕ) :
    ezHomotopyApp C D (n + 1) ≫
        ((alternatingFaceMapComplex _).obj (simplicialIntegerTensor C D)).d (n + 2) (n + 1) +
      ((alternatingFaceMapComplex _).obj (simplicialIntegerTensor C D)).d (n + 1) n ≫
        ezHomotopyApp C D n =
    𝟙 _ - alexanderWhitneyApp C D (n + 1) ≫ shuffleApp C D (n + 1) := by
  have he := congrArg (simplexPairOperation C D (op ⦋n + 1⦌))
    (ezUniversalHomotopyChain_boundary_succ n)
  rw [simplexPairOperation_boundary, map_sub, simplexPairOperation_ezDifference,
    simplexPairOperation_faceSum] at he
  exact (eq_sub_iff_add_eq.mp he)

/-- 概要：恒等と実 AW→shuffle の間の標準鎖ホモトピー。
方針：普遍模型の収縮で構成した一段上の成分を Pi.single で全二次数へ拡張する。
規約：KST Construction A.5、引用による未証明の比較仮定を導入しない。
使われ方：Moore 正規化と単体的区間への復元に渡す実比較。 -/
def ezHomotopy : Homotopy (𝟙 _) (alexanderWhitney C D ≫ shuffle C D) where
  hom i := Pi.single (i + 1) (ezHomotopyApp C D i)
  zero i j hij := Pi.single_eq_of_ne (Ne.symm hij) _
  comm i := by
    cases i with
    | zero =>
      rw [Homotopy.prevD_chainComplex, Homotopy.dNext_zero_chainComplex]
      change 𝟙 _ = 0 + (ezHomotopyApp C D 0 ≫
        ((alternatingFaceMapComplex _).obj (simplicialIntegerTensor C D)).d 1 0) +
          (alexanderWhitney C D ≫ shuffle C D).f 0
      rw [zero_add]
      exact (eq_sub_iff_add_eq.mp (ezHomotopyApp_boundary_zero C D)).symm
    | succ n =>
      rw [Homotopy.prevD_chainComplex, Homotopy.dNext_succ_chainComplex]
      simp only [Pi.single_eq_same]
      change 𝟙 _ =
        ((alternatingFaceMapComplex _).obj (simplicialIntegerTensor C D)).d (n + 1) n ≫
            ezHomotopyApp C D n +
          ezHomotopyApp C D (n + 1) ≫
            ((alternatingFaceMapComplex _).obj (simplicialIntegerTensor C D)).d (n + 2) (n + 1) +
          (alexanderWhitney C D ≫ shuffle C D).f (n + 1)
      rw [add_comm (_ ≫ ezHomotopyApp C D n)]
      exact (eq_sub_iff_add_eq.mp (ezHomotopyApp_boundary_succ C D n)).symm

/-- 概要：標準比較ホモトピーの成分は両入力の射に自然。
方針：固定した普遍ホモトピー鎖に作用素の入力自然性を適用する。
規約：KST A.5、外部群の作用の射も含む。
使われ方：標準比較の外部 G 同変性。 -/
lemma ezHomotopyApp_naturality
    {C' D' : SimplicialObject (ModuleCat.{u} ℤ)} (f : C ⟶ C') (g : D ⟶ D') (n : ℕ) :
    integerTensorMap (f.app (op ⦋n⦌)) (g.app (op ⦋n⦌)) ≫ ezHomotopyApp C' D' n =
      ezHomotopyApp C D n ≫ integerTensorMap (f.app (op ⦋n + 1⦌)) (g.app (op ⦋n + 1⦌)) :=
  simplexPairOperation_map_naturality C D f g _ _

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
