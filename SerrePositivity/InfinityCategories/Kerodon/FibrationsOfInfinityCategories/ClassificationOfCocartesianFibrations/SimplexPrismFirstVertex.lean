module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftAnodynePushoutProduct
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.ScaffoldFirstVertex
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.PointFunctorEvaluation

/-!
概要：標準単体と任意のパラメーターの prism の最初の頂点からの包含。
方針：最初の頂点の left anodyne 性を直積へ移し、端点を定値族で計算する。
規約：零次元を含む任意の次元を扱う。
使われ方：Kerodon Corollary 5.6.5.15（Tag 0296）、coherent な変換の高次の族の相対持ち上げ。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：left anodyne な包含と任意の単体集合の直積は left anodyne。
方針：空の単体集合からの単射との pushout-product を使う。
規約：元の包含の単射性を別の仮定にはしない。
使われ方：Kerodon §4.2.5（Tag 0152）、相対持ち上げの任意のパラメーターへの拡張。 -/
lemma leftAnodyneExtensions_whiskerRight {K L : SSet.{u}}
    (i : K ⟶ L) (hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions i) (A : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions (i ▷ A) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions_pushoutObjObj_left i hi (initial.to A)
    (.ofIsInitialRight (curriedTensor _) i (initial.to A) initialIsInitial)

/-- 概要：標準単体の prism の最初の頂点からの包含は left anodyne。
方針：標準単体の最初の頂点の包含に直積の保存則を適用する。
規約：n=0 と空のパラメーター A も含む。
使われ方：Kerodon Corollary 5.6.5.15（Tag 0296）、最初の値を固定した高次の変換の持ち上げ。 -/
lemma simplexPrismFirstVertex_leftAnodyne (n : ℕ) (A : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.scaffoldFirstVertex.{u} n ▷ A) :=
  leftAnodyneExtensions_whiskerRight _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.scaffoldFirstVertex_leftAnodyne n) A

/-- 概要：単体の prism の指定した頂点への包含。
方針：指定頂点への定値射と恒等射を直積へ組み合わせる。
規約：n=1 の i=0、1 は既存の prismEndpoint と一致する表示。
使われ方：Kerodon Corollary 5.6.5.15（Tag 0296）、単体でパラメーター付けられた変換の値。 -/
def simplexPrismVertex (n : ℕ) (i : Fin (n + 1)) (A : SSet.{u}) :
    A ⟶ (Δ[n] : SSet.{u}) ⊗ A :=
  lift (SSet.const (stdSimplex.obj₀Equiv.symm i)) (𝟙 A)

/-- 概要：単体の prism の指定頂点をパラメーターへ射影すると恒等射。
方針：直積への組み合わせの第二射影を取る。
規約：次元と頂点は任意。
使われ方：Kerodon Corollary 5.6.5.15（Tag 0296）、固定する元の全空間の回収。 -/
lemma simplexPrismVertex_snd (n : ℕ) (i : Fin (n + 1)) (A : SSet.{u}) :
    simplexPrismVertex n i A ≫ snd (Δ[n] : SSet.{u}) A = 𝟙 A :=
  lift_snd _ _

/-- 概要：単体の prism の頂点包含はパラメーターの射に自然。
方針：直積の二成分で定値射と恒等射を計算する。
規約：次元と頂点を固定する。
使われ方：Kerodon Corollary 5.6.5.15（Tag 0296）、持ち上げの底の図式の頂点での計算。 -/
lemma simplexPrismVertex_naturality (n : ℕ) (i : Fin (n + 1))
    {A B : SSet.{u}} (f : A ⟶ B) :
    simplexPrismVertex n i A ≫ (Δ[n] ◁ f) = f ≫ simplexPrismVertex n i B := rfl

/-- 概要：零単体から最初の頂点への包含とパラメーターの積は、最初の頂点への包含を経由する。
方針：各次数で零単体の成分が一意であることを使う。
規約：左辺の定義域は Δ⁰ ⊗ A。
使われ方：Kerodon Corollary 5.6.5.15（Tag 0296）、具体的な始点条件と相対制限の接続。 -/
lemma scaffoldFirstVertex_whiskerRight (n : ℕ) (A : SSet.{u}) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.scaffoldFirstVertex.{u} n ▷ A) =
      snd (Δ[0] : SSet.{u}) A ≫ simplexPrismVertex n 0 A := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  rintro ⟨s, a⟩
  apply Prod.ext
  · apply stdSimplex.ext
    intro i
    apply Fin.ext
    rfl
  · rfl

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
