module
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.SquareHomotopyCategory

/-! # 零角の列のホモトピー圏への関手性

概要：四角形間の自然変換は、零角の列から得た短複体の間の射を与える。
方針：三つの角における自然変換の成分を取り、二辺の自然性を使う。
規約：四角形のホモトピー圏上の自然変換を入力とし、安定性を仮定しない。
使われ方：S4 の cofiber 三角形の射と図式の族の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：零角の二つの四角形の自然変換から短複体の射を得る。
方針：左下、右下、右上の成分を取り、下辺と右辺の自然性を用いる。
規約：二つの端の四角形に零角があればよい。
使われ方：fiber/cofiber 列の射の h C への移送。 -/
def ZeroTriangle.hoShortComplexMap {X : SSet.{u}} [Quasicategory X]
    [HasZeroMorphisms (hoFunctor.obj X)] (t d : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X)
    (α : (hoFunctor.map t.square).toFunctor ⟶ (hoFunctor.map d.square).toFunctor) :
    t.hoShortComplex ⟶ d.hoShortComplex where
  τ₁ := α.app (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoVertex (𝟙 ((Δ[1] : SSet.{u}) ⊗ Δ[1])) 0 0)
  τ₂ := α.app (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoVertex (𝟙 ((Δ[1] : SSet.{u}) ⊗ Δ[1])) 1 0)
  τ₃ := α.app (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoVertex (𝟙 ((Δ[1] : SSet.{u}) ⊗ Δ[1])) 1 1)
  comm₁₂ := (α.naturality (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoBottom (𝟙 ((Δ[1] : SSet.{u}) ⊗ Δ[1])))).symm
  comm₂₃ := (α.naturality (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoRight (𝟙 ((Δ[1] : SSet.{u}) ⊗ Δ[1])))).symm

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle export _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroTriangle (hoShortComplexMap)


/-- 概要：恒等自然変換は短複体の恒等射を与える。
方針：三成分を計算する。規約：同じ四角形。
使われ方：短複体への関手性の単位。 -/
lemma ZeroTriangle.hoShortComplexMap_id {X : SSet.{u}} [Quasicategory X]
    [HasZeroMorphisms (hoFunctor.obj X)] (t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X) :
    t.hoShortComplexMap t (𝟙 (hoFunctor.map t.square).toFunctor) = 𝟙 t.hoShortComplex := by
  ext <;> rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle export _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroTriangle (hoShortComplexMap_id)


/-- 概要：自然変換の合成は短複体の射の合成に写る。
方針：三成分の合成を計算する。規約：合成は左から右。
使われ方：短複体への関手性の合成則。 -/
lemma ZeroTriangle.hoShortComplexMap_comp {X : SSet.{u}} [Quasicategory X]
    [HasZeroMorphisms (hoFunctor.obj X)] (t d e : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X)
    (α : (hoFunctor.map t.square).toFunctor ⟶ (hoFunctor.map d.square).toFunctor)
    (β : (hoFunctor.map d.square).toFunctor ⟶ (hoFunctor.map e.square).toFunctor) :
    t.hoShortComplexMap e (α ≫ β) = t.hoShortComplexMap d α ≫ d.hoShortComplexMap e β := by
  ext <;> rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle export _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroTriangle (hoShortComplexMap_comp)


/-- 概要：四角形の間の単体的ホモトピーは零角の短複体の射を与える。
方針：ホモトピーの二端から h C の自然変換を構成して適用する。
規約：中間パラメーターでの零角条件は不要。
使われ方：実際の四角形の族から cofiber 列の射を作る。 -/
def ZeroTriangle.hoShortComplexMapOfHomotopy {X : SSet.{u}} [Quasicategory X]
    [HasZeroMorphisms (hoFunctor.obj X)] (t d : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X)
    (H : ((Δ[1] : SSet.{u}) ⊗ Δ[1]) ⊗ Δ[1] ⟶ X)
    (h₀ : SSet.ι₀ ≫ H = t.square) (h₁ : SSet.ι₁ ≫ H = d.square) :
    t.hoShortComplex ⟶ d.hoShortComplex :=
  t.hoShortComplexMap d (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyNatTransOfEndpoints H h₀ h₁)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle export _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroTriangle (hoShortComplexMapOfHomotopy)


end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
