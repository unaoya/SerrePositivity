module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.FibrantModels.DGSuspensionCoherentActionInput
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Triangles.DGSuspensionNativeSquareModel

/-!
概要：同じ実核・cone・零角・懸垂の全四角形族の採用入力。
方針：作用の辺比較だけを緩め、各対象の全四角形と懸垂角は厳密に保持する。
規約：模型・I・P・固定 S・ν・K は変更しない。この型の無条件存在は未供給。
使われ方：D-8 e の供給と K-B3 の比較付き反復アダプタ。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.KST.SConstruction SerrePositivity.KST.NonConnective
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
variable (R : Type u) [CommRing R] {κ : Cardinal.{u}}
  (s : DGSuspensionStageProvider.{u, v} R κ)

/-- 採用 B1 の全四角形。各対象の元の全四角形と懸垂角の厳密一致を保持する。 -/
structure DGSuspensionCoherentSquareInput where
  action : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGSuspensionCoherentActionInput R s
  square : ((Δ[1] ⊗ Δ[1]) ⊗ dgKInputInfinity.{u, max (u + 1) v} R) ⟶
    dgKInputInfinity.{u, max (u + 1) v} R
  square_at : ∀ A : PerfDGInput.{u, max (u + 1) v} R,
    dgSuspensionNativeSquareAt R square A = dgKappaResolvedConnectiveSquare R A (s A).cone
  suspension : dgSuspensionNativeSquareCornerFamily R square 1 1 = action.map

/-- 既存の厳密四角形供給から、同じ全四角形を保持して採用入力へ送る。 -/
def DGSuspensionCoherentSquareInput.ofStrict (m : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGSuspensionNativeSquareModel R s) :
    DGSuspensionCoherentSquareInput R s where
  action := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGSuspensionCoherentActionInput.ofStrict R s m.action
  square := m.square
  square_at := m.square_at
  suspension := m.suspension

end SerrePositivity.InfinityCategories.Project.DerivedCategories
