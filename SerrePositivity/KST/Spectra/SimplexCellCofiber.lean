module

public import SerrePositivity.KST.Spectra.AdjoinCofiberCoproduct
public import SerrePositivity.KST.Spectra.SkeletalCellCofiber

/-!
概要：骨格のセルの cofiber を個々の単体の境界を潰した球面の余積で表示する。
方針：境界包含の余積への自由基点追加と cofiber の余積保存の同型を使う。
規約：sphere d は Δ[d] の境界を一点に潰す厳密な点つき模型。
使われ方：Goerss–Jardine VIII §1。塔の fiber のセルごとの Hom への分解。
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits SSet
open scoped Simplicial

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：標準 d 単体の境界を一点へ潰した点つき球面の模型。
方針：境界包含に自由基点を加えて cofiber を取る。
規約：d=0 も含む。Kan 置換はこの定義には施さない。
使われ方：Goerss–Jardine I §7、VIII §1。個々のセルの Hom の源。 -/
def SimplexCell.sphere (d : ℕ) : PointedSimplicialSet.{u} :=
  pointedCofiber (PointedObject.adjoinFunctor.map (∂Δ[d].ι : (∂Δ[d] : SSet.{u}) ⟶ Δ[d]))

namespace SkeletalCellAttachment

/-- 概要：セルの境界の余積の cofiber は球面の点つき余積と同型。
方針：自由基点を加えた射の余積と cofiber の同型を適用する。
規約：添字は通常の d 次元の非退化セルの型。
使われ方：Goerss–Jardine VIII §1。各セルの寄与への分解。 -/
def cellCoproductIso (K : SSet.{u}) (d : ℕ) :
    cellCofiber K d ≅ ∐ fun (_ : relativeCellComplexOfMono.Cell (K.skeleton d).ι d) ↦
      SimplexCell.sphere.{u} d :=
  adjoinCofiberCoproductIso
    (fun (_ : relativeCellComplexOfMono.Cell (K.skeleton d).ι d) ↦ (∂Δ[d] : SSet.{u}))
    (fun _ ↦ ∂Δ[d].ι)

end SkeletalCellAttachment

end

end SerrePositivity.KST.Spectra
