module
public import SerrePositivity.EInfinity.HomotopyWeight.BousfieldKanCellTensor

/-!
概要：BKの同じ自由テンソル細胞は境界生成族の左持ち上げ性を保つ。
方針：各終頂点で元の境界の持ち上げを取り、同じ生成元の降下射で全射へ束ねる。
規約：IS-W2 R03aの自由境界付着の証明分割。SSetモデルの追加仮定なし。
使われ方：BK骨格の各付着の射影cofibration性。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.HomotopyWeight
open CategoryTheory Limits Opposite SSet MonoidalCategory
open SerrePositivity.DiagramModel SerrePositivity.DiagramModel.BousfieldKanCells
open scoped Simplicial
variable (I : Type u) [SmallCategory I]

/-- 元の単体境界を全自由細胞へテンソルした射は、同じ自由境界の右類に左持ち上げ性。 -/
theorem bkCellTensor_map_llp (n : ℕ) {X Y : SSet.{u}} (f : X ⟶ Y)
    (hf : SSet.modelCategoryQuillen.I f) :
    (boundaries I).rlp.llp ((bkCellTensor I n).map f) := by
  intro H H' p hp
  constructor
  intro a b sq
  let sc (c : (nerve I).nonDegenerate n) :
      CommSq (bkCellGenerator I c X ≫ a.app (c.val.obj (Fin.last n))) f
        (p.app (c.val.obj (Fin.last n)))
        (bkCellGenerator I c Y ≫ b.app (c.val.obj (Fin.last n))) := by
    refine ⟨?_⟩
    have hc := NatTrans.congr_app sq.w (c.val.obj (Fin.last n))
    change a.app _ ≫ p.app _ = ((bkCellTensor I n).map f).app _ ≫ b.app _ at hc
    rw [Category.assoc, hc, ← Category.assoc, bkCellGenerator_naturality, Category.assoc]
  have hpc (c : (nerve I).nonDegenerate n) :
      HasLiftingProperty f (p.app (c.val.obj (Fin.last n))) :=
    ((boundaries_rlp I).le _ hp (c.val.obj (Fin.last n))) f hf
  let x (c : (nerve I).nonDegenerate n) : Y ⟶ H.obj (c.val.obj (Fin.last n)) := by
    letI := hpc c
    exact (sc c).lift
  let l := bkCellDesc I Y H x
  refine CommSq.HasLift.mk' { l := l, fac_left := ?_, fac_right := ?_ }
  · apply bkCellHom_ext I
    intro c
    change bkCellGenerator I c X ≫ ((bkCellTensor I n).map f).app _ ≫
      (bkCellDesc I Y H x).app _ = bkCellGenerator I c X ≫ a.app _
    rw [← Category.assoc, bkCellGenerator_naturality, Category.assoc, bkCellGenerator_desc]
    letI := hpc c
    exact (sc c).fac_left
  · apply bkCellHom_ext I
    intro c
    change bkCellGenerator I c Y ≫ (bkCellDesc I Y H x).app _ ≫ p.app _ =
      bkCellGenerator I c Y ≫ b.app _
    rw [← Category.assoc, bkCellGenerator_desc]
    letI := hpc c
    exact (sc c).fac_right

end SerrePositivity.EInfinity.HomotopyWeight
