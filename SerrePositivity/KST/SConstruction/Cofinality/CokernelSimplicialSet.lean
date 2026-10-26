module
public import SerrePositivity.KST.SConstruction.Cofinality.CokernelNerveSimplex

/-!
概要：元の指定射の K₀ 余核の S 方向を単体集合に束ねる。
方針：元の全端点制限とその厳密な関手則を使う。
規約：次数ごとの同型だけで単体的な比較を主張しない。
使われ方：元の障害図式と群 nerve の単体的な同定。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction.Cofinality
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：元の指定射の S_n K₀ 余核の単体集合。
方針：面・退化を含む全端点制限を関手に束ねる。
規約：元の射の K₀ 像による余核を各段で使う。
使われ方：障害図式の bar 比較の始域。 -/
def cutCokernelSimplicialSet {X Y : StableModel.{u}} (f : X ⟶ Y) : SSet.{u} where
  obj n := cutKZeroCokernel n.unop.len f
  map α := ↾(cutCokernelRestriction f α.unop.toOrderHom)
  map_id n := by
    apply ConcreteCategory.hom_ext
    intro a
    exact DFunLike.congr_fun (cutCokernelRestriction_id n.unop.len f) a
  map_comp α β := by
    apply ConcreteCategory.hom_ext
    intro a
    exact DFunLike.congr_fun
      (cutCokernelRestriction_comp f β.unop.toOrderHom α.unop.toOrderHom) a

/-- 概要：区間の端点制限は元の全単体作用素と可換。
方針：二端点の順序写像の合成を各端点で計算する。
規約：面・退化以外の任意の単体作用素も許す。
使われ方：群 nerve 比較の全単体的自然性。 -/
lemma cokernelIntervalOrder_comp {m n : ℕ} (θ : Fin (m + 1) →o Fin (n + 1))
    (i j : Fin (m + 1)) (hij : i ≤ j) :
    θ.comp (cokernelIntervalOrder i j hij) =
      cokernelIntervalOrder (θ i) (θ j) (θ.monotone hij) := by
  apply DFunLike.ext
  intro b
  fin_cases b <;> rfl

end SerrePositivity.KST.SConstruction.Cofinality
