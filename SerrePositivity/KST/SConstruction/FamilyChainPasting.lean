module
public import SerrePositivity.KST.SConstruction.CylinderCellWalks

/-! # 全補正円柱を実 pushout で貼った有限複体
概要：実ホモトピー有限列を、全セルと共有面・両端を保持する一つの複体にする。
方針：各元の円柱の出口を次の複体の入口へ pushout で貼る。
規約：元の全円柱と順序を保持し、空列では元のパラメータ自体を使う。
使われ方：元の三角形と二次元補正全体の貼り合わせ。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory CategoryTheory.Limits MonoidalCategory SSet
open scoped Simplicial

/-- 元の有限列の全セルを同時に保持する貼り合わせ複体と実写像。 -/
structure FamilyChainPastingData {U E : SSet.{u}} {f g : U ⟶ E}
    (c : FamilyHomotopyChain f g) where
  /-- 元の全円柱を貼った実複体。 -/
  domain : SSet.{u}
  /-- 元の始点族の入口。 -/
  source : U ⟶ domain
  /-- 元の終点族の出口。 -/
  target : U ⟶ domain
  /-- 各元の円柱全体の包含を順に保存する。 -/
  cells : List (U ⊗ (Δ[1] : SSet.{u}) ⟶ domain)
  /-- 同じ複体内の厳密な共有面と両端。 -/
  walk : CylinderCellWalk source target cells
  /-- 全複体から元の値域への実写像。 -/
  map : domain ⟶ E
  /-- 元の始点族の厳密な回収。 -/
  source_eq : source ≫ map = f
  /-- 元の終点族の厳密な回収。 -/
  target_eq : target ≫ map = g
  /-- 元の全円柱と順序を厳密に回収する。 -/
  cells_eq : cells.map (· ≫ map) = familyHomotopyChainTrace c

/-- 元の有限列を、全セルと共有面を保って一つの実複体へ貼る。 -/
def familyChainPasting {U E : SSet.{u}} {f g : U ⟶ E} (c : FamilyHomotopyChain f g) :
    FamilyChainPastingData c := by
  induction c with
  | nil f => exact ⟨U, 𝟙 U, 𝟙 U, [], .nil _, f, Category.id_comp _, Category.id_comp _, rfl⟩
  | @cons f g h H tail T =>
      let d := pushout (SSet.ι₁ (X := U)) T.source
      let a : U ⊗ (Δ[1] : SSet.{u}) ⟶ d := pushout.inl _ _
      let b : T.domain ⟶ d := pushout.inr _ _
      let hd : SSet.ι₁ ≫ H.h = T.source ≫ T.map := H.h₁.trans T.source_eq.symm
      let q : d ⟶ E := pushout.desc H.h T.map hd
      refine {
        domain := d
        source := SSet.ι₀ ≫ a
        target := T.target ≫ b
        cells := a :: T.cells.map (· ≫ b)
        walk := .cons a rfl ?_ (cylinderCellWalkMap T.walk b)
        map := q
        source_eq := ?_
        target_eq := ?_
        cells_eq := ?_ }
      · exact pushout.condition
      · change (SSet.ι₀ ≫ pushout.inl _ _) ≫ pushout.desc H.h T.map hd = f
        rw [Category.assoc, pushout.inl_desc]
        exact H.h₀
      · change (T.target ≫ pushout.inr _ _) ≫ pushout.desc H.h T.map hd = h
        rw [Category.assoc, pushout.inr_desc]
        exact T.target_eq
      · change (pushout.inl _ _ :: T.cells.map (· ≫ pushout.inr _ _)).map
          (· ≫ pushout.desc H.h T.map hd) = H.h :: familyHomotopyChainTrace tail
        simp only [List.map_cons, List.map_map, Function.comp_def,
          Category.assoc, pushout.inl_desc, pushout.inr_desc, T.cells_eq]

end SerrePositivity.KST.SConstruction
