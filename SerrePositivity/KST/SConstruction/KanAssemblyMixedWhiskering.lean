module
public import SerrePositivity.KST.SConstruction.KanAssemblyMixedChoices
public import SerrePositivity.KST.SConstruction.PointedExtensionTransportLaws

/-! # 入力の合成による混合延長空間の移送
概要：入力の射の前後への合成を全ての延長パラメーターに作用させる。
方針：元の随伴射の厳密な自然性と Kan 単位の自然性を使う。
規約：元の制限と高次単体を同時に保持する。
使われ方：自然性ホモトピーを入力の射列に沿って貼り合わせる。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 入力の後合成を混合延長空間の全単体へ作用させる。 -/
def kanAssemblyMixedPost (r : ℕ) {X Y Z : StableModel.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    kanAssemblyMixedChoices r f ⟶ kanAssemblyMixedChoices r (f ≫ g) :=
  pointedExtensionTransport _ _ _ _ (𝟙 _) (𝟙 _) ((loopBoundaryKanFunctor (r + 1)).map g)
    (by simp) (by
      rw [Category.id_comp, Category.assoc,
        ← (kanTargetAssemblyAdjointNat r).naturality g,
        CategoryTheory.Functor.map_comp, Category.assoc])

/-- 入力の前合成を混合延長空間の全単体へ作用させる。 -/
def kanAssemblyMixedPre (r : ℕ) {X Y Z : StableModel.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    kanAssemblyMixedChoices r g ⟶ kanAssemblyMixedChoices r (f ≫ g) :=
  pointedExtensionTransport _ _ _ _ ((oneDirectionReducedRealizationFunctor r).map f)
    ((oneDirectionKanRealizationFunctor r).map f) (𝟙 _)
    (Spectra.PointedKanReplacement.unit.naturality
      ((oneDirectionReducedRealizationFunctor r).map f)) (by
      rw [Category.comp_id, CategoryTheory.Functor.map_comp, Category.assoc])

/-- 混合延長の自然性を表す辺を、元の随伴射への制限を固定して選べる。 -/
lemma kanAssemblyMixedChoices_nonempty_edge (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (v : (kanAssemblyAdjointChoices r X) _⦋0⦌)
    (w : (kanAssemblyAdjointChoices r Y) _⦋0⦌) :
    Nonempty ((kanAssemblyMixedChoices r f).Edge
      ((kanAssemblyMixedFromSource r f).app (Opposite.op ⦋0⦌) v)
      ((kanAssemblyMixedFromTarget r f).app (Opposite.op ⦋0⦌) w)) := by
  let a := (kanAssemblyMixedFromSource r f).app (Opposite.op ⦋0⦌) v
  let b := (kanAssemblyMixedFromTarget r f).app (Opposite.op ⦋0⦌) w
  obtain ⟨e⟩ := ((kanAssemblyMixedChoices_isContractibleKan r f).isTerminalVertex b).nonempty_edge a
  exact ⟨SSet.Edge.ofTruncated e⟩

/-- 混合延長空間内で指定した全ての面を保つ高次の比較が存在する。 -/
lemma kanAssemblyMixedChoices_fill_boundary (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (n : ℕ) (a : (boundary n : SSet.{u}) ⟶ kanAssemblyMixedChoices r f) :
    ∃ b : (Δ[n] : SSet.{u}) ⟶ kanAssemblyMixedChoices r f, (boundary n).ι ≫ b = a :=
  kanAssemblyMixedChoices_relative_lifting r f (boundary n).ι a

end SerrePositivity.KST.SConstruction
