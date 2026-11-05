module

public import SerrePositivity.InfinityCategories.Derived.PiCriterion.PositiveValueRepresentatives
public import SerrePositivity.InfinityCategories.Derived.PiCriterion.PiPathRelation

/-!
概要：全空間の正次数の代表元検出を、元の指定頂点そのものを基点として述べる。
方針：点つき対象の基点表示の等式を、恒等射の群写像と可換正方形で消去する。
規約：基点の持ち替えを結論の仮定に残さない。
使われ方：D の全基点の元ごとの条件と、全空間比較の正次数判定の接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.PiCriterion
open KST.Spectra
variable {B : SSet.{u}} [Quasicategory B] [IsFilteredInfinity B]
  (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})

local notation "T" => coherentDiagramTotalKan F
local notation "V" b => KanObject.obj (spaceInfinityObject
  (F.app (Opposite.op ⦋0⦌) (ULift.up b)))
local notation "j" b => coherentDiagramValueToTotalKan F b

/-- 元の指定基点での正次数の類に、一つの元の値の類と実際の path を取る。 -/
lemma total_positive_vertex_representative (n : ℕ) (x : T _⦋0⦌)
    (a : _root_.SerrePositivity.InfinityCategories.Kan.KanHomotopyGroup T n x) :
    ∃ b : B _⦋0⦌, ∃ y : (V b) _⦋0⦌,
      ∃ β : _root_.SerrePositivity.InfinityCategories.Kan.KanHomotopyGroup (V b) n y,
        PiPathRelated n a (_root_.SerrePositivity.InfinityCategories.Kan.KanHomotopyGroup.map (j b) rfl β) := by
  let hx := PointedSimplicialSet.basepoint_ofVertex T x
  let e := _root_.SerrePositivity.InfinityCategories.Kan.KanHomotopyGroup.equivOfIso n (Iso.refl T) (x := _)
    (y := x) hx
  obtain ⟨b, y, β, z, h₀, h₁, hⱼ, γ, ha, hb⟩ :=
    total_positiveClass_value_representative F n x (e.symm a)
  have h : PiPathRelated n (e.symm a) (_root_.SerrePositivity.InfinityCategories.Kan.KanHomotopyGroup.map (j b) hⱼ β) :=
    ⟨z, h₀, h₁, γ, ha, hb⟩
  let hy := PointedSimplicialSet.basepoint_ofVertex (V b) y
  let ht := hⱼ.symm.trans (congrArg ((j b).app (Opposite.op ⦋0⦌)) hy)
  have h' := h.rebase hx ht
  have hsource : _root_.SerrePositivity.InfinityCategories.Kan.KanHomotopyGroup.map (𝟙 T) hx (e.symm a) = a := by
    change e (e.symm a) = a
    exact e.apply_symm_apply a
  have hs := _root_.SerrePositivity.InfinityCategories.Kan.KanHomotopyGroup.map_square (𝟙 (V b)) (𝟙 T) (j b) (j b)
    (by simp) hy ht hⱼ rfl n β
  obtain ⟨w, hw₀, hw₁, δ, hδ₀, hδ₁⟩ := h'
  exact ⟨b, y, _root_.SerrePositivity.InfinityCategories.Kan.KanHomotopyGroup.map (𝟙 (V b)) hy β,
    w, hw₀, hw₁, δ, hδ₀.trans hsource, hδ₁.trans hs.symm⟩

end SerrePositivity.InfinityCategories.F2.PiCriterion
