module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.EdgeEquiv

/-! # Coherent 単体の二頂点を結ぶ元の通常の射
概要：各二頂点の端点だけの Path で豊穣作用を評価し、通常の射を回収する。
方針：端点 Path の再添字の厳密な式を使う。
規約：局所 Kan 性は不要。対象と Hom の宇宙は独立。
使われ方：coherent な実三角形の写像空間での復号。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SimplicialThickening SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 二つの端点だけを含む、元の simplicial thickening の Path。 -/
def coherentEndpointPath {J : Type u} [LinearOrder J] {a b : J} (hab : a ≤ b) : Path a b where
  I := {x | x = a ∨ x = b}
  left := Or.inl rfl
  right := Or.inr rfl
  left_le x hx := by
    rcases hx with rfl | rfl
    · exact le_rfl
    · exact hab
  le_right x hx := by
    rcases hx with rfl | rfl
    · exact hab
    · exact le_rfl

/-- 端点 Path は任意の順序写像による再添字と厳密に可換。 -/
lemma coherentEndpointPath_map {J K : Type u} [LinearOrder J] [LinearOrder K]
    (θ : J →o K) {a b : J} (hab : a ≤ b) :
    (SimplicialThickening.functorMap θ (.mk a) (.mk b)).obj (coherentEndpointPath hab) =
      coherentEndpointPath (θ.monotone hab) := by
  apply SimplicialThickening.Path.ext
  ext x
  change (∃ z, (z = a ∨ z = b) ∧ θ z = x) ↔ x = θ a ∨ x = θ b
  constructor
  · rintro ⟨z, rfl | rfl, hz⟩ <;> simp [← hz]
  · rintro (rfl | rfl)
    · exact ⟨a, Or.inl rfl, rfl⟩
    · exact ⟨b, Or.inr rfl, rfl⟩

/-- Coherent 単体の二頂点間の元の通常の射。 -/
def coherentSimplexArrow {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {n : ℕ} (s : (SimplicialNerve C) _⦋n⦌) (i j : Fin (n + 1)) (hij : i ≤ j) :
    s.obj (.mk (ULift.up i)) ⟶ s.obj (.mk (ULift.up j)) :=
  (SimplicialCategory.homEquiv' _ _).symm
    ((s.map (.mk (ULift.up i)) (.mk (ULift.up j))).app (Opposite.op ⦋0⦌)
      (ComposableArrows.mk₀ (coherentEndpointPath (show (ULift.up i : ULift.{u} _) ≤
        ULift.up j from hij))))

/-- 通常の射を辺として埋めた場合、元の射そのものを回収する。 -/
lemma coherentSimplexArrow_edge {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {X Y : C} (f : X ⟶ Y) :
    coherentSimplexArrow (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).edge 0 1 (by decide) = f := by
  change (SimplicialCategory.homEquiv' X Y).symm
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (SimplicialCategory.homEquiv' X Y f) 0) = f
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero, Equiv.symm_apply_apply]

/-- 任意の単体作用による辺の復号は、元の単体の対応する二頂点での復号そのもの。 -/
lemma coherentSimplexArrow_naturality {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {m n : ℕ} (s : (SimplicialNerve C) _⦋n⦌) (θ : ⦋m⦌ ⟶ ⦋n⦌)
    (i j : Fin (m + 1)) (hij : i ≤ j) :
    coherentSimplexArrow ((SimplicialNerve C).map θ.op s) i j hij =
      coherentSimplexArrow s (θ.toOrderHom i) (θ.toOrderHom j) (θ.toOrderHom.monotone hij) := by
  unfold coherentSimplexArrow
  change (SimplicialCategory.homEquiv' _ _).symm
    ((s.map _ _).app (Opposite.op ⦋0⦌) (ComposableArrows.mk₀
      ((SimplicialThickening.functorMap θ.toOrderHom.uliftMap _ _).obj
        (coherentEndpointPath (show (ULift.up i : ULift.{u} _) ≤ ULift.up j from hij))))) = _
  rw [coherentEndpointPath_map]
  rfl

end SerrePositivity.KST.SConstruction
