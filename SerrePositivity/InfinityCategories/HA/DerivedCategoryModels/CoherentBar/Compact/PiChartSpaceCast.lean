module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.PiChartEquivalence
/-!
概要：全基点チャートの空間表示を厳密な等式で合わせる。
方針：空間・実射・チャートを同じ等式で同時に輸送する。
規約：全空間比較のデータを選び直さない。
使われ方：coherent 頂点と元の dg 頂点の表示差を吸収する。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
open CategoryTheory SSet
open _root_.SerrePositivity.KST.Spectra
open scoped _root_.Simplicial

/-- 空間の等式による実射の輸送。 -/
def dgBarCompactSpaceMapCast {X X' Y Y' : SSet.{u}}
    (hx : X = X') (hy : Y = Y') (f : X ⟶ Y) : X' ⟶ Y' := hx ▸ hy ▸ f

lemma dgBarCompactSpaceMapCast_heq {X X' Y Y' : SSet.{u}}
    (hx : X = X') (hy : Y = Y') (f : X ⟶ Y) :
    HEq (dgBarCompactSpaceMapCast hx hy f) f := by subst X'; subst Y'; rfl

/-- 元の空間の厳密な表示にチャートを合わせる。 -/
def DGBarCompactPiChart.cast {X Y : SSet.{u}} [KanComplex X] [KanComplex Y]
    {n : ℕ} {A : Type v} (h : X = Y) (c : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.DGBarCompactPiChart X n A) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.DGBarCompactPiChart Y n A := h ▸ c

lemma dgBarCompactPiChart_cast_naturality {X X' Y Y' : SSet.{u}}
    [KanComplex X] [KanComplex X'] [KanComplex Y] [KanComplex Y']
    {n : ℕ} {A : Type v} {B : Type w} (hx : X = X') (hy : Y = Y')
    (c : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.DGBarCompactPiChart X n A) (c' : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.DGBarCompactPiChart Y n B)
    (f : X ⟶ Y) (φ : A → B)
    (hf : ∀ z a, c'.equiv (f.app _ z) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactPiMap n f z a) = φ (c.equiv z a))
    (z : X' _⦋0⦌) (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup X' n z) :
    (c'.cast hy).equiv ((dgBarCompactSpaceMapCast hx hy f).app _ z)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactPiMap n (dgBarCompactSpaceMapCast hx hy f) z a) =
      φ ((c.cast hx).equiv z a) := by
  subst X'; subst Y'
  exact hf z a

def dgBarCompactPiZeroChart_cast {X Y : SSet.{u}} {A : Type v}
    (h : X = Y) (c : SSet.π₀ X ≃ A) : SSet.π₀ Y ≃ A := h ▸ c

lemma dgBarCompactPiZeroChart_cast_naturality {X X' Y Y' : SSet.{u}}
    {A : Type v} {B : Type w} (hx : X = X') (hy : Y = Y')
    (c : SSet.π₀ X ≃ A) (c' : SSet.π₀ Y ≃ B) (f : X ⟶ Y) (φ : A → B)
    (hf : ∀ a, c' (SSet.mapπ₀ f a) = φ (c a)) (a : SSet.π₀ X') :
    dgBarCompactPiZeroChart_cast hy c' (SSet.mapπ₀ (dgBarCompactSpaceMapCast hx hy f) a) =
      φ (dgBarCompactPiZeroChart_cast hx c a) := by
  subst X'; subst Y'
  exact hf a

/-- 全基点の自然性を、元の二つのチャートと実射に付随する命題として束ねる。 -/
structure DGBarCompactPiChartNaturality {X Y : SSet.{u}} [KanComplex X] [KanComplex Y]
    {n : ℕ} {A : Type v} {B : Type w} (c : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.DGBarCompactPiChart X n A)
    (c' : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.DGBarCompactPiChart Y n B) (f : X ⟶ Y) (φ : A → B) : Prop where
  app : ∀ x a, c'.equiv (f.app _ x) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactPiMap n f x a) = φ (c.equiv x a)

lemma DGBarCompactPiChartNaturality.cast {X X' Y Y' : SSet.{u}}
    [KanComplex X] [KanComplex X'] [KanComplex Y] [KanComplex Y']
    {n : ℕ} {A : Type v} {B : Type w} {c : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.DGBarCompactPiChart X n A}
    {c' : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.DGBarCompactPiChart Y n B} {f : X ⟶ Y} {φ : A → B}
    (h : DGBarCompactPiChartNaturality c c' f φ) (hx : X = X') (hy : Y = Y') :
    DGBarCompactPiChartNaturality (c.cast hx) (c'.cast hy)
      (dgBarCompactSpaceMapCast hx hy f) φ :=
  ⟨dgBarCompactPiChart_cast_naturality hx hy c c' f φ h.app⟩

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
