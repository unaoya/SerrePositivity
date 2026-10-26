module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.ModuleZeroChartExtension
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.PiCriterion.PathVertexEdge
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.PiCriterion.PiPathSphereComparison
/-!
概要：全基点チャートを指定道と全空間ホモトピーに沿って比較する。
方針：指定道移送の関数性を使い、チャート値の等式と移送を同定する。
規約：基点を等号で置換せず、元の指定辺と実円柱を保持する。
使われ方：線形模型のチャートを native 値の同値と実辺の全比較へ渡す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet AlgebraicTopology Opposite
open SerrePositivity.KST.Spectra
open F2.PiCriterion
open scoped Simplicial

/-- 全基点のチャートと、同じ指定道で比較された元の不変性。 -/
structure DGBarCompactPiChart (X : SSet.{u}) [KanComplex X] (n : ℕ) (A : Type v) where
  equiv : ∀ x : X _⦋0⦌, KanHomotopyGroup X n x ≃ A
  of_transport : ∀ {x y} (e : X.Edge x y) (a : KanHomotopyGroup X n x)
    (b : KanHomotopyGroup X n y), dgBarCompactPiTransport n e a b → equiv x a = equiv y b

variable {X Y Z : SSet.{u}} [KanComplex X] [KanComplex Y] [KanComplex Z]
  {n : ℕ} {A : Type v}

lemma DGBarCompactPiChart.transport_iff (c : DGBarCompactPiChart X n A)
    {x y : X _⦋0⦌} (e : X.Edge x y) (a : KanHomotopyGroup X n x)
    (b : KanHomotopyGroup X n y) :
    dgBarCompactPiTransport n e a b ↔ c.equiv x a = c.equiv y b := by
  constructor
  · exact c.of_transport e a b
  · intro h
    have ht := (bridge_transport_iff_equiv n e a (bridgePiTransportEquiv n e a)).mpr rfl
    have hb := (c.equiv y).injective ((c.of_transport e a _ ht).symm.trans h)
    exact hb ▸ ht

lemma DGBarCompactPiChart.homotopy (c : DGBarCompactPiChart Y n A)
    {f g : X ⟶ Y} (H : SSet.Homotopy f g) (x : X _⦋0⦌)
    (a : KanHomotopyGroup X n x) :
    c.equiv (f.app _ x) (dgBarCompactPiMap n f x a) =
      c.equiv (g.app _ x) (dgBarCompactPiMap n g x a) := by
  obtain ⟨e, he⟩ := (piPathRelated_iff_exists_transport n _ _).mp
    (piPathRelated_of_homotopy H n x a)
  exact c.of_transport e _ _ he

lemma DGBarCompactPiChart.functorIso (c : DGBarCompactPiChart Y n A)
    {f g : X ⟶ Y} (H : FunctorIso f g) (x : X _⦋0⦌)
    (a : KanHomotopyGroup X n x) :
    c.equiv (f.app _ x) (dgBarCompactPiMap n f x a) =
      c.equiv (g.app _ x) (dgBarCompactPiMap n g x a) :=
  c.homotopy (FunctorIso.simplicialHomotopy H) x a

/-- 単体的加群の零チャートを、道に不変な全基点チャートへ延長する。 -/
def dgBarCompactModuleZeroPiChart {R : Type w} [CommRing R]
    (W : SimplicialObject (ModuleCat.{u} R)) [KanComplex (moduleUnderlyingSSet W)]
    (n : ℕ) (α : KanHomotopyGroup (moduleUnderlyingSSet W) n 0 ≃ A) :
    DGBarCompactPiChart (moduleUnderlyingSSet W) n A where
  equiv := dgBarCompactModuleZeroChartExtension n α
  of_transport {x y} e a b h := by
    let b' := (dgBarCompactModuleZeroChartExtension n α y).symm
      (dgBarCompactModuleZeroChartExtension n α x a)
    have ht : dgBarCompactPiTransport n e a b' :=
      dgBarCompactModuleZeroChartExtension_transport n α e a b'
        (Equiv.apply_symm_apply _ _).symm
    have hb := bridge_transport_right_unique n e h ht
    rw [hb]
    exact (Equiv.apply_symm_apply _ _).symm

end SerrePositivity.InfinityCategories
