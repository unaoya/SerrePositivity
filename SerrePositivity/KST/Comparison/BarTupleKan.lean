module

public import SerrePositivity.KST.Comparison.BarTupleMaps
public import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex

/-!
# Kan モノイドの有限積座標

概要：基礎単体集合が Kan であるモノイドの有限積座標も Kan である。
方針：各座標で horn を充填し、得た射を有限積の射へ束ねる。
規約：Segal 1974 Proposition 1.5 の Kan な bar の行の模型。
使われ方：bar の各行を Kan 複体として扱う。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Opposite
open scoped Simplicial

/--
概要：有限積座標の指定した一つの座標への射影。
方針：各次数で関数を指定した添字で評価する。
規約：bar の Segal 座標の射影。
使われ方：horn を座標ごとに充填する。
-/
def monoidTupleProjection (M : SimplicialObject MonCat.{u}) (r : ℕ) (i : Fin r) :
    monoidTupleSpace M r ⟶ monoidSpace M where
  app _ := ↾fun s => s i
  naturality _ _ _ := rfl

/--
概要：同じ定義域からの各座標への射を有限積座標への射へ束ねる。
方針：各次数で射の値を添字の関数にする。
規約：有限積座標を関数型で表す規約に合わせる。
使われ方：各座標の horn の充填を一つの充填へまとめる。
-/
def monoidTupleLift (M : SimplicialObject MonCat.{u}) (r : ℕ) {X : SSet.{u}}
    (f : Fin r → (X ⟶ monoidSpace M)) : X ⟶ monoidTupleSpace M r where
  app d := ↾fun x i => (f i).app d x
  naturality _ _ θ := by
    apply ConcreteCategory.hom_ext
    intro s
    funext i
    exact ConcreteCategory.congr_hom ((f i).naturality θ) s

/--
概要：Kan な基礎単体集合を持つモノイドの有限積座標は Kan 複体である。
方針：各座標の horn の充填を選んで束ね、面との合成の式を各座標で確認する。
規約：元のモノイドの群状性は不要。
使われ方：Segal の比較の Kan な行の入力。
-/
instance monoidTupleSpace_kanComplex (M : SimplicialObject MonCat.{u}) (r : ℕ)
    [SSet.KanComplex (monoidSpace M)] : SSet.KanComplex (monoidTupleSpace M r) := by
  apply SSet.KanComplex.iff.mpr
  intro n k f hf
  have hfill (i : Fin r) : ∃ g : Δ[n + 1] ⟶ monoidSpace M,
      (SSet.horn (n + 1) k).ι ≫ g = hf.desc ≫ monoidTupleProjection M r i := by
    obtain ⟨g, hg⟩ := SSet.KanComplex.hornFilling (hf.desc ≫ monoidTupleProjection M r i)
    exact ⟨g, hg.symm⟩
  let g (i : Fin r) := (hfill i).choose
  have hg : (SSet.horn (n + 1) k).ι ≫ monoidTupleLift M r g = hf.desc := by
    apply NatTrans.ext
    funext d
    apply ConcreteCategory.hom_ext
    intro s
    funext i
    exact ConcreteCategory.congr_hom (congr_app (hfill i).choose_spec d) s
  refine ⟨monoidTupleLift M r g, ?_⟩
  intro j hj
  rw [← hf.ι_desc j hj, ← hg, ← Category.assoc]
  simp only [SSet.horn.ι_ι]

end SerrePositivity.KST.Comparison
