module

public import SerrePositivity.KST.Comparison.BarSegal
public import SerrePositivity.KST.Comparison.MonoidComponents
public import SerrePositivity.HomotopicalAlgebra.Simplicial.AnodyneLocalizedTensor
public import Mathlib.Data.Fin.Tuple.Basic

/-!
# bar の有限積座標の射と局所化

概要：単体的モノイドの基礎射が局所化可逆なら、有限積座標上の射も局所化可逆である。
方針：Fin の先頭と残りの分解により積の個数で帰納し、直積が局所化可逆性を保つことを使う。
規約：Segal 1974 Proposition 1.5 の Kan なモノイドの模型への移行。
使われ方：元の bar と Kan 置換後の bar の各行の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Opposite MonoidalCategory
open SerrePositivity.SimplicialModel

/--
概要：単体的モノイドの射を各有限積座標に適用する写像。
方針：各単体次数で各座標へ準同型を適用する。
規約：bar の Segal 座標に対応する写像。
使われ方：bar の行の写像の局所化可逆性。
-/
def monoidTupleMap {M N : SimplicialObject MonCat.{u}} (f : M ⟶ N) (r : ℕ) :
    monoidTupleSpace M r ⟶ monoidTupleSpace N r where
  app d := ↾fun s i => (f.app d).hom (s i)
  naturality d e θ := by
    apply ConcreteCategory.hom_ext
    intro s
    funext i
    exact ConcreteCategory.congr_hom (f.naturality θ) (s i)

/--
概要：有限積の先頭の座標と残りの座標を分離する同型。
方針：Fin.consEquiv の逆同値を各単体次数で使う。
規約：有限積を二項直積の反復として扱う。
使われ方：局所化可逆性の有限帰納。
-/
def monoidTupleSuccIso (M : SimplicialObject MonCat.{u}) (r : ℕ) :
    monoidTupleSpace M (r + 1) ≅ monoidSpace M ⊗ monoidTupleSpace M r :=
  NatIso.ofComponents (fun d => (Fin.consEquiv (fun _ : Fin (r + 1) => M.obj d)).symm.toIso)
    (by intros; rfl)

/--
概要：有限積の座標の分離は単体的モノイドの射と可換である。
方針：先頭の値と残りの各値の両方で同じ準同型を適用する。
規約：Segal の有限積座標の自然性。
使われ方：帰納段階の比較を二項直積の比較へ移す。
-/
@[reassoc] theorem monoidTupleSuccIso_naturality {M N : SimplicialObject MonCat.{u}}
    (f : M ⟶ N) (r : ℕ) :
    monoidTupleMap f (r + 1) ≫ (monoidTupleSuccIso N r).hom =
      (monoidTupleSuccIso M r).hom ≫
        (Functor.whiskerRight f (forget MonCat) ⊗ₘ monoidTupleMap f r) := rfl

/--
概要：零個の座標の間の写像は同型である。
方針：空の定義域を持つ関数の型の間の写像が全単射であることを各次数で使う。
規約：有限積の帰納の基底。
使われ方：bar の零行の比較。
-/
instance monoidTupleMap_zero_isIso {M N : SimplicialObject MonCat.{u}} (f : M ⟶ N) :
    IsIso (monoidTupleMap f 0) := by
  have (d : SimplexCategoryᵒᵖ) : IsIso ((monoidTupleMap f 0).app d) := by
    apply (isIso_iff_bijective _).mpr
    constructor
    · intro a b _
      exact funext (fun i => Fin.elim0 i)
    · intro a
      exact ⟨fun i => Fin.elim0 i, funext (fun i => Fin.elim0 i)⟩
  exact NatIso.isIso_of_isIso_app _

/--
概要：基礎射が局所化可逆なら、任意の有限積座標の射も局所化可逆である。
方針：二項直積による分解で帰納し、左右の直積関手が局所化可逆性を保つことを使う。
規約：Segal 1974 Proposition 1.5 の bar の各行の模型の不変性。
使われ方：対角化で bar の比較を局所化可逆とする。
-/
theorem monoidTupleMap_localized_isIso {M N : SimplicialObject MonCat.{u}} (f : M ⟶ N)
    (hf : IsIso (AnodyneHomotopy.anodyneQ.map (Functor.whiskerRight f (forget MonCat))))
    (r : ℕ) : IsIso (AnodyneHomotopy.anodyneQ.map (monoidTupleMap f r)) := by
  induction r with
  | zero => infer_instance
  | succ r ih =>
      let Q := AnodyneHomotopy.anodyneQ.{u}
      let g := Functor.whiskerRight f (forget MonCat)
      have ht : IsIso (Q.map (g ⊗ₘ monoidTupleMap f r)) := by
        rw [tensorHom_def, Q.map_comp]
        have := AnodyneHomotopy.whiskerRight_anodyneQ_isIso g hf (monoidTupleSpace M r)
        have := AnodyneHomotopy.whiskerLeft_anodyneQ_isIso (monoidTupleMap f r) ih (monoidSpace N)
        infer_instance
      have h := congrArg Q.map (monoidTupleSuccIso_naturality f r)
      rw [Q.map_comp, Q.map_comp] at h
      have hc : IsIso (Q.map (monoidTupleMap f (r + 1)) ≫ Q.map (monoidTupleSuccIso N r).hom) :=
        h.symm ▸ inferInstanceAs (IsIso (Q.map (monoidTupleSuccIso M r).hom ≫
          Q.map (g ⊗ₘ monoidTupleMap f r)))
      exact (isIso_comp_right_iff _ _).mp hc

end SerrePositivity.KST.Comparison
