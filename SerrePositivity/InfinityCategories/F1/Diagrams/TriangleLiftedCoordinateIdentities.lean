module

public import SerrePositivity.InfinityCategories.F1.Diagrams.TriangleSeparatedLongHom
public import SerrePositivity.InfinityCategories.Core.UniverseJoinSimplexShapes

/-!
概要：持ち上げた有限座標の前合成と、元のパラメーターの面・退化を照合する。
方針：ulift の標準単体同型の自然性と Yoneda の自然性を使う。
規約：パラメーターは大きい宇宙の任意の単体集合でよい。
使われ方：全次数の長 Hom の合成則と単体的自然性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

lemma triangleLiftedCoordinate_precomp {A B : SSet.{u}} {K : SSet.{max u v}} {n : ℕ}
    (f : A ⟶ B) (c : B ⟶ (Δ[n] : SSet.{u})) (s : K _⦋n⦌) :
    (SSet.uliftFunctor.{v, u}).map f ≫ triangleLiftedCoordinate c s =
      triangleLiftedCoordinate (f ≫ c) s := by
  simp only [triangleLiftedCoordinate, Functor.map_comp, Category.assoc]

lemma triangleLiftedCoordinate_eq_of_comp_eq {A B D : SSet.{u}}
    {K : SSet.{max u v}} {n : ℕ} (f : A ⟶ B) (g : A ⟶ D)
    (c : B ⟶ (Δ[n] : SSet.{u})) (d : D ⟶ (Δ[n] : SSet.{u}))
    (h : f ≫ c = g ≫ d) (s : K _⦋n⦌) :
    (SSet.uliftFunctor.{v, u}).map f ≫ triangleLiftedCoordinate c s =
      (SSet.uliftFunctor.{v, u}).map g ≫ triangleLiftedCoordinate d s := by
  rw [triangleLiftedCoordinate_precomp, triangleLiftedCoordinate_precomp, h]

lemma triangleLiftedCoordinate_naturality {A : SSet.{u}} {K : SSet.{max u v}} {m n : ℕ}
    (α : ⦋m⦌ ⟶ ⦋n⦌) (c : A ⟶ (Δ[m] : SSet.{u})) (s : K _⦋n⦌) :
    triangleLiftedCoordinate (c ≫ stdSimplex.map α) s =
      triangleLiftedCoordinate c (K.map α.op s) := by
  unfold triangleLiftedCoordinate
  rw [Functor.map_comp]
  simp only [Category.assoc]
  rw [← Category.assoc ((SSet.uliftFunctor.{v, u}).map (stdSimplex.map α))
    (HomotopyLimits.uliftStdSimplexIso.{u, v} n).hom]
  rw [uliftStdSimplexIso_hom_map]
  simp only [Category.assoc]
  rw [← SSet.yonedaEquiv_symm_naturality_left]

end SerrePositivity.InfinityCategories
