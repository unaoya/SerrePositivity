module

public import SerrePositivity.KST.Spectra.GroupNerveFaces
public import SerrePositivity.KST.Spectra.SimplicialValueFaces
public import SerrePositivity.KST.Spectra.RepresentationCochainComparison

/-!
概要：BG の全単体の係数値 cochain と自明作用の非斉次群 cochain の複体同型。
方針：群座標から復元した単体の面を計算し、余積の合成順序を含めて微分を照合する。
規約：係数は可換環上の加群。群の有限性は比較には不要。
使われ方：Goerss–Jardine VIII §2。群 cohomology の計算を BG の正規化 cochain へ移す。
-/

@[expose] public section

universe u

open CategoryTheory SSet
open scoped Simplicial

namespace SerrePositivity.KST.Spectra.GroupNerve

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (G : Type u) [Group G]

lemma fromCoordinates_face_zero {n : ℕ} (a : Fin (n + 1) → G) :
    (nerve (AsSmall.{u} (SingleObj G))).δ (0 : Fin (n + 2)) (fromCoordinates G a) =
      fromCoordinates G (Fin.tail a) := by
  apply (coordinatesEquiv G n).injective
  change coordinates G _ = coordinates G _
  rw [coordinates_face_zero, coordinates_fromCoordinates, coordinates_fromCoordinates]

lemma fromCoordinates_face_succ {n : ℕ} (a : Fin (n + 1) → G) (j : Fin (n + 1)) :
    (nerve (AsSmall.{u} (SingleObj G))).δ j.succ (fromCoordinates G a) =
      fromCoordinates G (Fin.contractNth j (· * ·) a) := by
  apply (coordinatesEquiv G n).injective
  change coordinates G _ = coordinates G _
  rw [coordinates_face_succ, coordinates_fromCoordinates, coordinates_fromCoordinates]

/-- 概要：BG の全単体上の cochain は非斉次群座標上の関数群と加法同型。
方針：群座標と単体の同値への前合成を取る。
規約：基点と作用はなく通常の加法的係数だけを使う。
使われ方：Goerss–Jardine VIII §2。群 cochain の次数ごとの比較。 -/
def cochainEquiv (M : AddCommGrpCat.{u}) (n : ℕ) :
    ((nerve (AsSmall.{u} (SingleObj G))) _⦋n⦌ → M) ≃+ ((Fin n → G) → M) where
  toFun a x := a (fromCoordinates G x)
  invFun a s := a (coordinates G s)
  left_inv a := by
    funext s
    exact congrArg a (fromCoordinates_coordinates G s)
  right_inv a := by
    funext x
    exact congrArg a (coordinates_fromCoordinates G x)
  map_add' _ _ := rfl

/-- 概要：BG の通常の cochain は自明係数の非斉次群 cochain の複体と同型。
方針：各次数の群座標の加法同型を取り、最初の面と contraction の面の交代式を照合する。
規約：係数の線形複体を加法群へ忘却して比較する。
使われ方：Goerss–Jardine VIII §2。有理群 cohomology の消滅を BG へ移す。 -/
def linearComplexIso (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M] :
    SimplicialValueCochains.complex (nerve (AsSmall.{u} (SingleObj G))) (AddCommGrpCat.of M) ≅
      ((forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj (LinearGroupCochains.complex (Rep.trivial R G M)) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ AddEquiv.toAddCommGrpIso (cochainEquiv G (AddCommGrpCat.of M) n))
    (fun i j hij ↦ by
      obtain rfl : i + 1 = j := hij
      simp only [LinearGroupCochains.complex, AlgebraicTopology.AlternatingCofaceMapComplex.obj,
        Functor.mapHomologicalComplex_obj_d, CochainComplex.of_d]
      apply ConcreteCategory.hom_ext
      intro a
      change (ComposableArrows (AsSmall.{u} (SingleObj G)) i → M) at a
      funext g
      change (Fin (i + 1) → G) at g
      change (AlgebraicTopology.AlternatingCofaceMapComplex.objD
        (LinearGroupCochains.obj (Action.trivial G (ModuleCat.of R M))) i).hom
        (fun v : Fin i → G ↦ a (fromCoordinates G v)) g =
        (SimplicialValueCochains.complex (nerve (AsSmall.{u} (SingleObj G)))
          (AddCommGrpCat.of M)).d i (i + 1) a (fromCoordinates G g)
      rw [LinearGroupCochains.alternating_d_apply, SimplicialValueCochains.differential_apply_succ]
      change a (fromCoordinates G (Fin.tail g)) +
          ∑ j : Fin (i + 1), (-1 : ℤ) ^ (j.val + 1) •
            a (fromCoordinates G (Fin.contractNth j (· * ·) g)) = _
      apply congrArg₂ (fun x y : M ↦ x + y)
      · exact congrArg a (fromCoordinates_face_zero G g).symm
      · apply Finset.sum_congr rfl
        intro j _
        exact congrArg (fun t ↦ (-1 : ℤ) ^ (j.val + 1) • a t)
          (fromCoordinates_face_succ G g j).symm)

end

end SerrePositivity.KST.Spectra.GroupNerve
